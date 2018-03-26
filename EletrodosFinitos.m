(* ::Package:: *)

(* ::Title:: *)
(*Eletrodos Finitos*)


(* ::Program:: *)
(*Autor: Pedro Henrique Nascimento Vieira*)
(*Criado em: 26 de Outubro de 2017*)
(*\[CapitalUAcute]ltima altera\[CCedilla]\[ATilde]o: 23 de Marco de 2018*)


(* ::Text:: *)
(*Conjunto de fun\[CCedilla]\[OTilde]es para c\[AAcute]lculos de eletrodos finitos.*)
(*Cada eletrodo \[EAcute] definido como uma lista da forma:*)
(*	eletrodo = { {ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total }*)
(*	*)
(*Pontos em coordenadas retangulares \[DoubleStruckCapitalR]^3: {x,y,z}.*)


(* ::Section:: *)
(*Integrando*)


(* ::DisplayFormula:: *)
(*Exp[-\[Gamma] \[Eta]] Log[Subscript[N, f]]*)


(*Tive que fazer esse tro\[CCedilla]o feio com os argumentos, pois NIntegrate tenta resolver simbolicamente primeiro, o que causa erros por causa da fun\[CCedilla]\[ATilde]o compilada.
Para contornar, \[EAcute] necess\[AAcute]rio uma fun\[CCedilla]\[ATilde]o intermedi\[AAcute]ria que garanta que os argumentos passados sejam todos num\[EAcute]ricos. Para isto, tive que separar os vetores.*)
IntegrandoCompilado = Compile[
	{
		{exi,_Real},{eyi,_Real},{ezi,_Real},
		{exf,_Real},{eyf,_Real},{ezf,_Real},
		{rxi,_Real},{ryi,_Real},{rzi,_Real},
		{rxf,_Real},{ryf,_Real},{rzf,_Real},
		{\[Gamma],_Complex},{t,_Real},{Ls,_Real},{simplificado,True|False}
	},
	Block[{x,y,z,\[Eta],R1,R2,Nf,val=0. I},
		(*curvas param\[EAcute]tricas {t,0,1}*)
		x = rxi + (rxf - rxi) t;
		y = ryi + (ryf - ryi) t;
		z = rzi + (rzf - rzi) t;
		R1 = Norm[{x,y,z} - {exi,eyi,ezi}];
		R2 = Norm[{x,y,z} - {exf,eyf,ezf}];
		Nf = (R1 + R2 + Ls)/(R1 + R2 - Ls);
		If[simplificado,
		(*True*)
			val = Log[Nf],
		(*False*)
			\[Eta] = Norm[{x,y,z} - ({exi,eyi,ezi} + {exf,eyf,ezf})/2];
			val = Exp[-\[Gamma] \[Eta]] Log[Nf]
		];
	Return[val]
	]
]

IntegrandoIntermediario[
	exi_?NumericQ,eyi_?NumericQ,ezi_?NumericQ,
	exf_?NumericQ,eyf_?NumericQ,ezf_?NumericQ,
	rxi_?NumericQ,ryi_?NumericQ,rzi_?NumericQ,
	rxf_?NumericQ,ryf_?NumericQ,rzf_?NumericQ,
	\[Gamma]_?NumericQ,t_?NumericQ,Ls_?NumericQ,simplificado_?BooleanQ
	] := 
IntegrandoCompilado[
	exi,eyi,ezi,
	exf,eyf,ezf,
	rxi,ryi,rzi,
	rxf,ryf,rzf,
	\[Gamma],t,Ls,simplificado
]

Integrando[emissor_,receptor_,\[Gamma]_,t_,Ls_:0,simplificado_:False] := 
Block[{ll},
	If[Ls === 0,
		ll = Norm[emissor[[1]] - emissor[[2]]](*True*),
		ll = Ls (*False*)
	];
	IntegrandoIntermediario[
		emissor[[1,1]],emissor[[1,2]],emissor[[1,3]],
		emissor[[2,1]],emissor[[2,2]],emissor[[2,3]],
		receptor[[1,1]],receptor[[1,2]],receptor[[1,3]],
		receptor[[2,1]],receptor[[2,2]],receptor[[2,3]],
		\[Gamma],t,ll,simplificado
	]
]
Integrando::usage = "Fun\[CCedilla]\[ATilde]o auxiliar para resolver a integral \!\(\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(Lr\)]Exp[-\[Gamma] \[Eta]] Log[Nf] dl;
Se simplificado (padr\[ATilde]o = False), Exp[-\[Gamma] \[Eta]] n\[ATilde]o \[EAcute] avaliado e deve ser incluso fora da integral.
Argumentos:
	emissor: eletrodo na forma de lista '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	receptor: idem;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	t: valor param\[EAcute]trico (0 \[LessSlantEqual] t \[LessSlantEqual] 1) que define o ponto de c\[AAcute]lculo no eletrodo receptor (sendo: t=0 -> ponto inicial, t=1 -> ponto final);
	Ls: opcional, comprimento do eletrodo emissor;
	simplificado: opicional, Booleano se considera Exp[-\[Gamma] \[Eta]] constante ou n\[ATilde]o durante a integra\[CCedilla]\[ATilde]o.
		padr\[ATilde]o = False";


(* ::Section:: *)
(*Imped\[AHat]ncia Transversal*)


ImpedanciaTransversalPropria[eletrodo_,c_]:=
Block[{Ls,k1,k2},
	Ls = Norm[eletrodo[[1]] - eletrodo[[2]]];
	k1 = eletrodo[[3]]/Ls;
	k2 = Sqrt[1. + k1^2.];
	Return[1./(2. \[Pi] Ls c) (Log [(k2 + 1.)/k1] - k2 + k1)]
]
ImpedanciaTransversalPropria::usage=
"Calcula a imped\[AHat]ncia transversal pr\[OAcute]pria de um eletrodo considerando-o imerso em meio infinito, isotr\[OAcute]pico e homog\[EHat]neo.
Argumentos:
	eletrodo: lista no formato {{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total};
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]).";


ImpedanciaTransversalMutua[emissor_,receptor_,\[Gamma]_,c_,integral_:{}]:=
Block[{Ls,Lr,int},
	Ls = Norm[emissor[[1]] - emissor[[2]]];
	Lr = Norm[receptor[[1]] - receptor[[2]]];
	If[integral === {},
		int = NIntegrate[Integrando[emissor,receptor,\[Gamma],t,Ls],{t,0.,1.},Compiled->False];,
		int = integral; (*else*)
	];
	Return[1./(4. \[Pi] Ls Lr c) int]
]
ImpedanciaTransversalMutua::usage=
"Calcula a imped\[AHat]ncia transversal m\[UAcute]tua entre dois eletrodos considerando-os imersos em meio infinito, isotr\[OAcute]pico e homog\[EHat]neo.
Argumentos:
	emissor: eletrodo no formato de lista {{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total};
	receptor: idem;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	integral: opcional, o valor de \!\(\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(Lr\)]Exp[-\[Gamma] \[Eta]] Log[Nf] dl.";


(* ::Section:: *)
(*Imped\[AHat]ncia Longitudinal*)


ImpedanciaLongitudinalPropria[eletrodo_,\[Mu]_,\[Omega]_]:=
Block[{Ls,k1,k2},
	Ls = Norm[eletrodo[[1]] - eletrodo[[2]]];
	k1 = eletrodo[[3]]/Ls;
	k2 = Sqrt[1. + k1^2.];
	Return[(I \[Omega] \[Mu] Ls)/(2. \[Pi]) (Log [(k2 + 1.)/k1] - k2 + k1) + eletrodo[[4]]]
]
ImpedanciaLongitudinalPropria::usage=
"Calcula a imped\[AHat]ncia longitudinal pr\[OAcute]pria de um eletrodo considerando-o imerso em meio infinito, isotr\[OAcute]pico e homog\[EHat]neo.
Argumentos:
	eletrodo: lista no formato {{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total};
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular.";


ImpedanciaLongitudinalMutua[emissor_,receptor_,\[Gamma]_,\[Mu]_,\[Omega]_,integral_:{}]:=
Block[{ds,dr,Ls,Lr,cos\[Phi],int},
	ds = emissor[[1]] - emissor[[2]];
	dr = receptor[[1]] - receptor[[2]];
	Ls = Norm[ds];
	Lr = Norm[dr];
	cos\[Phi] = (ds[[1]] dr[[1]] + ds[[2]] dr[[2]] + ds[[3]] dr[[3]])/(Ls Lr);
	If[cos\[Phi] === 0, Return[0]];
	If[integral === {},
		int = NIntegrate[Integrando[emissor,receptor,\[Gamma],t,Ls],{t,0.,1.},Compiled->False];,
		int = integral; (*else*)
	];
	Return[(-I \[Omega] \[Mu] cos\[Phi])/(4. \[Pi]) int]
]
ImpedanciaLongitudinalMutua::usage=
"Calcula a imped\[AHat]ncia longitudinal m\[UAcute]tua entre dois eletrodos considerando-os imersos em meio infinito, isotr\[OAcute]pico e homog\[EHat]neo.
Argumentos:
	emissor: eletrodo no formato de lista {{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total};
	receptor: idem;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	\[Mu]: opicional, permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	integral: opcional, o valor de \!\(\*SubsuperscriptBox[\(\[Integral]\), \(0\), \(Lr\)]Exp[-\[Gamma] \[Eta]] Log[Nf] dl.";


(* ::Section:: *)
(*Imped\[AHat]ncia Total*)


(* ::Subsection::Closed:: *)
(*Versao original*)


ImpedanciaEletrodos[eletrodos_,\[Gamma]_,c_,\[Mu]_,\[Omega]_,simplificado_:False]:=
Block[{ZT,ZL,numEletrodos,Ls,integral,\[Eta]},
	numEletrodos = Dimensions[eletrodos][[1]];
	ZT = Table[ImpedanciaTransversalPropria[e,c],{e,eletrodos}];
	ZT = DiagonalMatrix[ZT];
	ZL = Table[ImpedanciaLongitudinalPropria[e,\[Mu],\[Omega]],{e,eletrodos}];
	ZL = DiagonalMatrix[ZL];
	If[numEletrodos === 1, Return[{ZT,ZL}]];
	Do[
		Ls = Norm[eletrodos[[i,1]] - eletrodos[[i,2]]];
		integral = NIntegrate[Integrando[eletrodos[[i]],eletrodos[[k]],\[Gamma],t,Ls,simplificado],{t,0.,1.},Compiled->False];
		If[simplificado,
			\[Eta] = Norm[(eletrodos[[i,1]] + eletrodos[[i,2]])/2 - (eletrodos[[k,1]] + eletrodos[[k,2]])/2];
			integral = integral Exp[-\[Gamma] \[Eta]];
		];
		ZT[[i,k]] = ImpedanciaTransversalMutua[eletrodos[[i]],eletrodos[[k]],\[Gamma],c,integral];
		ZL[[i,k]] = ImpedanciaLongitudinalMutua[eletrodos[[i]],eletrodos[[k]],\[Gamma],\[Mu],\[Omega],integral];
		ZT[[k,i]] = ZT[[i,k]];
		ZL[[k,i]] = ZL[[i,k]];
		,{i,1,numEletrodos},{k,i+1,numEletrodos}
	];
	Return[{ZT,ZL}]
]
ImpedanciaEletrodos::usage=
"Calcula as matrizes de imped\[AHat]ncia longitudinal e transvesal do conjunto de eletrodos considerando-os imersos em meio homog\[EHat]neo.
Argumentos:
	eletrodos: lista de listas dos eletrodos '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	simplificado: opicional, Booleano se considera Exp[-\[Gamma] \[Eta]] constante ou n\[ATilde]o durante a integra\[CCedilla]\[ATilde]o.
		padr\[ATilde]o = False
-------
Retorna:
	ZT: matriz de imped\[AHat]ncia transveral;
	ZL: matriz de imped\[AHat]ncia longitudinal.";


IncluirImagensImpedancia[zt_,zl_,eletrodos_,imagens_,\[Gamma]_,c_,\[Mu]_,\[Omega]_,coefReflexao_:1.0,simplificado_:False]:=
Block[{ZT=zt,ZL=zl,numEletrodos,Ls,integral,\[Eta]},
	numEletrodos = Dimensions[eletrodos][[1]];
	(*adicionar mutua com imagem \[AGrave] Z pr\[OAcute]pria*)
	(*Do[
		If[imagens[[i]] === Null, Continue[]];
		Ls = Norm[eletrodos[[i,1]] - eletrodos[[i,2]]];
		integral = NIntegrate[Integrando[imagens[[i]],eletrodos[[i]],\[Gamma],t,Ls,simplificado],{t,0.,1.},Compiled->False];
		If[simplificado,
			\[Eta] = Norm[(imagens[[i,1]] + imagens[[i,2]])/2 - (eletrodos[[i,1]] + eletrodos[[i,2]])/2];
			integral = integral Exp[-\[Gamma] \[Eta]];
		];
		ZT[[i,i]] += coefReflexao ImpedanciaTransversalMutua[imagens[[i]],eletrodos[[i]],\[Gamma],c,integral];
		ZL[[i,i]] += (1 - coefReflexao) ImpedanciaLongitudinalMutua[imagens[[i]],eletrodos[[i]],\[Gamma],\[Mu],\[Omega],integral];
		,{i,numEletrodos}
	];
	If[numEletrodos === 1, Return[{ZT,ZL}]];*)
	(*adicionar efeito da imagem \[AGrave] Z m\[UAcute]tua*)
	Do[
		If[imagens[[i]] === Null || imagens[[k]] === Null, Continue[]];
		Ls = Norm[eletrodos[[i,1]] - eletrodos[[i,2]]];
		integral = NIntegrate[Integrando[imagens[[i]],eletrodos[[k]],\[Gamma],t,Ls,simplificado],{t,0.,1.},Compiled->False];
		If[simplificado,
			\[Eta] = Norm[(imagens[[i,1]] + imagens[[i,2]])/2 - (eletrodos[[k,1]] + eletrodos[[k,2]])/2];
			integral = integral Exp[-\[Gamma] \[Eta]];
		];
		ZT[[i,k]] += coefReflexao ImpedanciaTransversalMutua[imagens[[i]],eletrodos[[k]],\[Gamma],c,integral];
		ZL[[i,k]] += (1 - coefReflexao) ImpedanciaLongitudinalMutua[imagens[[i]],eletrodos[[k]],\[Gamma],\[Mu],\[Omega],integral];
		ZT[[k,i]] = ZT[[i,k]];
		ZL[[k,i]] = ZL[[i,k]];
		,{i,1,numEletrodos},{k,i,numEletrodos}
	];
	Return[{ZT,ZL}]
]
IncluirImagensImpedancia::usage=
"Adiciona \[AGrave]s matrizes de imped\[AHat]ncia longitudinal e transvesal o efeito das imagens. Se houver m\[UAcute]ltiplas imagens para um mesmo eletrodo, use esta fun\[CCedilla]\[ATilde]o recursivamente.
Argumentos:
	zt: matriz de imped\[AHat]ncia transveral;
	zl: matriz de imped\[AHat]ncia longitudinal;
	eletrodos: lista de listas dos eletrodos '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	imagens: lista de listas, onde imagens[[i]] \[EAcute] a imagem de eletrodos[[i]] (se n\[ATilde]o houver imagem para ele, ent\[ATilde]o ela deve ser Null. Neste caso, inclusive, o eletrodo n\[ATilde]o receber\[AAcute] influ\[EHat]ncia de qualquer imagem);
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	coefReflexao: opicional, o coeficiente de reflex\[ATilde]o para as imagens;
		padr\[ATilde]o = 1.0
	simplificado: opicional, Booleano se considera Exp[-\[Gamma] \[Eta]] constante ou n\[ATilde]o durante a integra\[CCedilla]\[ATilde]o.
		padr\[ATilde]o = False
-------
Retorna:
	ZT: matriz de imped\[AHat]ncia transveral com efeito das imagens incluso;
	ZL: matriz de imped\[AHat]ncia longitudinal com efeito das imagens incluso.";


(* ::Subsection:: *)
(*Versao simplificada*)


(* ::Text:: *)
(**Nota sobre os argumentos**)
(*integral: e uma matriz cujo elemento [[i,k]] e o valor da integral do eletrodo emissor i em relacao ao receptor k.*)
(*etam: e a matriz de distancias dos pontos medios dos eletrodos. Os elementos da diagonal sao o comprimento dos eletrodos.*)
(*etai: matriz de distancias dos pontos medios dos eletrodos ao ponto medio das imagens.*)


ImpedanciaEletrodosSimples[eletrodos_,\[Gamma]_,c_,\[Mu]_,\[Omega]_,integral_,etam_]:=
Block[{ZT,ZL,numEletrodos,Ls,intg},
	numEletrodos = Dimensions[eletrodos][[1]];
	ZT = Table[ImpedanciaTransversalPropria[e,c],{e,eletrodos}];
	ZT = DiagonalMatrix[ZT];
	ZL = Table[ImpedanciaLongitudinalPropria[e,\[Mu],\[Omega]],{e,eletrodos}];
	ZL = DiagonalMatrix[ZL];
	If[numEletrodos === 1, Return[{ZT,ZL}]];
	Do[
		Ls = etam[[i,i]];
		intg = Exp[-\[Gamma] etam[[i,k]]] integral[[i,k]];
		ZT[[i,k]] = ImpedanciaTransversalMutua[eletrodos[[i]],eletrodos[[k]],\[Gamma],c,intg];
		ZL[[i,k]] = ImpedanciaLongitudinalMutua[eletrodos[[i]],eletrodos[[k]],\[Gamma],\[Mu],\[Omega],intg];
		ZT[[k,i]] = ZT[[i,k]];
		ZL[[k,i]] = ZL[[i,k]];
		,{i,1,numEletrodos},{k,i+1,numEletrodos}
	];
	Return[{ZT,ZL}]
]
ImpedanciaEletrodosSimples::usage=
"Calcula as matrizes de imped\[AHat]ncia longitudinal e transvesal do conjunto de eletrodos considerando-os imersos em meio homog\[EHat]neo.
Versao otimizada para caso simplificado.
Argumentos:
	eletrodos: lista de listas dos eletrodos '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	integral: matriz do valor das integrais;
	etam: matriz de distancias medias entre eletrodos;
-------
Retorna:
	ZT: matriz de imped\[AHat]ncia transveral;
	ZL: matriz de imped\[AHat]ncia longitudinal.";


IncluirImagensImpedanciaSimples[zt_,zl_,eletrodos_,imagens_,\[Gamma]_,c_,\[Mu]_,\[Omega]_,integral_,etam_,etai_,coefReflexao_:1.0]:=
Block[{ZT=zt,ZL=zl,numEletrodos,Ls,intg},
	numEletrodos = Dimensions[eletrodos][[1]];
	(*adicionar mutua com imagem \[AGrave] Z pr\[OAcute]pria*)
	(*Do[
		If[imagens[[i]] === Null, Continue[]];
		Ls = Norm[eletrodos[[i,1]] - eletrodos[[i,2]]];
		integral = NIntegrate[Integrando[imagens[[i]],eletrodos[[i]],\[Gamma],t,Ls,simplificado],{t,0.,1.},Compiled->False];
		If[simplificado,
			\[Eta] = Norm[(imagens[[i,1]] + imagens[[i,2]])/2 - (eletrodos[[i,1]] + eletrodos[[i,2]])/2];
			integral = integral Exp[-\[Gamma] \[Eta]];
		];
		ZT[[i,i]] += coefReflexao ImpedanciaTransversalMutua[imagens[[i]],eletrodos[[i]],\[Gamma],c,integral];
		ZL[[i,i]] += (1 - coefReflexao) ImpedanciaLongitudinalMutua[imagens[[i]],eletrodos[[i]],\[Gamma],\[Mu],\[Omega],integral];
		,{i,numEletrodos}
	];
	If[numEletrodos === 1, Return[{ZT,ZL}]];*)
	(*adicionar efeito da imagem \[AGrave] Z m\[UAcute]tua*)
	Do[
		If[imagens[[i]] === Null || imagens[[k]] === Null, Continue[]];
		Ls = etam[[i,i]];
		intg = Exp[-\[Gamma] etai[[i,k]]] integral[[i,k]];
		ZT[[i,k]] += coefReflexao ImpedanciaTransversalMutua[imagens[[i]],eletrodos[[k]],\[Gamma],c,intg];
		ZL[[i,k]] += (1 - coefReflexao) ImpedanciaLongitudinalMutua[imagens[[i]],eletrodos[[k]],\[Gamma],\[Mu],\[Omega],intg];
		ZT[[k,i]] = ZT[[i,k]];
		ZL[[k,i]] = ZL[[i,k]];
		,{i,1,numEletrodos},{k,i,numEletrodos}
	];
	Return[{ZT,ZL}]
]
IncluirImagensImpedanciaSimples::usage=
"Adiciona \[AGrave]s matrizes de imped\[AHat]ncia longitudinal e transvesal o efeito das imagens. Se houver m\[UAcute]ltiplas imagens para um mesmo eletrodo, use esta fun\[CCedilla]\[ATilde]o recursivamente.
Versao otimizada para caso simplificado.
Argumentos:
	zt: matriz de imped\[AHat]ncia transveral;
	zl: matriz de imped\[AHat]ncia longitudinal;
	eletrodos: lista de listas dos eletrodos '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	imagens: lista de listas, onde imagens[[i]] \[EAcute] a imagem de eletrodos[[i]] (se n\[ATilde]o houver imagem para ele, ent\[ATilde]o ela deve ser Null. Neste caso, inclusive, o eletrodo n\[ATilde]o receber\[AAcute] influ\[EHat]ncia de qualquer imagem);
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	integral: matriz do valor das integrais;
	etam: matriz de distancias medias entre eletrodos;
	etai: matriz de distancias medias entre eletrodos e imagens;
	coefReflexao: opicional, o coeficiente de reflex\[ATilde]o para as imagens;
		padr\[ATilde]o = 1.0
-------
Retorna:
	ZT: matriz de imped\[AHat]ncia transveral com efeito das imagens incluso;
	ZL: matriz de imped\[AHat]ncia longitudinal com efeito das imagens incluso.";


(* ::Section:: *)
(*Montar e resolver sistema*)


ResolverEletrodos[eletrodos_,zt_,zl_,correntesInjetadas_,nodes_,ynodal_:{}]:=
Block[{A,B,C,D,E,We,Ie,solucao,numEletrodos,numNodes,v,u,il1,il2,il,it},
	numEletrodos = Dimensions[eletrodos][[1]];
	numNodes = Dimensions[nodes][[1]];
	E = If[ynodal =!= {},
			ynodal,
			(*else*)ConstantArray[0, {numNodes, numNodes}]
	];
	C = Table[
		v = 0;
		If[eletrodos[[i,1]] === nodes[[k]], v = 1];
		v
		,{k,numNodes},{i, numEletrodos}
	];
	D = Table[
		v = 0;
		If[eletrodos[[i,2]] === nodes[[k]], v = -1];
		v
		,{k,numNodes},{i, numEletrodos}
	];
	A = Table[
		v = 0;
		If[eletrodos[[i,1]] === nodes[[k]], v = -1];
		If[eletrodos[[i,2]] === nodes[[k]], v = 1];
		v
		,{i, numEletrodos},{k,numNodes}
	];
	(*A = Transpose[C + D];*)
	B = -Abs[A]/2;
	We = ArrayFlatten[{ {A, zl/2, -zl/2}, {B, zt, zt}, {E, C, -D} }];
	Ie = Join[Table[0, Length[We] - numNodes], correntesInjetadas];
	solucao = LinearSolve[We, Ie];
	u = solucao[[1;;numNodes]];
	il1 = solucao[[numNodes + 1 ;; -numEletrodos - 1]];
	il2 = solucao[[-numEletrodos;;]];
	il = (il1 - il2)/2;
	it = il1 + il2;
	Return[{u, it, il}]
]
ResolverEletrodos::usage=
"Resolve o sistema de eletrodos, calculando o potencial em cada node e as correntes transversal e longitudinal em cada eletrodo.
Argumentos:
	eletrodos: lista de listas '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	zt: a matriz de imped\[AHat]ncia transversal dos eletrodos;
	zl: a matriz de imped\[AHat]ncia longitudinal dos eletrodos;
	correntesInjetadas: a corrente injetada em cada node;
	nodes: lista de todos os pontos \[UAcute]nicos do sistema (extra\[IAcute]dos dos pontos iniciais e finais dos eletrodos);
	ynodal: opicional, matriz quadrada (dimens\[ATilde]o=n\[UAcute]mero de nodes) das admit\[AHat]ncias (externas) conectadas aos nodes.
		padr\[ATilde]o = zeros
-------
Retorna:
	u: o potencial nos nodes;
	it: a corrente transversal nos eletrodos;
	il: a corrente longitudinal nos eletrodos;";


(* ::Section:: *)
(*Campo El\[EAcute]trico*)


CampoEletricoInduzido[ponto_,eletrodos_,it_,\[Gamma]_,c_,coefReflexao_:1]:=
Block[{Ls,R1,R2,\[Gamma]\[Eta],K1,Ex,Ey,Ez,numEletrodos},
	numEletrodos = Dimensions[eletrodos][[1]];
	Ls = Table[Norm[ eletrodos[[i,1]] - eletrodos[[i,2]] ], {i, numEletrodos}];
	R1 = Table[Norm[ponto - eletrodos[[i,1]]], {i, numEletrodos}];
	R2 = Table[Norm[ponto - eletrodos[[i,2]]], {i, numEletrodos}];
	\[Gamma]\[Eta] = \[Gamma] Table[Norm[ponto - (eletrodos[[i,1]] + eletrodos[[i,2]])/2], {i, numEletrodos}];
	K1 = Table[(1 + \[Gamma]\[Eta][[i]]) Exp[-\[Gamma]\[Eta][[i]]] coefReflexao it[[i]]/( (R1[[i]] + R2[[i]] + Ls[[i]]) (R1[[i]] + R2[[i]] - Ls[[i]]) ),{i, numEletrodos}];
	Ex = Sum[K1[[i]] ( (ponto[[1]] - eletrodos[[i,1,1]])/R1[[i]] + (ponto[[1]] - eletrodos[[i,2,1]])/R2[[i]] ), {i, numEletrodos}];
	Ey = Sum[K1[[i]] ( (ponto[[2]] - eletrodos[[i,1,2]])/R1[[i]] + (ponto[[2]] - eletrodos[[i,2,2]])/R2[[i]] ), {i, numEletrodos}];
	Ez = Sum[K1[[i]] ( (ponto[[3]] - eletrodos[[i,1,3]])/R1[[i]] + (ponto[[3]] - eletrodos[[i,2,3]])/R2[[i]] ), {i, numEletrodos}];
	Return[1/(2 Pi c) {Ex,Ey,Ez}]
]
CampoEletricoInduzido::usage=
"Calcula o campo el\[EAcute]trico radial Ec induzido num ponto pelas correntes transversais nos eletrodos.
Argumentos:
	ponto: coordenadas retangulares na forma {x,y,z};
		obs: n\[ATilde]o usar {0,0,0}, use e.g. {\!\(\*SuperscriptBox[\(10\), \(-9\)]\),\!\(\*SuperscriptBox[\(10\), \(-9\)]\),\!\(\*SuperscriptBox[\(10\), \(-9\)]\)} para evitar erro.
	eletrodo: lista '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	it: as correntes transversais nos eletrodos;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	coefReflexao: opicional, o coeficiente de reflex\[ATilde]o para aplicar nas correntes;
		padr\[ATilde]o = 1
-------
Retorna:
	{Ecx, Ecy, Ecz}: o campo el\[EAcute]trico em coordenadas retangulares.";


CampoEletricoPotencial[ponto_,eletrodos_,il_,\[Gamma]_,\[Omega]_,\[Mu]_,coefReflexao_:1]:=
Block[{numEletrodos,\[Eta],R1,R2,Nf,K2,Ls,Aox,Aoy,Aoz},
	numEletrodos = Dimensions[eletrodos][[1]];
	\[Eta] = Table[Norm[ponto - (eletrodos[[i,1]] + eletrodos[[i,2]])/2], {i, numEletrodos}];
	R1 = Table[Norm[ponto - eletrodos[[i,1]]], {i, numEletrodos}];
	R2 = Table[Norm[ponto - eletrodos[[i,2]]], {i, numEletrodos}];
	Nf = Table[(R1[[i]] + R2[[i]] + \[Eta][[i]])/(R1[[i]] + R2[[i]] - \[Eta][[i]]), {i, numEletrodos}];
	Ls = Table[Norm[ eletrodos[[i,1]] - eletrodos[[i,2]] ], {i, numEletrodos}];
	K2 = Table[coefReflexao il[[i]] Log[ Nf[[i]] ]/(Ls[[i]]),{i, numEletrodos}];
	Aox = Sum[K2[[i]] (eletrodos[[i,2,1]] - eletrodos[[i,1,1]]), {i, numEletrodos}];
	Aoy = Sum[K2[[i]] (eletrodos[[i,2,2]] - eletrodos[[i,1,2]]), {i, numEletrodos}];
	Aoz = Sum[K2[[i]] (eletrodos[[i,2,3]] - eletrodos[[i,1,3]]), {i, numEletrodos}];
	Return[-I \[Omega] \[Mu]/(4 Pi) {Aox, Aoy, Aoz}]
]
CampoEletricoPotencial::usage=
"Calcula o campo el\[EAcute]trico radial EA gerado pelo vetor potencial magn\[EAcute]tico \!\(\*OverscriptBox[\(A\), \(\[Rule]\)]\).
Argumentos:
	ponto: coordenadas retangulares na forma {x,y,z};
		obs: n\[ATilde]o usar {0,0,0}, use e.g. {\!\(\*SuperscriptBox[\(10\), \(-9\)]\),\!\(\*SuperscriptBox[\(10\), \(-9\)]\),\!\(\*SuperscriptBox[\(10\), \(-9\)]\)} para evitar erro.
	eletrodos: lista '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	il: as correntes longitudinais nos eletrodos;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	\[Omega]: frequ\[EHat]ncia angular;
	\[Mu]: permeabilidade magn\[EAcute]tica do meio;
	coefReflexao: opicional, o coeficiente de reflex\[ATilde]o para aplicar nas correntes;
		padr\[ATilde]o = 1
-------
Retorna:
	{EAx, EAy, EAz}: o campo el\[EAcute]trico em coordenadas retangulares.";


(* ::Section:: *)
(*Potencial Escalar*)


(* ::Input::Initialization:: *)
(*escalar; c=\[Sigma]+I\[Omega]\[Epsilon]*)
CalcularPotencial[ponto_,eletrodos_,it_,\[Gamma]_,c_,coefReflexao_:1]:=
Block[{pmedio,\[Eta],Ls,R1,R2,Nf},
Sum[
	pmedio=(eletrodos[[i,1]]+eletrodos[[i,2]])/2;
	\[Eta]=Norm[ponto-pmedio];
	Ls=Norm[eletrodos[[i,1]]-eletrodos[[i,2]]];
	R1 = Norm[ponto - eletrodos[[i,1]]];
	R2 = Norm[ponto - eletrodos[[i,2]]];
	Nf = (R1 + R2 + Ls)/(R1 + R2 - Ls);
	Exp[-\[Gamma] \[Eta]] coefReflexao it[[i]] Log[Nf]/(4 Pi Ls c)
	,{i,eletrodos//Length}]
]
CalcularPotencial::usage=
"Calcula o potencial escalar gerado pelas correntes transversais de todos os eletrodos. Se existirem imagens, esta fun\[CCedilla]\[ATilde]o deve ser chamada novamente considerando-as como os eletrodos e aplicando o coeficiente de reflex\[ATilde]o.
Argumentos:
	ponto: coordenadas retangulares na forma {x,y,z};
	eletrodos: lista '{{ponto_inicial}, {ponto_final}, raio, imped\[AHat]ncia_interna_total}';
	it: as correntes transversais nos eletrodos;
	\[Gamma]: constante de propaga\[CCedilla]\[ATilde]o do meio;
	c: condutividade el\[EAcute]trica complexa do meio (\[Sigma] + I \[Omega] \[Epsilon]);
	coefReflexao: opicional, o coeficiente de reflex\[ATilde]o para aplicar nas correntes;
		padr\[ATilde]o = 1
-------
Retorna:
	potencial el\[EAcute]trico (complexo) no ponto";


(* ::Section:: *)
(*Grid eletrodos*)


(* ::Input::Initialization:: *)
(*https://mathematica.stackexchange.com/a/30706*)
meshgrid[x_List,y_List]:={ConstantArray[x,Length[x]],Transpose@ConstantArray[y,Length[y]]}


(* ::Input::Initialization:: *)
CriarGridEletrodos[z_,raio_,a_,m_,b_,n_]:=
Block[{rangex,rangey,pontos2d,nodes,eletrodosHorizontais,eletrodosVerticais},
	rangex=Range[-b/2,b/2,n];
	rangey=Range[-a/2,a/2,m];
	pontos2d=Table[{x,y},{x,rangex},{y,rangey}];
	pontos2d=ArrayFlatten[pontos2d,1];
	nodes=Table[Join[ponto,{z}],{ponto,pontos2d}];
	eletrodosHorizontais=Table[
	Block[{xx,yy,pontos,ni,nodesTemp},
		ni=Length[rangex];
		{xx,yy}=meshgrid[rangex,ConstantArray[y,ni]];
		pontos=Flatten[{xx,yy},{2,3}];
		nodesTemp=Table[Join[pt,{z}],{pt,pontos}];
		Table[{nodesTemp[[i]],nodesTemp[[i+1]],raio,0},{i,ni-1}]
	],{y,rangey}];
	eletrodosHorizontais=ArrayFlatten[eletrodosHorizontais,1];
	eletrodosVerticais=Table[
	Block[{xx,yy,pontos,ni,nodesTemp},
		ni=Length[rangey];
		{xx,yy}=meshgrid[ConstantArray[x,ni],rangey];
		yy=Transpose[yy];
		pontos=Flatten[{xx,yy},{2,3}];
		nodesTemp=Table[Join[pt,{z}],{pt,pontos}];
	Table[{nodesTemp[[i]],nodesTemp[[i+1]],raio,0},{i,ni-1}]
	],{x,rangex}];
	eletrodosVerticais=ArrayFlatten[eletrodosVerticais,1];
	{nodes,Join[eletrodosHorizontais,eletrodosVerticais]}
]
CriarGridEletrodos::usage=
"Cria uma malha retangular de eletrodos de lados 'a' e 'b', espa\[CCedilla]ados 'a/n' e 'b/m' considerando a coordenada 'z' como profundide.
Argumentos:
	z: a profundidade dos eletrodos;
	raio: o raio dos eletrodos;
	a: o comprimento do primeiro lado;
	m: o espa\[CCedilla]amento do primeiro lado;
	b: o comprimento do segundo lado;
	n: o espa\[CCedilla]amento do segundo lado;
-------
Retorna:
	{nodes, eletrodos}";

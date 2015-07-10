-- -*- coding: utf-8 -*-

-- Last edited 14 January 2014

--*************************************************************************
-- HEADER --
--*************************************************************************

-- I would like to thank Prof Gregory Smith who initially developed a 
-- substantial part of this package, as well as for his advice during 
-- its development. I also thank Dr Alastair Craw for his supervision 
-- and Tom Hawes for his advice.

newPackage(
	"QuiversToricVarieties",
    	Version => "1.0.0", 
    	Date => "November 06, 2012",
    	Authors => {
	     {Name => "Nathan Prabhu-Naik", 
	      Email => "n.prabhu-naik@bath.ac.uk", 
	      HomePage => "http://people.bath.ac.uk/npn22/"}
	     },
    	Headline => "a package to construct and manipulate the quiver of 
	sections for a smooth toric variety with a given collection of 
	line bundles",
	AuxiliaryFiles => true, 
	-- set to true if package comes with auxiliary files
  	PackageExports => {"NormalToricVarieties"},
  	PackageImports => {"FourierMotzkin","LLLBases"},
    	DebuggingMode => false		 
	-- set to true only during development
    	)

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export{
     "quiver",
     "Quiver",
     "QuiverArrow",
     "tCharacterMap",
     "tDivisorMap",
     "picardMap",
     "contractionList",
     "blowUpCone",
     "exceptionalDivisor",
     "primitiveRelations", 
     "fullStrExcColl",
     "doHigherSelfExtsVanish",
     "resOfDiag",
     "bundlesNefCheck",     
     "quiverToResMap",
     "label",
     "forbiddenSets",
     "toricFanoContractions"
      }


--**********************************************
-- BODY --
--**********************************************

debug Core

------------------------------------------------
-- FUNCTIONS NOT EXPORTED --
-- (Can be viewed via listLocalSymbols command)
------------------------------------------------

------------------------------------------------
-- anticanDiv (Non-exported function)
-- The anticanonical divisor in Cl X 
------------------------------------------------

anticanDiv = X -> (
sum entries transpose fromWDivToCl X);

------------------------------------------------
-- degs (Non-exported function)
-- The degrees of the torus-invariant divisors of X 
------------------------------------------------

degs = X -> (
     entries transpose fromWDivToCl X);

------------------------------------------------
-- irrel (Non-exported function)
-- Creates the irrelevent ideal for the product
-- of toric varieties XxX, in the variables needed
-- for resOfDiag function 
------------------------------------------------

irrel = X -> (
 x := symbol x;
 w := symbol w;
 SS := QQ[x_1..x_(#rays X), w_1..w_(#rays X), 
     Degrees =>
     join(apply(degs X, i -> (
      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
      i|zerolist)),
     apply(degs X, i -> (
      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
      zerolist|i)))];
   intersect(
    ideal apply(apply(
	    (entries generators ideal X)#0, i -> indices i), j ->
 	product apply(j, k -> x_(k+1))),
    ideal apply(apply(
	    (entries generators ideal X)#0, i -> indices i), j ->
     	product apply(j, k -> w_(k+1)))));

------------------------------------------------
-- getContractionList (Non-exported function)
-- Reads the database for the contractionList function 
------------------------------------------------

f1 := currentFileDirectory | 
"QuiversToricVarieties/ToricFanoContractionLists.txt";
getContractionList = hashTable apply(lines get f1, x -> (
	x = value x;
	(x#0,x#1)));

------------------------------------------------
-- getFanoConData (Non-exported function)
-- Reads the database for the tCharacterMap, tDivisorMap,
-- picardMap,exceptionalDivisor and blowupCone functions
------------------------------------------------

f2 := currentFileDirectory | 
"QuiversToricVarieties/ToricFanoContractions.txt";
getFanoConData = hashTable apply(lines get f2, x -> (
	x = value x;
	((x#0,{x#1,x#2}), drop(x,3))));

------------------------------------------------
-- resOfDiagData (Non-exported function)
-- Reads the database for the primitiveRelations,
-- fullStrExcColl and the resOfDiag functions
------------------------------------------------

f3 := currentFileDirectory | 
"QuiversToricVarieties/FullStrongExcCollections.txt";
resOfDiagData = hashTable apply(lines get f3, y -> (
	x := value y;
	((x#0,x#1),flatten toList drop(x,2))));

------------------------------------------------
-- EXPORTED FUNCTIONS (unless otherwise stated) --
------------------------------------------------

------------------------------------------------
-- contractionList
-- Each dimension i returns a list. The list contains pairs of
-- numbers {j,k} which indicate that there is a divisorial contraction
-- between the dimension i toric Fano smooth varieties indexed by j and k
------------------------------------------------

contractionList = method();
contractionList ZZ := i -> (
    --input is the dimension of the toric Fano smooth varieties
    if i < 1 then (
	error "-- expected positive dimension")
    else if i === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if i > 4 then (
	error "-- not in database")
    else getContractionList#i)

------------------------------------------------
-- toricFanoContractions
-- Each dimension n and index i returns a list. The list contains 
-- lists of the form {i,i_1,i_2,...,i_k} which indicate that there
-- is a chain of divisorial contractions from the i^th smooth toric
-- Fano variety of dimension n to the i_k^th smooth toric Fano 
-- variety of dimension n, via the n dimensional smooth toric Fano
-- varieties indexed by the list
------------------------------------------------

toricFanoContractions = method();
toricFanoContractions(ZZ,ZZ) := (n,i) -> (
    X := smoothFanoToricVariety(n,i);
    C := new MutableHashTable;
    C#0 = select(contractionList n, j -> first j == i);
    if #C#0 == 0 then ( 
    "variety is birationally-minimal") else
    (r := rank pic X;
    j := 1;
    while r-j > 0 do (
	L := sort unique apply(C#(j-1),last);
	C#j = sort flatten apply(L, k ->
	    select(contractionList n, l -> first l == k)
	    );
	j = j+1);
    M := max select(r, k -> C#k != {});
scan(-M..-1, k -> (
	while C#(-k) != {} do (
	    l := first C#(-k);
	    K := select(C#(-k-1), m -> last m == first l);
	    T := apply(K, m -> ( 
		-sort(-unique(l|m))));
	    C#(-k-1) = sort((C#(-k-1))|T);
	    C#(-k) = drop(C#(-k),1))));
select(C#0, k -> not any(toList(set C#0 - {k}), l -> (
	    isSubset(k,l))))))
 
------------------------------------------------
-- tCharacterMap
-- For each dimension there is a poset of toric Fano varieties determined 
-- by divisorial contractions. The input for this function is the dimension
-- and a list corresponding to a decreasing chain in the poset of 
-- divisorial contractions. The output is the corresponding map between the
-- character lattice of the first variety on the list and the character 
--lattice of the last variety on the list
------------------------------------------------

tCharacterMap = method(TypicalValue => Matrix)
tCharacterMap (ZZ,List) := (nn,L) -> (
   -- input is the dimension of the toric Fano smooth varieties and a 
   -- list enumerating the varieties in a chain of divisorial contractions
if nn < 1 then (
	error "-- expected positive dimension")
    else if nn === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if nn > 4 then (
	error "-- not in database")
    else if #L < 2 then (
	error "--expected more than one variety")
    else if #L === 2 then (
	if not getFanoConData#?(nn,L) then (
	error "-- no divisorial contraction between the chosen varieties")
	else matrix getFanoConData#(nn,L)#0)
    else if #L > 2 then (
	LL := apply(0..#L-2, i -> {L#i,L#(i+1)});
	if all(LL, i -> getFanoConData#?(nn,i)) then (
	    times(apply(reverse LL, i -> (
		matrix getFanoConData#(nn,i)#0))))
   --produces the product of the matrices for the varieties in the list
    	else (
    error "-- no decreasing chain of divisorial contractions 
    --between chosen varieties"))) 

------------------------------------------------
-- tDivisorMap
-- For each dimension there is a poset of toric Fano varieties determined 
-- by divisorial contractions. The input for this function is the dimension
-- and a list corresponding to a decreasing chain in the poset of 
-- divisorial contractions. The output is the corresponding map between the
-- torus-invariant divisor lattice of the first variety on the list and the
-- torus-invariant divisor lattice of the last variety on the list
------------------------------------------------

tDivisorMap = method(TypicalValue => Matrix)
tDivisorMap (ZZ,List) := (nn,L) -> (
    -- input is the dimension of the toric Fano smooth varieties and a list
    -- enumerating the varieties in a chain of divisorial contractions
if nn < 1 then (
	error "-- expected positive dimension")
    else if nn === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if nn > 4 then (
	error "-- not in database")
    else if #L < 2 then (
	error "--expected more than one variety")
    else if #L === 2 then (
	if not getFanoConData#?(nn,L) then (
        error "-- no divisorial contraction between the chosen varieties")
	else matrix getFanoConData#(nn,L)#1)
    else if #L > 2 then (
	LL := apply(0..#L-2, i -> {L#i,L#(i+1)});
	if all(LL, i -> getFanoConData#?(nn,i)) then (
	    times(apply(reverse LL, i -> (
		matrix getFanoConData#(nn,i)#1))))
   --produces the product of the matrices for the varieties in the list
    	else (
    error "-- no decreasing chain of divisorial contractions 
    --between chosen varieties"))) 

------------------------------------------------
-- picardMap
-- For each dimension there is a poset of toric Fano varieties determined 
-- by divisorial contractions. The input for this function is the dimension
-- and a list corresponding to a decreasing chain in the poset of 
-- divisorial contractions. The output is the corresponding map between the
-- Picard lattice of the first variety on the list and the Picard lattice
-- of the last variety on the list
------------------------------------------------

picardMap = method(TypicalValue => Matrix)
picardMap (ZZ,List) := (nn,L) -> (
    -- input is the dimension of the toric Fano smooth varieties and a list
    -- enumerating the varieties in a chain of divisorial contractions
if nn < 1 then (
	error "-- expected positive dimension")
    else if nn === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if nn > 4 then (
	error "-- not in database")
    else if #L < 2 then (
	error "--expected more than one variety")
    else if #L === 2 then (
	if not getFanoConData#?(nn,L) then (
	error "-- no divisorial contraction between the chosen varieties")
	else matrix getFanoConData#(nn,L)#2)
    else if #L > 2 then (
	LL := apply(0..#L-2, i -> {L#i,L#(i+1)});
	if all(LL, i -> getFanoConData#?(nn,i)) then (
	    times(apply(reverse LL, i -> (
		matrix getFanoConData#(nn,i)#2))))
    --produces the product of the matrices for the varieties in the list
    	else (
    error "-- no decreasing chain of divisorial contractions 
    --between chosen varieties"))) 

------------------------------------------------
-- exceptionalDivisor
-- For each dimension there is a poset of toric Fano varieties determined 
-- by divisorial contractions. The input for this function is the dimension
-- and a list corresponding to a divisorial contraction between two 
-- varieties. The output is the ray corresponding to the exceptional 
-- divisor of the contraction, in the basis of the blow up
------------------------------------------------

exceptionalDivisor = method(TypicalValue => List)
exceptionalDivisor (ZZ,List) := (nn,L) -> (
-- input is the dimension of the toric Fano smooth varieties and a list
-- enumerating the pair of varieties involved in the divisorial contraction
if nn < 1 then (
	error "-- expected positive dimension")
    else if nn === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if nn > 4 then (
	error "-- not in database")
    else if #L === 2 then (
	if not getFanoConData#?(nn,L) then (
	error "-- no divisorial contraction between the chosen varieties")
	else getFanoConData#(nn,L)#3)
    else if #L =!= 2 then (
	error "-- expected two toric Fano smooth varieties"))

------------------------------------------------
-- blowUpCone
-- For each dimension there is a poset of toric Fano varieties determined 
-- by divisorial contractions. The input for this function is the dimension
-- and a list corresponding to a divisorial contraction between two 
-- varieties. The output are the rays of the cone in the contraction that 
-- corresponds to the subvariety that will be blown up. The rays are given
-- in the basis of the blow up
------------------------------------------------

blowUpCone = method(TypicalValue => List)
blowUpCone (ZZ,List) := (nn,L) -> (
-- input is the dimension of the toric Fano smooth varieties and a list 
-- enumerating the pair of varieties involved in the divisorial contraction
if nn < 1 then (
	error "-- expected positive dimension")
    else if nn === 1 then (
	error "-- there is only one smooth Fano toric curve")
    else if nn > 4 then (
	error "-- not in database")
    else if #L === 2 then (
	if not getFanoConData#?(nn,L) then (
	error "-- no divisorial contraction between the chosen varieties")
	else getFanoConData#(nn,L)#4)
    else if #L =!= 2 then (
	error "-- expected two toric Fano smooth varieties"))	

------------------------------------------------
-- Quiver
-- Creates the 'type' Quiver.
------------------------------------------------

Quiver = new Type of MutableHashTable
Quiver.synonym = "quiver of sections"
Quiver.GlobalAssignHook = globalAssignFunction
Quiver.GlobalReleaseHook = globalReleaseFunction
net Quiver := Q -> (
     if hasAttribute(Q,ReverseDictionary) 
     then toString getAttribute(Q,ReverseDictionary) 
     else horizontalJoin(net "Q_0 = ", net Q_0, 
	 net " and Q_1 = ", net Q_1))
Quiver#{Standard,AfterPrint} = Q -> (
     X := variety Q;
     << endl;
     << concatenate(interpreterDepth:"o") << lineNumber << 
     " : quiver of sections on " << X;
     << endl;)

------------------------------------------------
-- quiver
-- Creates the quiver of sections for a normal toric variety, either from a
-- list of vertices and arrows, or from a list of elements in the Picard 
-- lattice
------------------------------------------------

quiver = method(TypicalValue => Quiver)
-- creates a quiver given vertices and arrows
quiver (List, List, NormalToricVariety) := (vertices,arrows,X) -> (
     n := #vertices;
     new Quiver from {{symbol variety, X}, {symbol size, n}, 
	  {symbol cache, new CacheTable}} | apply(n, i -> (
	       out := select(arrows, p -> p#0#0 == i);
	       H := new HashTable from 
	       {{symbol degree, vertices#i}} | apply(
		   out, p -> {p#0#1,p#1});
	       {i,H})))


quiver(List,NormalToricVariety) := Quiver => (L',X) -> (
-- creates a quiver given vertices; it finds the minimal (irreducible) set
-- of arrows
     S := ring X;     
     h := (options monoid S)#Heft;
     L := apply(sort apply(unique L', f -> {sum(
		     #h, i -> h#i*f#i)} | f ), l -> drop(l,1));
     n := #L;     
     arrows := {};
     scan(n-1, i -> scan(i+1..n-1, j -> (
		    B := first entries basis(L#j-L#i,S);
		    if #B > 0 then arrows = arrows | {{(i,j),B}})));
     if arrows == {} then quiver(L,arrows,X)
     --creates the quiver with no arrows in this case
     else (	
     Q' := quiver(L,arrows,X);
     M := entries transpose mingens image quiverMap Q';
     R := ring M#0#0;
     RtoS := map(S,R, (gens S) | toList(numgens S:1_S));
     H := new MutableHashTable;
     scan(n, i -> H#i = new MutableHashTable);
     scan(#M, i -> (
	       p := select(toList(0..n-1), j -> M#i#j != 0);
	       if not H#(p#0)#?(p#1) then 
	       H#(p#0)#(p#1) = {- product(p, k -> RtoS(M#i#k))}
	       else H#(p#0)#(p#1) = 
	       {- product(p, k -> RtoS(M#i#k))} |  H#(p#0)#(p#1) ));
     arrows = {}; 
     scan(n, i -> scan(keys H#i, j -> arrows = arrows | {{(i,j), H#i#j}}));
     quiver(L,arrows,X)))


variety Quiver := NormalToricVariety => Q -> Q.variety

QuiverArrow = new Type of MutableHashTable
QuiverArrow.synonym = "quiver arrow"
net QuiverArrow := a -> horizontalJoin(net "arrow", (net index a)^(-1))

index QuiverArrow := ZZ => a -> a.index
source QuiverArrow := ZZ => a -> a.source
target QuiverArrow := ZZ => a -> a.target
label = method(TypicalValue => RingElement)
label QuiverArrow := RingElement => a -> a.label

Quiver _ ZZ := List => (Q,n) -> (
     if n == 0 then toList(0..Q.size -1)
     else if n == 1 then (
	 arrowList := getSymbol "arrowList";
	  if not Q.cache#?arrowList then (
	       arrows := {};
	       l := 1;
	       scan(Q_0, i -> (
	  	    	 directions := sort select(
			     keys Q#i, k -> instance(k,ZZ));
	  	    	 scan(directions, j -> scan(Q#i#j, r -> (
				   	a := new QuiverArrow from {
					     symbol index => l,
					     symbol source => i,
					     symbol target => j,
					     symbol label => r};
					l = l+1;
					arrows = arrows | {a})))));
	       Q.cache#arrowList = arrows);
	  Q.cache#arrowList))


-- creates a map of vector bundles on X*X
quiverMap = method(TypicalValue => Matrix)
quiverMap Quiver := Matrix => Q -> (
     if not Q.cache.?map then (
	  r := Q.size;
     	  X := variety Q;
     	  n := #rays X;     
     	  S := ring X;
     	  R := S**S;                       --previously, ring(X**X)    
     	  StoR := map(R,S, (gens R)_{0..n-1});
     	  StoR' := map(R,S, (gens R)_{n..2*n-1});
     	  rows := {};
     	  sourceDeg := {};
     	  scan(r, i -> (
	      arrows := select(keys Q#i, k -> instance(k,ZZ));
	      if #arrows > 0 then scan(arrows, j -> (
	      	      rows = rows | apply(Q#i#j, g -> apply(r, 
		   	l -> if l == i then (
			     e := StoR(g);
			     sourceDeg = sourceDeg | {{i,degree(e)}};
			     - e) 
		else if l == j then StoR'(g) else 0_R))))));
     	  M := transpose matrix rows;
     	  targetDeg := apply(r, i -> (
	       	    v := (Q#i).degree;
	       	     -v | v ));
     	  sourceDeg = apply(sourceDeg, p -> targetDeg#(p#0) - p#1);
     	  Q.cache.map = map(R^targetDeg, R^sourceDeg, M));
     Q.cache.map)


------------------------------------------------
-- nonVanishingCohomology
-- Computes the non-vanishing cohomlogy cones in the Picard lattice of
-- a toric variety 
------------------------------------------------
  
nonVanishingCohomology = X -> (
 if not X.cache.?cones then (  
-- create (fine graded) coordinate ring and irrelevant ideal of X
     n := #rays X;
     deg := entries id_(ZZ^n);
     h := toList(n:1);
     S := ring X;
     fineS := QQ(monoid [gens S, Degrees => deg, Heft => h]);
     StoFineS := map(fineS, S, gens fineS);
     J := StoFineS ideal X;
-- using simplicial cohomology find the support sets of the nonVanishing
-- cones
     cellularComplex := Hom(res (fineS^1/J), fineS^1);
     supportSets := delete({},subsets(toList(0..n-1)));
     d := dim X;
     omega:= new MutableHashTable;
     scan(1..d, i -> (
     	simplicialHH := prune HH^(i+1)(cellularComplex);
       	omega#i = select(supportSets, 
	    s -> basis(-degree product(
		    s, j -> fineS_j), simplicialHH) != 0)));
     	     -- compute the nonVanishing cones
  	A := fromWDivToCl X;
     	cones := new MutableHashTable;
     	cones#0 = {map(ZZ^1,ZZ^(n-d),0), (fourierMotzkin A)#0};
     	scan(1..d, i -> cones#i = apply(omega#i, s -> (
	    translation := - sum(s, j -> A_{j});
	    M := matrix table(n, n, (p,q) -> if p == q then (
		    if member(p,s) then -1 else 1) else 0);
	    	    outerNorm := (fourierMotzkin (A*M))#0;
	    	    {translation, outerNorm})));
     	     X.cache.cones = new HashTable from pairs cones);
     X.cache.cones)

------------------------------------------------
-- forbiddenSets
-- This function computes the forbidden sets of a toric variety, that is 
-- the subsets of rays of the defining fan that determine non vanishing
-- cohomology cones in the Picard lattice 
------------------------------------------------   

forbiddenSets =  method(TypicalValue => MutableHashTable)
forbiddenSets (NormalToricVariety) := X -> (
-- create (fine graded) coordinate ring and irrelevant ideal of X
     n := #rays X;
     deg := entries id_(ZZ^n);
     h := toList(n:1);
     S := ring X;
     fineS := QQ(monoid [gens S, Degrees => deg, Heft => h]);
     StoFineS := map(fineS, S, gens fineS);
     J := StoFineS ideal X;
-- using simplicial cohomology find the support sets of the nonVanishing 
-- cones
     cellularComplex := Hom(res (fineS^1/J), fineS^1);
     supportSets := delete({},subsets(toList(0..n-1)));
     d := dim X;
     gamma:= new MutableHashTable;
     scan(1..d, i -> (
        simplicialHH := prune HH^(i+1)(cellularComplex);
        gamma#i = select(supportSets, 
   	    s -> basis(-degree product(
		    s, j -> fineS_j), simplicialHH) != 0)));
    gamma)

------------------------------------------------
-- pullbackCones(non-exported function)
-- Given a list of divisorial contractions for toric Fano smooth varieties
-- along with their dimension, the function computes the preimage of the 
-- non-zero cohomology cones in the Picard lattice for the maximal variety
-- under the Picard lattice maps  
------------------------------------------------  

pullbackCones = (nn,L) -> (
 X := smoothFanoToricVariety(nn,L#0);
--the 'maximal' variety
 LLength := #L;
 oldL := L;
 pbDetails := new MutableHashTable;
 while #L > 1 do (
   tDiv := tDivisorMap(nn,L);
   excDivs := select(numgens tDiv.source, i -> (
	 tDiv_i == vector(toList(numgens tDiv.target :0))));
   perm := select(
      (0,0)..(numgens tDiv.target -1, numgens tDiv.source -1), i -> 
      tDiv_i == 1);
--permutation of the divisors
   Perm := hashTable(toList perm); 
   Y := smoothFanoToricVariety(nn, last L);
   A1:= forbiddenSets Y;
--the forbidden sets for Y using the enumeration for Y
   forbiddens0 := apply(
       flatten values A1, i -> sort apply(i, j -> Perm#j));
--the forbidden sets for Y using the enumeration for X
   forbiddens := forbiddens0;
   scan(forbiddens0, i -> (if (any(keys pbDetails, j -> (
		   rmExc := sort toList(set i - pbDetails#j#0);
		   any(pbDetails#j#1, k -> (
			   k == rmExc))))) then
       forbiddens = delete(i,forbiddens)));
--removes forbidden sets covered by those from previous varieties
   pbDetails#(LLength - #L) = (excDivs, forbiddens);
   L = delete(last L, L);
	    );
 gamma0 := flatten values forbiddenSets X;
 gamma := gamma0;
 apply(gamma0, i -> (if (any(keys pbDetails, j -> (
		   rmExc := sort toList(set i - pbDetails#j#0);
		   any(pbDetails#j#1, k -> (
			   k == rmExc))))) then
       gamma = delete(i,gamma)));
--removes forbidden sets covered by those from previous varieties
pbDetails#(LLength-1) = ({},gamma);
--the unaffected nonvanishing cones for X 
 d := #rays X;
 A := fromWDivToCl X;      
--to calculate the nonvanishing cones in the Picard lattice  
 preImageCones := new MutableHashTable;
     	scan(keys pbDetails, i -> preImageCones#(
	 oldL#(LLength-1-i)) = apply(
	  pbDetails#i#1, s -> (
	    translation := - sum(s, j -> A_{j});
	    M0 := matrix table(d, d, (p,q) -> if member(
		    p,pbDetails#i#0) then 0
	      else if p == q then 
	         (if member(p,s) then -1 else 1) else 0);
	    M := transpose matrix({toList (d:0)});
	    apply(d, i -> if M0_i == vector(toList(d:0)) then
		M = M|((id_(ZZ^d))_{i})|(-((id_(ZZ^d))_{i}))
		else
		M = M|(M0_{i}));
	  outerNorm := (fourierMotzkin (A*M))#0;
    {translation, outerNorm})));
  X.cache.preImageCones = new HashTable from pairs preImageCones;
  X.cache.preImageCones)

------------------------------------------------
-- doHigherSelfExtsVanish
-- This function determines if a collection of (normalised) line bundles 
-- have any higher self-extensions
------------------------------------------------    

doHigherSelfExtsVanish = method()     
doHigherSelfExtsVanish Quiver := Q -> (
    --input is a quiver
    L := apply(#Q_0, i -> Q#i.degree);
    --the list of line bundles determining the quiver
     X := variety Q;
     d := dim X;
     T := new MutableHashTable;
     --the keys are L1 - L2 for L1, L2 in L  
     scan(L, l -> T#l = true);
     scan(subsets(#Q_0,2), p -> (
	       l := L#(p#0) - L#(p#1);
	       if not T#?l then T#l = true;
	       if not T#?(-l) then T#(-l) = true;));
     cones := nonVanishingCohomology X;
     not any(keys T, l -> any(1..d, j -> any(cones#j, C -> (
		 P := (transpose C#1) * (transpose matrix{l} - C#0);
		 all( first entries transpose P, i -> i <= 0))))))
--checks that each key is not contained in any non vanishing cohomology 
--cones by computing the dot product of the key with each outer pointing 
--normal to each cone and showing that it is less than or equal to zero
     
doHigherSelfExtsVanish (Quiver,ZZ) := (Q,n) -> (     
--input is a quiver and the maximal chosen tensor power of the 
--anticanonical bundle
     L := apply(#Q_0, i -> Q#i.degree);
     X := variety Q;
     d := dim X;
     w := anticanDiv X;  
-- the anticanonical divisor
     T := new MutableHashTable;
     scan(0..n, i -> (scan(L, l -> T#(l+(i*w)) = true)));       
--adds a power of w to each line bundle
     scan(0..n, i -> (scan(subsets(#Q_0,2), p -> (
	       l := L#(p#0) - L#(p#1);                   
--adds a power of w to each line bundle. The keys of T are the line 
--bundles 
       if not T#?(l +(i*w)) then T#(l +(i*w)) = true;
       if not T#?(-l +(i*w)) then T#(-l +(i*w)) = true;))));
     cones := nonVanishingCohomology X;
     not any(keys T, l -> any(1..d, j -> any(cones#j, C -> (
		 P := (transpose C#1) * (transpose matrix{l} - C#0);
		 all( first entries transpose P, i -> i <= 0))))))
--checks that each key is not contained in any non vanishing cohomology 
--cones

doHigherSelfExtsVanish (Quiver,List) := (Q,K) -> (          
    --input is a quiver and a decreasing list of divisorial contractions
     L := apply(#Q_0, i -> Q#i.degree);
     d := dim Q.variety;
     T := new MutableHashTable;
     --the keys are L1 - L2 for L1, L2 in L
     scan(L, l -> T#l = true);
     scan(subsets(#Q_0,2), p -> (
	       l := L#(p#0) - L#(p#1);
	       if not T#?l then T#l = true;
	       if not T#?(-l) then T#(-l) = true;));
     cones := pullbackCones (d,K);                                 
     not any(keys T, l -> any(keys cones, j -> any(cones#j, C -> (
		 P := (transpose C#1) * (transpose matrix{l} - C#0);
		 all( first entries transpose P, i -> i <= 0))))))
--checks that each key is not contained in any non vanishing cohomology 
--cones
     
doHigherSelfExtsVanish (Quiver,List,ZZ) := (Q,K,nn) -> (          
--input is a quiver, a decreasing list of divisorial contractions
--and the maximal chosen tensor power of the anticanonical bundle
     L := apply(#Q_0, i -> Q#i.degree);
     d := dim Q.variety;
     w := anticanDiv Q.variety;  
-- the anticanonical divisor
     T := new MutableHashTable;
     scan(0..nn, i -> (scan(L, l -> T#(l+(i*w)) = true)));       
--adds a power of w to each line bundle
     scan(0..nn, i -> (scan(subsets(#Q_0,2), p -> (
	       l := L#(p#0) - L#(p#1);                   
--adds a power of w to each line bundle. The keys of T are the line 
--bundles 
	       if not T#?(l +(i*w)) then T#(l +(i*w)) = true;
	       if not T#?(-l +(i*w)) then T#(-l +(i*w)) = true;))));
     cones := pullbackCones (d,K);                                 
     not any(keys T, l -> any(keys cones, j -> any(cones#j, C -> (
		 P := (transpose C#1) * (transpose matrix{l} - C#0);
		 all( first entries transpose P, i -> i <= 0))))))
--checks that each key is not contained in any non vanishing cohomology 
--cones     
     
------------------------------------------------
-- bundlesNefCheck
-- Given an normal toric variety, a normalised list of elements L in Cl(X)
-- and a tensor power nn for the anticanonical bundle w^(-1), the function
-- computes L_i tensor L_j tensor w^(-nn) for all i and j and checks if the
-- corresponding divisors are nef
------------------------------------------------

bundlesNefCheck = method();
bundlesNefCheck (NormalToricVariety,List,ZZ) := (X,L,nn) -> (
--X - normal toric variety; L - list of entries in Cl X containing {0,..,0}
--nn - natural number, the tensor power of the anticanonical bundle
     w := anticanDiv X;                    
     C := transpose (fourierMotzkin(transpose nef X))#0;
--the rows of this matrix are the outward pointing normals of the nef cone
     T := new MutableHashTable;
     --keys of T will be L#i + L^(-1)#j + nn*w, for i != j  
     scan(L, i -> T#(i + nn*w) = true);
     --includes the trivial sheaf, as L is assumed to be normalised.      
     scan(subsets(L,2), i -> (
	       l := i#0 - i#1;
	       if not T#?(l + nn*w) then T#(l + nn*w) = true;
	       if not T#?(-l + nn*w) then T#(-l + nn*w) = true;));  
--adds the nth power of the anticanonical bundle to the difference of two
--line bundles
     all(keys T, i -> (
	       v := C*(transpose matrix {i});
	       all(first entries transpose v, j -> j <= 0))));  
--checks if the dot product of the vector with each of the outward pointing
--normals is less than or equal to zero, i.e. if the vector is in the nef
--cone

bundlesNefCheck (Quiver,ZZ) := (Q,nn) -> (
--Q - quiver; nn - natural number, the tensor power of the anticanonical 
--bundle
     X := Q.variety;
     L := apply(#Q_0, i -> Q#i.degree);
--rebuilds the list used to define the quiver 
     w := anticanDiv X;                    
     C := transpose (fourierMotzkin(transpose nef X))#0; 
--the rows of this matrix are the outward pointing normals of the nef cone 
     T := new MutableHashTable;
--keys of T will be L#i + L^(-1)#j + nn*w, for i != j              
     scan(L, i -> T#(i + nn*w) = true);
--includes the trivial sheaf, as L is assumed to be normalised.	         
     scan(subsets(L,2), i -> (
	       l := i#0 - i#1;
	       if not T#?(l + nn*w) then T#(l + nn*w) = true;
	       if not T#?(-l + nn*w) then T#(-l + nn*w) = true;));  
--adds the nth power of the anticanonical bundle to the difference of two
--line bundles
     all(keys T, i -> (
	       v := C*(transpose matrix {i});
	       all(first entries transpose v, j -> j <= 0)))); 
--checks if the dot product of the vector with each of the outward pointing
--normals is less than or equal to zero, i.e. if the vector is in the nef
--cone

------------------------------------------------
-- quiverToResMap
-- Given a quiver formed from a collection of line bundles {L_1,...,L_k} on
-- a toric variety X, the function produces the final map in T \boxtensor T
-- dual, where T is the direct sum of the L_i
------------------------------------------------
     
quiverToResMap = method(TypicalValue => Matrix)     
quiverToResMap  Quiver := Q -> (
 X := Q.variety;
 x := symbol x;
 w := symbol w;
 SS := QQ[x_1..x_(#rays X), w_1..w_(#rays X), 
	Degrees =>
	join(apply(degs X, i -> (
	      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
	      i|zerolist)),
             apply(degs X, i -> (
	      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
	      zerolist|i)))];
    --creates the ring of the product XxX
 m := mutableMatrix(SS,#Q_0,#Q_1);
 scan(Q_1, i -> (
    arrLabel := sort apply(indices label i, j -> (
	    j+1,(exponents label i)#0#j));
    m_(i.source,(i.index)-1) = -product(arrLabel, (j,k) -> (w_j)^k);
    m_(i.target,(i.index)-1) = product(arrLabel, (j,k) -> (x_j)^k)));
    matrix m);     
    --the tail of the arrow gives a negative entry in variables w_i
    --the head of the arrow gives a positive entry in variables x_i

------------------------------------------------
-- primitiveRelations
-- Given a toric Fano smooth variety, the function returns its
-- primitive relations from a database
------------------------------------------------

primitiveRelations = method(TypicalValue => List)
primitiveRelations (ZZ,ZZ) := (d,n) -> (
    if d < 1 or n < 0 then (
	error "-- expected positive dimension or nonnegative index")
    else if d === 1 and n > 0 then (
    	error "-- there is only one smooth Fano toric curve")
    else if d === 2 and n > 4 then (
    	error "-- there are only five smooth Fano toric surfaces")
    else if d === 3 and n > 17 then (
    	error "-- there are only 18 smooth Fano toric 3-folds")
    else if d === 4 and n > 123 then (
    	error "-- there are only 124 smooth Fano toric 4-folds")
    else if d > 4 then (
    error "-- database doesn't include full strong exceptional collections 
    --for varieties with dimension > 4")
    else resOfDiagData#(d,n)#0);

------------------------------------------------
-- fullStrExcColl
-- Given a toric Fano smooth variety, the function returns a
-- full strong exceptional collection for it from a database
------------------------------------------------

fullStrExcColl = method(TypicalValue => List)
fullStrExcColl (ZZ,ZZ) := (d,n) -> (
    if d < 1 or n < 0 then (
	error "-- expected positive dimension or nonnegative index")
    else if d === 1 and n > 0 then (
    	error "-- there is only one smooth Fano toric curve")
    else if d === 2 and n > 4 then (
    	error "-- there are only five smooth Fano toric surfaces")
    else if d === 3 and n > 17 then (
    	error "-- there are only 18 smooth Fano toric 3-folds")
    else if d === 4 and n > 123 then (
    	error "-- there are only 124 smooth Fano toric 4-folds")
    else if d > 4 then (
    error "-- database doesn't include full strong exceptional collections 
    --for varieties with dimension > 4")
    else resOfDiagData#(d,n)#1);



------------------------------------------------
-- resOfDiag
-- Given a toric Fano smooth variety X, the function returns a
-- chain complex which encodes the resolution of the diagonal
-- of XxX by a full strong exceptional collection box tensor
-- its dual. The resolution is constructed from a database
------------------------------------------------

resOfDiag = method()
resOfDiag (ZZ,ZZ) :=  memoize ((d,n) -> (
	--input is the dimension and index of the toric Fano smooth variety
    if d < 1 or n < 0 then (
	error "-- expected positive dimension or nonnegative index")
    else if d === 1 and n > 0 then (
    	error "-- there is only one smooth Fano toric curve")
    else if d === 2 and n > 4 then (
    	error "-- there are only five smooth Fano toric surfaces")
    else if d === 3 and n > 17 then (
    	error "-- there are only 18 smooth Fano toric 3-folds")
    else if d === 4 and n > 123 then (
    	error "-- there are only 124 smooth Fano toric 4-folds")
    else if d > 4 then (
    error "-- database doesn't include full strong exceptional collections
    --for varieties with dimension > 4")
    else if #resOfDiagData#(d,n) === 2 then(
	error "-- resolution not contained in database")
    else (
	X := smoothFanoToricVariety(d,n);
	L := fullStrExcColl (d,n);
	x := getSymbol "x";
	w := getSymbol "w";
	SS := QQ[x_1..x_(#rays X), w_1..w_(#rays X), 
	    Degrees =>
	    join(apply(degs X, i -> (
	      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
	      i|zerolist)),
      apply(degs X, i -> (
	      zerolist:= toList apply(1..#((degs X)#0), j -> 0);
	      zerolist|i)))];
--creates the ring of XxX
    	data := drop(resOfDiagData#(d,n),2);
	matrices := apply(floor((#data)/2), i -> (
		matrix(SS, value data#i)));
--creates the matrices in the resolution from the database
    	     maps := apply(#matrices, i -> (
		map(SS^(data#(floor(#data/2) + i)),
		    SS^(data#(floor(#data/2) + 1 + i)),
		    matrices#i)));
--creates the homogeneous maps for the chain complex from the database
	C := chainComplex maps;
	irr := getSymbol "irr";
	complexMaps := getSymbol "complexMaps";
	C.cache#irr = irrel X;
	C.cache.fullStrExcColl = L;
	C.cache#complexMaps = matrices;
	C.cache.degrees = drop(data, floor((#data)/2));
	C)));  


     
--**********************************************
-- DOCUMENTATION --
--**********************************************

beginDocumentation()

document { 
	Key => QuiversToricVarieties,
	Headline => "a package to construct a quiver of sections
	for a normal toric variety",
	PARA{
	     "Given a collection of line bundles on a complete normal 
	toric variety ", TEX "$X$", " with a torsion-free class group, 
	the package ", TO QuiversToricVarieties, " enables the user
        to construct and manipulate the quiver of sections ", TEX "$Q$", 
	". It can determine whether the collection of line bundles is
	strong exceptional and contains a database of full strong 
	exceptional collections of line bundles on smooth toric Fano 
	varieties in dimension ", TEX "$1 \\leq \\ n \\leq  \\ 4$", "."
	},
	SUBSECTION "Contributors",
	UL {
        {HREF("http://www.mast.queensu.ca/~ggsmith","Gregory G. Smith")}}
    }

------------------------------------------------
-- quiver
------------------------------------------------

document { 
     Key => Quiver,
     Headline => "the class of all quivers of sections", 
     } 
 
 document { 
     Key => QuiverArrow,
     Headline => "the class of all arrows in a quiver of sections", 
     SeeAlso => {
    (label,QuiverArrow),
    (source,QuiverArrow),
    (target,QuiverArrow),
    (index,QuiverArrow)}}  

document { 
     Key => {quiver, (quiver,List,List,NormalToricVariety), 
	 (quiver,List,NormalToricVariety)},
     Headline => "creates a quiver of sections",
     Usage => "quiver(L,X)",
     Inputs => {	 
	  "L" => List => {"of lattice points in the class group lattice 
	      for ", TEX "$X$", ", each corresponding to a line bundle"},
	  "X" => NormalToricVariety},
     Outputs => {Quiver},
     "A quiver of sections associated to a list of line bundles on a toric
     variety ", TEX "$X$", " is a quiver in which the vertices ", 
     TEX "$\\{ \\ 0,\\ \\ldots,\\ r \\rbrace$", " correspond to
     the line bundles and the arrows from ", TEX "$i$", " to ", TEX "$j$", 
     " correspond to indecomposable torus-invariant
     sections in ",TEX "$H^0(X, L_i \\otimes \\  L_j^{-1})$", 
     ".  We identify
     these sections with appropriate monomials in the Cox homogeneous
     coordinate ring.", 
     PARA{},
     "Given a list of line bundles ", TEX "$L$", " on a complete normal 
     toric variety ",TEX "$X$", " with a torsion-free class group, ", 
     TO "quiver", " constructs the associated
     complete quiver of sections --- every indecomposable
     torus-invariant section of ", TEX "$H^0(X, L_i \\otimes \\  
     L_j^{-1})$", " appears as an arrow. The quotient of the path 
     algebra of the quiver by an ideal of relations is then isomorphic 
     to the endomorphism algebra of ", 
     TEX "$\\oplus^r_{i=0} L_i$" , ".",
     PARA{},
     "The first example illustrates a complete quiver of sections on
     the first Hirzebruch surface.",     
     EXAMPLE {
	  "FF1 = hirzebruchSurface(1);",
	  "Q = quiver({{0,0},{1,0},{0,1}},FF1)",
	  "Q_0",
	  "Q_1",
	  "variety Q",	  
	  "Q#0#1,Q#0#2,Q#1#2",
          },
     PARA{},
     "The last output shows that this quiver has two arrows going from
     vertex ", TEX "$0$", " to vertex ", TEX "$1$", ", one from vertex ", 
     TEX "$0$", " to vertex ", TEX "$2$", " and one from vertex ", 
     TEX "$1$", " to vertex ", TEX "$2$", ".",
     PARA{},     
     "The second example illustrates a complete quiver of sections on
     the second Hirzebruch surface.",
     EXAMPLE {
	  "FF2 = hirzebruchSurface(2);",
	  "Q = quiver({{0,0},{1,0},{0,1},{1,1}},FF2);",
	  "Q_0",
	  "Q_1",     
	  "variety Q",
	  "Q#0#1, Q#0#2, Q#1#2, Q#1#3, Q#2#3",
          },     
     PARA{},
     "One can also create a quiver of sections by explicitly listing
     all the arrows.",
     EXAMPLE {
	  "S = ring FF2;",
	  "Q = quiver({{0,0},{1,0},{0,1},{1,1}}, {{(0,1),{x_1}},
	  {(0,2),{x_4}},
	  {(2,3),{x_1}},{(1,3),{x_4}}}, FF2)",
	  "Q_0",
	  "Q_1",
	  "Q#0#1, Q#0#2, Q#1#3, Q#2#3",
	  },     
     SeeAlso => {normalToricVariety, hirzebruchSurface}
     }  

document {
  Key => {(symbol _, Quiver, ZZ)},
  Headline => "lists the vertices and arrows of a quiver",
  Usage => "Q_i",
  Inputs => {
    "Q" => Quiver,
    "i" => ZZ},
  Outputs => {List => {"the vertices of the quiver when ", TEX "$i = 0$",
                       " and the arrows of the quiver when ", TEX "$i = 1$"
		       }
		   },
  "A quiver is determined by its vertices and its arrows between those
  vertices. For example, 
  take the Beilinson quiver of sections on ", TEX "$\\mathbb{P}^2$",  
  " which has three vertices corresponding to three line bundles, and six 
  arrows corresponding to torus-invariant irreducible sections.",
  PARA{},  
  EXAMPLE {
	  "X = projectiveSpace 2;",
	  "L = {{0},{1},{2}};",
	  "Q = quiver(L,X);",
	  "Q_0",
	  "Q_1",
	  },
  PARA{},
  "We can determine which vertices the arrows go between, as well as
  their labels.",
  EXAMPLE {
	  "a = Q_1#4",
	  "source a",
	  "target a",
	  "label a",
	  "index a",
	  },
  PARA{},      
  "To see which line bundle a vertex ", TEX "$i$", " of the quiver 
  corresponds to, we can use ", TEX "$Q#i$",
  EXAMPLE {
	  "Q#0",
	  "Q#1",
	  "Q#2",
	  },
  SeeAlso => {quiver}
  }              

undocumented {(net,Quiver),(net,QuiverArrow)}
----------------------------------------------------------------------
-- Lattice Maps induced By T-Invariant Maximal Birational Contractions
----------------------------------------------------------------------

document { 
     Key => {tCharacterMap, (tCharacterMap,ZZ,List)},
     Headline => "provides the map between the character lattices of two 
     toric Fano varieties induced by torus-invariant divisorial 
     contractions",
     Usage => "tCharacterMap(d,L)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano varieties"},	  
	  "L" => List => {"enumerating the varieties in a chain of 
	      torus-invariant divisorial contractions"}
	  },
     Outputs => {Matrix},
     "A morphism between two toric varieties induces a map between their
     corresponding character lattices. When defining a toric variety in ",
     TT "Macaulay2", ", a basis for the character lattice is chosen. ", 
     TO "tCharacterMap", " accesses a database of matrices - each matrix
     give an isomorphism between the character lattices ", TEX "$M_1 
     \\rightarrow M_2$", " induced by a torus-invariant divisorial 
     contraction ", TEX "$X_1 \\rightarrow X_2$", " between two ", 
     TEX "$d$", "-dimensional smooth 
     toric Fano varieties, ", TEX "$ \\ 2 \\leq \\ d \\leq \\ 4$", ". A 
     diagram of the contractions for the smooth toric Fano threefolds can
     be found in ", TT "[T. Oda, Convex bodies and algebraic geometry. An 
     introduction to the theory of toric varieties. page 91]", " and Sato 
     has listed the contractions for the smooth toric Fano fourfolds in ", 
     HREF "http://arxiv.org/abs/math/9911022", " (see also Remark 2.4 
     in ", HREF "http://arxiv.org/abs/1501.05871", ").",
     PARA{},
      
     EXAMPLE {
	  "contractionList 2",
	  "tCharacterMap(2,{2,0})",
	  "tCharacterMap(2,{3,2})",
	  },
     PARA{},     
     "We can input a list that corresponds to a chain of torus-invariant
     divisorial contractions between smooth toric Fano varieties.",
     EXAMPLE {
	  "tCharacterMap(2,{4,3,2,0})",
	  },     
     SeeAlso => {smoothFanoToricVariety, contractionList, tDivisorMap, 
	 picardMap}
     }  

document { 
     Key => {tDivisorMap, (tDivisorMap,ZZ,List)},
     Headline => "provides the map between the divisor 
     lattices of two toric Fano varieties induced by torus-invariant 
     divisorial contractions",
     Usage => "tDivisorMap(d,L)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano varieties"},	  
	  "L" => List => {"enumerating the varieties in a chain of 
	      torus-invariant divisorial contractions"}
	  },
     Outputs => {Matrix},
     "This function accesses 
     a database of matrices. Each matrix gives a map between the 
     torus-invariant divisor lattices ", TEX "$\\mathbb{Z}^d \\rightarrow 
     \\mathbb{Z}^{d-1}$", " induced by a torus-invariant divisorial 
     contraction ", 
     TEX "$X_1 \\rightarrow X_2$"," between two ", TEX "$d$", "-dimensional
     smooth toric Fano varieties, ", TEX "$ \\ 2 \\leq \\ d \\leq \\ 4$",
     ". A diagram of the 
     contractions for the smooth toric Fano threefolds can be found in ", 
     TT "[T. Oda, Convex bodies and algebraic geometry. An 
     introduction to the theory of toric varieties. page 91]", " and Sato 
     has listed the contractions for the smooth toric Fano fourfolds in ", 
     HREF "http://arxiv.org/abs/math/9911022", " (see also Remark 2.4 
     in ", HREF "http://arxiv.org/abs/1501.05871", ").",
     PARA{}, 
      
     EXAMPLE {
	  "contractionList 2",
	  "tDivisorMap(2,{2,0})",
	  "tDivisorMap(2,{3,2})",
	  },
     PARA{},     
     "We can input a list that corresponds to a chain of torus-invariant
     divisorial contractions between smooth toric Fano varieties.",
     EXAMPLE {
	  "tDivisorMap(2,{4,3,2,0})",
	  },     
     SeeAlso => {smoothFanoToricVariety, contractionList, tCharacterMap, 
	 picardMap}
     }  

document { 
     Key => {picardMap, (picardMap,ZZ,List)},
     Headline => "provides the map between the Picard lattices 
     of two toric Fano varieties induced by torus-invariant divisorial 
     contractions",
     Usage => "picardMap(d,L)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano varieties"},	  
	  "L" => List => {"enumerating the varieties in a chain of 
	      torus-invariant divisorial contractions"}
	  },
     Outputs => {Matrix},
     "A smooth complete toric variety determines the exact sequence of 
     lattices ", TEX "$0 \\rightarrow \\ M \\rightarrow \\ \\mathbb{Z}^d 
     \\rightarrow \\ $",
     "Pic", TEX "$(X) \\rightarrow \\ 0$", " where ", TEX "$M$", " is the 
     character
     lattice, ", TEX "$\\mathbb{Z}^d$", " is the torus-invariant divisor 
     lattice and Pic", TEX "$(X)$", " is the Picard lattice. For a  
     torus-invariant divisorial contraction ", TEX "$X_1 \\rightarrow 
     \\ X_2$", " between two ", TEX "$d$", "-dimensional smooth toric 
     Fano varieties, ", 
     TEX "$2 \\leq \\ d \\leq \\ 4$",", we have Pic", TEX "$(X_1) 
     \\cong$", "Pic", TEX "$(X_2) \\oplus \\mathbb{Z}$", ", where ", 
     TEX "$\\mathbb{Z}$", " is generated by the class ", TEX "$[E]$",
     " of the exceptional divisor ", TEX "$E$", ". A basis for ",
     TEX "$X_1$", " and ", TEX "$X_2$", " is fixed by ", 
     TO "smoothFanoToricVariety", ". The function ", 
     TO "picardMap", " returns the matrix from a database that gives
     the projection map Pic", TEX "(X_1) \\rightarrow", "Pic", 
     TEX "$(X_2)$", ", sending ", TEX "$[E]$", " to ", TEX "$[0]$", 
     ". A diagram of the contractions for the smooth toric Fano 
     threefolds can be found in ", 
     TT "[T. Oda, Convex bodies and algebraic geometry. An 
     introduction to the theory of toric varieties. page 91]", 
     " and Sato has listed the contractions for the smooth toric Fano
     fourfolds in ", HREF "http://arxiv.org/abs/math/9911022", 
     " (see also Remark 2.4 in ", 
     HREF "http://arxiv.org/abs/1501.05871", ").",
     PARA{}, 
      
     EXAMPLE {
	  "contractionList 2",
	  "picardMap(2,{2,0})",
	  "picardMap(2,{3,2})",
	  },
     PARA{},     
     "We can input a list that corresponds to a chain of torus-invariant
     divisorial contractions between smooth toric Fano varieties.",
     EXAMPLE {
	  "picardMap(2,{4,3,2,0})",
	  },
     PARA{},
     "The map makes a commutative square with ", 
     TO "tDivisorMap", ".",
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "Y = smoothFanoToricVariety(2,0);",
	  "picardMap(2,{2,0})*fromCDivToPic(X) ==
	   fromCDivToPic(Y)*tDivisorMap(2,{2,0})",
	  },      
     SeeAlso => {smoothFanoToricVariety, contractionList, tCharacterMap, 
	 tDivisorMap}
     }  

document { 
     Key => {contractionList, (contractionList,ZZ)},
     Headline => "lists the pairs of toric Fano varieties that 
     have a torus-invariant divisorial contraction between them",
     Usage => "contractionList(d)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano varieties"}
	      },
     Outputs => {List},
     "This function accesses a database that contains pairs of numbers for
     which there is a torus-invariant divisorial contraction between the 
     corresponding smooth toric Fano varieties of dimension ", 
     TEX "$d, \\ 2 \\leq \\ d \\leq \\ 4$", ". A diagram of the 
     contractions for the smooth toric Fano threefolds can be found in ", 
     TT "[T. Oda, Convex bodies and algebraic geometry. An 
     introduction to the theory of toric varieties. page 91]",  " and Sato
     has listed the contractions for the smooth toric Fano fourfolds in ", 
     HREF "http://arxiv.org/abs/math/9911022", " (see also Remark 2.4 
     in ", HREF "http://arxiv.org/abs/1501.05871", ").",
     PARA{}, 
      
     EXAMPLE {
	  "contractionList 2",
	  },
     SeeAlso => {smoothFanoToricVariety, picardMap, tCharacterMap, 
	 tDivisorMap}
     }

document { 
     Key => {toricFanoContractions, (toricFanoContractions,ZZ,ZZ)},
     Headline => "lists the toric Fano varieties that can be 
     obtained by torus-invariant divisorial contractions from a 
     given toric Fano variety",
     Usage => "toricFanoContractions(n,i)",
     Inputs => {	 
	  "n" => ZZ => {"determining the dimension of 
	      the smooth toric Fano varieties"},
	  "i" => ZZ => {"the ", TEX "$i^{th}$", " toric Fano variety of
	      dimension ", TEX "$n$"}
	      },
     Outputs => {List},
     "This function has as an input a dimension ", 
     TEX "$n, \\ 2 \\leq \\ d \\leq \\ 4$", " and an index ", TEX "$i$",
     " that labels a smooth toric Fano variety ", TEX "$X$", 
     " of dimension ", TEX "$n$", ". The function then produces a list
     of lists. Each list contain a list of numbers that index smooth 
     toric Fano varieties of dimension ", TEX "$n$", " such that there
     is a chain of torus-invariant divisorial contractions 
     from ", TEX "$X$", " to each of these varieties in turn. A diagram 
     of the 
     contractions for the smooth toric Fano threefolds can be found in ", 
     TT "[T. Oda, Convex bodies and algebraic geometry. An 
     introduction to the theory of toric varieties. page 91]",  " and Sato
     has listed the contractions for the smooth toric Fano fourfolds in ", 
     HREF "http://arxiv.org/abs/math/9911022", " (see also Remark 2.4 
     in ", HREF "http://arxiv.org/abs/1501.05871", ").",
     PARA{}, 
     "For example, let ", TEX "$X = X_4$", " be the blowup 
     of ", TEX "$\\mathbb{P}^2$", " in three points, the birationally 
     maximal smooth toric Fano surface. Then we have two chains 
     of divisorial contractions, ", TEX "$X_4 \\rightarrow X_3 
     \\rightarrow X_1 $", " and ", TEX "$X_4 \\rightarrow X_3 
     \\rightarrow X_2 \\rightarrow X_0$",  ", where all 
     the ", TEX "$X_i$", " are smooth toric Fano surfaces.",
     PARA{},  
     EXAMPLE {
	  "toricFanoContractions(2,4)",
	  },
     PARA{},
     "There are no divisorial contractions from ", TEX "$\\mathbb
     {P}^2$", " to any other smooth toric Fano surface - it is 
     birationally minimal.",
     PARA{},
     EXAMPLE {
         "toricFanoContractions(2,0)",
         },
 
     SeeAlso => {smoothFanoToricVariety, contractionList, 
         picardMap, tCharacterMap, tDivisorMap}
     }


----------------------------------------------------------------------
-- blowUpCone and exceptionalDivisor
----------------------------------------------------------------------

document { 
     Key => {blowUpCone, (blowUpCone,ZZ,List)},
     Headline => "provides the cone corresponding to the subvariety that
     has been blown up",
     Usage => "blowUpCone(d,L)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the toric Fano varieties"},	  
	  "L" => List => {"enumerating the varieties in the blow up of
	      a torus-invariant subvariety "}
	  },
     Outputs => {List},
     "Codimension ", TEX "$k$", " torus-invariant subvarieties of a toric 
     variety ", TEX "$X$", " correspond to ", TEX "$k$", "-dimensional 
     cones in the fan for ", TEX "$X$", ". A blow up of one of these 
     subvarieties corresponds to the star subdivision of the cone by a 
     new ", TEX "$1$", "-dimensional cone which labels the exceptional 
     divisor. If ", TEX "$X$", " and ", TEX "$Y$", " are two smooth toric 
     Fano varieties of dimension ", TEX "$d, \\ 2
     \\leq \\ d \\leq \\ 4$", ", then the command ", 
     TO "contractionList", " tells us if ", TEX "$X$", " is a blow up 
     of a torus-invariant subvariety in ", TEX "$Y$", ". If this is the 
     case, then the command ", TO "blowUpCone", " accesses a database 
     containing the primitive lattice points of the rays of the cone 
     involved in the blow up.", 
     PARA{},
     "For example, the blow up of a torus-invariant point on the smooth
     toric Fano surface numbered ", TEX "$0$", " is the smooth toric
     Fano surface numbered ", TEX "$2$", " in the database accessed 
     by ", TO "smoothFanoToricVariety", ".",   
     EXAMPLE {
	  "member({2,0}, contractionList(2))",
	  "blowUpCone(2,{2,0})",
	  },
     PARA{},     
     "The primitive lattice points are given in the basis determined
     by ", TO "smoothFanoToricVariety", " for ", TEX "$X.$",
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "Y = smoothFanoToricVariety(2,0);",
	  "rays X",
	  "rays Y",
	  },     
     SeeAlso => {smoothFanoToricVariety, contractionList, 
	 exceptionalDivisor, tCharacterMap, blowup}
     }  
 
document { 
     Key => {exceptionalDivisor, (exceptionalDivisor,ZZ,List)},
     Headline => "provides the ray corresponding to the exceptional divisor
     in the toric Fano blow ups",
     Usage => "exceptionalDivisor(d,L)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the toric Fano varieties"},	  
	  "L" => List => {"enumerating the varieties in the blow up of
	      a torus-invariant subvariety "}
	  },
     Outputs => {List},
     "Codimension ", TEX "$k$", " torus-invariant subvarieties of a toric 
     variety ", TEX "$X$", " correspond to ", TEX "$k$", "-dimensional 
     cones in the fan for ", TEX "$X$", ". A blow up of one of these 
     subvarieties corresponds to the star subdivision of the cone by a 
     new ", TEX "$1$", "-dimensional cone which labels the exceptional 
     divisor. If ", TEX "$X$", " and ", TEX "$Y$", " are two smooth toric 
     Fano varieties of dimension ", TEX "$d, \\ 2
     \\leq \\ d \\leq \\ 4$", ", then the command ", 
     TO "contractionList", " tells us if ", TEX "$X$", " is a blow up 
     of a torus-invariant subvariety in ", TEX "$Y$", ". If this is the 
     case, then the command ", 
     TO "exceptionalDivisor", " accesses a database containing the 
     primitive lattice point of the ray labelling the exceptional divisor
     in this blow up.", 
     PARA{},
     "For example, the blow up of a torus-invariant point on the smooth
     toric Fano surface numbered ", TEX "$0$", " is the smooth toric
     Fano surface numbered ", TEX "$2$", " in the database accessed 
     by ", TO "smoothFanoToricVariety", ".",  
     EXAMPLE {
	  "member({2,0}, contractionList(2))",
	  "exceptionalDivisor(2,{2,0})",
	  },
     PARA{},     
     "Note that sum of the primitive lattice points of the cone that was
     star subdivided is equal to the primitive lattice point for the 
     exceptional divisor.",
     EXAMPLE {
	  "sum blowUpCone(2,{2,0}) == exceptionalDivisor(2,{2,0})",
	  },     
     SeeAlso => {smoothFanoToricVariety, contractionList, 
	 blowUpCone, tCharacterMap, blowup}
     }  

----------------------------------------------------------------------
-- primitiveRelations
----------------------------------------------------------------------

document { 
     Key => {primitiveRelations, (primitiveRelations,ZZ,ZZ)},
     Headline => "provides the primitive relations for a smooth toric Fano
          variety",
     Usage => "primitiveRelations(n,k)",
     Inputs => {	 
	  "n" => ZZ => {"determining the dimension of 
	      the toric Fano variety"},	  
	  "k" => ZZ => {"the ", TEX "$k^{th}$", " toric Fano variety of
	      dimension ", TEX "$n$"}
	  },
     Outputs => {List},
     "Let ", TEX "$X$", " be a complete normal toric variety. A subset of 
     the primitive generators of the rays in the fan for ", TEX "$X$", " is
     a primitive collection if it does not form a cone in the
     fan, but any proper subset of the collection does form a cone. The sum
     of the lattice points in a primitive collection is a 
     lattice point in a cone ", TEX "$\\sigma$", " and so can be
     written uniquely as a linear combination of the generators of the
     rays of ", TEX "$\\sigma$", ". A primitive relation records the 
     relation between the primitive collection and the lattice point it 
     defines.   
     The primitive relations uniquely determine the toric variety; if for
     two toric varieties we have a bijection between the rays of their
     fans, then the bijection induces an isomorphism on the primitive 
     relations if and only if the two varieties are isomorphic.",  
     PARA{},
     TO "primitiveRelations", " recalls from a database the primitive 
     relations for a smooth toric Fano variety of dimension ", 
     TEX "$1 \\leq \\ n \\leq \\ 4$.",
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "R = rays X",
	  "(primitiveRelations(2,2))#0",
	  "- R#0 + R#1 - R#2",
	  "member({0,2}, max X)",
	  "(primitiveRelations(2,2))#1",
	  "- R#1 - R#3",
	  "member({1,3}, max X)", 
	  },
     
     SeeAlso => {smoothFanoToricVariety, (max,NormalToricVariety),
	(rays,NormalToricVariety) }
     }
 
----------------------------------------------------------------------
-- variety,source,target,label,index
----------------------------------------------------------------------

document { 
     Key => {(variety,Quiver)},
     Headline => "returns the toric variety used to define the quiver",
     Usage => "variety(Q)",
     Inputs => {	 
	  "Q" => Quiver
	  },
     Outputs => {NormalToricVariety},
     "A complete normal toric variety ", TEX "$X$", " with a torsion-free
     class group  and a list of 
     line bundles on ", TEX "$X$", " defines a ", TO "quiver", " of
     sections ", TEX "$Q$", ". The function ", TO "variety", " recalls the 
     toric variety defining ", TEX "$Q$.",
     PARA{},
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,X);",
	  "Y = variety Q;",
	  "X === Y", 
	  },
     
     SeeAlso => {smoothFanoToricVariety, quiver}
     }

document { 
     Key => {(source,QuiverArrow)},
     Headline => "determines the source of an arrow in a quiver",
     Usage => "source(a)",
     Inputs => {	 
	  "a" => QuiverArrow
	  },
     Outputs => {ZZ  => {"labelling the quiver vertex that is the source
	 of the arrow"},
	 },
     "A ", TO "quiver", " is determined by a list of vertices and a list
     of arrows between the vertices. This function displays the vertex at
     the source (or the tail) of an arrow in a quiver.",
     PARA{},
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,X);",
	  "Q_1",
	  "a1 = oo#0",
	  "source(a1)",
	  "label(a1)",
	  "Q#0",
	  "a4 = Q_1#3",
	  "source(a4)",
	  "label(a4)",
	  "Q#1", 
	  },
     
     SeeAlso => {quiver, QuiverArrow, (label,QuiverArrow), 
	 (target,QuiverArrow),(index,QuiverArrow)}
     }
 
 document { 
     Key => {(target,QuiverArrow)},
     Headline => "determines the target of an arrow in a quiver",
     Usage => "target(a)",
     Inputs => {	 
	  "a" => QuiverArrow
	  },
     Outputs => {ZZ  => {"labelling the quiver vertex that is the target
	 of the arrow"},
	 },
     "A ", TO "quiver", " is determined by a list of vertices and a list
     of arrows between the vertices. This function displays the vertex at
     the target (or the head) of an arrow in a quiver.",
     PARA{},
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,X);",
	  "Q_1",
	  "a1 = oo#0",
	  "target(a1)",
	  "label(a1)",
	  "Q#0",
	  "a4 = Q_1#3",
	  "target(a4)",
	  "label(a4)",
	  "Q#1", 
	  },
     
     SeeAlso => {quiver, QuiverArrow, (label,QuiverArrow), 
	 (source,QuiverArrow),(index,QuiverArrow)}
     }

document { 
     Key => {label, (label,QuiverArrow)},
     Headline => "determines the label of an arrow in a quiver",
     Usage => "label(a)",
     Inputs => {	 
	  "a" => QuiverArrow
	  },
     Outputs => {RingElement},
     "A complete normal toric variety ", TEX "$X$", " with a torsion-free
     class group and a list of 
     line bundles on ", TEX "$X$", " defines a ", TO "quiver", " of
     sections ", TEX "$Q$", ". The arrows between the vertices are given by
     torus-invariant irreducible maps between the line bundles and are
     labelled by appropriate monomials in the Cox homogeneous 
     coordinate ring. The function ", TO "label", " displays this label 
     for a given arrow in the quiver.",
     PARA{},
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,X);",
	  "Q_1",
	  "a1 = oo#0",
	  "label(a1)",
	  "Q#0",
	  "a4 = Q_1#3",
	  "label(a4)",
	  "Q#1", 
	  },
     
     SeeAlso => {quiver, QuiverArrow, (target,QuiverArrow), 
	 (source,QuiverArrow),(index,QuiverArrow)}
     }     

document { 
     Key => {(index,QuiverArrow)},
     Headline => "displays the index of an arrow in a quiver",
     Usage => "index(a)",
     Inputs => {	 
	  "a" => QuiverArrow
	  },
     Outputs => {ZZ},
     "The function displays the index of an arrow in a quiver.",
     PARA{},
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,X);",
	  "Q_1",
	  "a1 = oo#0",
	  "index(a1)",
	  "a4 = Q_1#3",
	  "index(a4)", 
	  },
     
     SeeAlso => {quiver, QuiverArrow, (target,QuiverArrow), 
	 (source,QuiverArrow),(label,QuiverArrow)}
     }
 
----------------------------------------------------------------------
-- fullStrExcColl
----------------------------------------------------------------------

document { 
     Key => {fullStrExcColl, (fullStrExcColl,ZZ,ZZ)},
     Headline => "recalls from a database a full strong exceptional 
     collection of line bundles for a toric Fano variety",
     Usage => "fullStrExcColl(d,k)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano variety"},	  
	  "k" => ZZ => {"corresponding to the smooth toric Fano variety"}
	  },
     Outputs => {List},
     TT "Macaulay2", " contains a database of smooth toric Fano varieties
     up to dimension 6. Up to dimension 4, these varieties have full strong
     exceptional collections of line bundles. ", TO "fullStrExcColl",
     " recalls from a database a full strong exceptional collection of 
     line bundles for each of these varieties. The collections can be found
     in ", HREF "http://www.maths.bath.ac.uk/~masadk/papers/tilt.pdf",
     " for the surfaces, ", HREF "http://arxiv.org/abs/1012.4086", " for
     the threefolds and ", HREF "http://arxiv.org/abs/1501.05871",
     " for the fourfolds.",
     PARA{}, 
      
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,4);",
	  "L = fullStrExcColl(2,4)",
	  },
     PARA{},     
     "We can construct the quiver of sections for the collection and 
     confirm that it is strong exceptional.",
     EXAMPLE {
	  "Q = quiver(L,X);",
	  "doHigherSelfExtsVanish Q",
	  },
     PARA{},
     "This collection can be used to give a resolution of the structure
     sheaf of the diagonal embedding into ", TEX "$X \\times \\ X$", ", 
     which implies that the collection is full.",
     EXAMPLE {
	  "C = resOfDiag(2,4);",
	  "SS = ring C;",
	  "C",
	  },
            
     SeeAlso => {smoothFanoToricVariety, quiver, doHigherSelfExtsVanish, 
	 resOfDiag}
     }  

----------------------------------------------------------------------
-- resOfDiag
----------------------------------------------------------------------

document { 
     Key => {resOfDiag, (resOfDiag,ZZ,ZZ)},
     Headline => "recalls from a database a resolution of the diagonal
     by a full strong exceptional collection of line bundles",
     Usage => "resOfDiag(d,k)",
     Inputs => {	 
	  "d" => ZZ => {"determining the dimension of 
	      the smooth toric Fano variety"},	  
	  "k" => ZZ => {"corresponding to the smooth toric Fano variety"}
	  },
     Outputs => {ChainComplex},
     
     "Let ", TEX "$X$", " be a smooth variety with a strong exceptional
     collection of line bundles ", TEX "$L$", ". If ", TEX "$L$", " can
     be used to give a resolution of the structure sheaf of the diagonal
     embedding in ", TEX "$X \\times \\ X$", ", then ", TEX "$L$", " is 
     full. For certain smooth toric Fano varieties of dimension ", 
     TEX "$d, \\ 1 \\leq d \\leq 4$", ", with a strong exceptional
     collection of line bundles given by ", TO "fullStrExcColl", ", the
     function ", TO "resOfDiag", " retrieves from a database the 
     resolution of the structure sheaf of the diagonal embedding. The 
     resolution is presented as a chain complex of modules over the Cox
     homogeneous coordinate ring for ", TEX "$X \\times \\ X$", ".", 
     PARA{},   
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,4);",
	  "L = fullStrExcColl(2,4);",
	  "Q = quiver(L,X);",
	  "C = resOfDiag(2,4);",
	  "SS = ring C;",
	  "C",
	  },
     PARA{},     
     "The basis elements ", TEX "$x_i$", " in the Cox homogeneous 
     coordinate ring for ", TEX "$X \\times \\ X$", " are the basis
     elements for the first copy of ", TEX "$X$", ", whilst the basis
     elements ", TEX "$w_i$", " are used for the second copy of ", 
     TEX "$X$", ". The final map in the chain complex is
     determined by the ", TO "source", ", the ", TO "target", " and 
     the ", TO "label", " of the arrows in the quiver of sections
     defined by the collection of line bundles, and can be computed 
     using ", TO "quiverToResMap", ". The rows of the 
     matrix correspond to the vertices of the quiver and the columns of
     the matrix correspond to the arrows.",
     
     EXAMPLE {
	  "finalMap = C.cache.complexMaps#0;",
	  "a0 = Q_1#0;",
	  "finalMap_0",
	  "source a0",
	  "target a0",
	  "label a0",
	  },
     EXAMPLE {
	 "a7 = Q_1#7;",
	 "finalMap_7",
	 "source a7",
	 "target a7",
	 "label a7",
	 },	   
                 
     SeeAlso => {fullStrExcColl, (label,QuiverArrow), (source,QuiverArrow),
	 (target,QuiverArrow), quiver, quiverToResMap}
     }  


----------------------------------------------------------------------
-- doHigherSelfExtsVanish
----------------------------------------------------------------------

document { 
     Key => {doHigherSelfExtsVanish, (doHigherSelfExtsVanish,Quiver),
	 (doHigherSelfExtsVanish,Quiver,List),
	 (doHigherSelfExtsVanish,Quiver,ZZ),
	 (doHigherSelfExtsVanish,Quiver,List,ZZ)},
     Headline => "checks whether a list of line bundles on a toric variety
     is strong exceptional",
     Usage => "doHigherSelfExtsVanish(Q,K,n)",
     Inputs => {	 
	  "Q" => Quiver => {"determined by the collection of line bundles
	      "},	  
	  "K" => List => {"corresponding to a chain of divisorial
	      contractions between toric Fano varieties (optional)"},
	  "n" => ZZ => {"the maximal tensor power of the anticanonical 
	      bundle (optional)"},   
	  },
     Outputs => {Boolean},
     
     "The input for this function is a complete quiver of sections 
     defined by a list of line bundles ", 
     TEX "$\\lbrace \\ L_0 , L_1 , \\ldots \\ , L_m
     \\rbrace$", " containing the structure sheaf on a complete normal 
     toric variety ", TEX "$X$", " with a torsion-free class group.
     To check that the collection of line bundles 
     is strong exceptional, it is enough to check that ", 
     TEX "$H^i (L_j \\otimes \\ L_k^{-1}) = 0$", " for ", TEX "$i > 0$", 
     ". This function implements the 
     construction by Eisenbud, Mustata and Stillman (see ", 
     HREF "http://arxiv.org/abs/math/0001159", ") to
     determine if the higher cohomology of these line bundles vanish, by
     creating cones in the vector space Cl", 
     TEX "$(X) \\otimes \\mathbb{R}$",
     " and checking that the line bundle avoids these cones. 
     These cones are called the non-vanishing cohomology
     cones and are determined by certain subsets of the
     rays of the fan for ", TEX"$X$", ", given by ", 
     TO "forbiddenSets", ".",
     PARA{},
     "The first example is of a collection of line bundles on the first
     Hirzebruch surface.",
	   
     EXAMPLE {
	  "FF1 = hirzebruchSurface(1);",
	  "L = {{0,0},{1,0},{0,1}};",
	  "Q = quiver(L,FF1);",
	  "doHigherSelfExtsVanish Q",
	   },
     PARA{},
     "The cones in Cl", TEX "$(X) \\otimes \\mathbb{R}$", " are generated 
     by ", TO "doHigherSelfExtsVanish", " and 
     then stored in the variety's cache table. Each non-vanishing 
     cohomology cone is given by a vector and a matrix ",
     TEX "$\\{\\mathbf{w},M\\}$", " encoding the supporting closed half 
     spaces of the cone, in which case the cone is ", TEX "$\\{ \\
     \\mathbf{v} \\in \\ Cl (X) \\otimes \\mathbb{R} \\ | \\ M 
     \\mathbf{v} \\leq \\ \\mathbf{w} \\}$", ".    
     Note that when checking if the collection is strong exceptional,
     the function ignores the ", TEX "$H^0$", " cone.",
     EXAMPLE {
	  "FF1.cache.cones",
	   },
     PARA{},
     "Let ", TEX "$X_t \\rightarrow X_{t-1} \\rightarrow \\ldots 
     \\rightarrow X_0$", " be a chain of torus-invariant divisorial
     contractions between smooth toric Fano varieties of dimension ",
     TEX "$d, 2 \\leq d \\leq 4$", ". We can check that a 
     given collection of line bundles on the maximal variety ", TEX "$X_t$"
     , " is strong exceptional and that the distinct line bundles in its 
     image under the Picard lattice maps ", TO "picardMap",
     " is strong exceptional on the contractions. We achieve this by 
     including as an additional input a list of decreasing integers that
     index the smooth toric Fano varieties via ", 
     TO "smoothFanoToricVariety", ".",
     PARA{},
     "In the example below, the maximal smooth toric Fano surface is the
     blow up of ", TEX "$\\mathbb{P}^2$", " in three points. The list of 
     line bundles  was shown to be strong exceptional by King (see ", 
     HREF "http://www.maths.bath.ac.uk/~masadk/papers/tilt.pdf", ").",
     
     EXAMPLE {
	  "contractionList 2",
	  "X = smoothFanoToricVariety(2,4);",
	  "K = {4,3,2,0};",
	  "L = {{0,0,0,0},{0,0,1,1},{0,1,0,0},{0,1,1,0},{1,0,0,0},
	       {1,0,0,1}};",
	  "Q = quiver(L,X);",
	  "doHigherSelfExtsVanish (Q,K)",
	  },
     PARA{},
     "The calculation below confirms that the image of the line bundles
     is strong exceptional on the blow up of ", TEX "$\\mathbb{P}^2$",
     " in two points, which is the 3rd smooth toric Fano surface.",
     
     EXAMPLE {
	 "Y = smoothFanoToricVariety(2,3);",
	 "Ly = unique entries ((matrix L)*(transpose picardMap(2,{4,3})))",
	 "Qy = quiver(Ly,Y);",
	 "doHigherSelfExtsVanish Qy",
	 },	   
     PARA{},
     "Let ", TEX "$X$", " be a smooth toric Fano variety with a full strong
     exceptional collection of line bundles and ", TEX "$Y$", " be the
     total space of the canonical bundle ", TEX "$\\omega_X$", ". To 
     determine if the pullback of these line bundles via ", TEX "$\\pi
     : Y \\rightarrow X$", " gives a tilting bundle on ", TEX "$Y$", ", it 
     is enough to check that ", 
     TEX "$\\oplus_{l \\geq 0} H^i (X, \\ L_j \\otimes \\ L_k^{-1} 
     \\otimes \\ \\omega_X^{-l}) = 0$", " for ", 
     TEX "$i > 0$", " and all ", TEX "$j,\\ k$", ". As ", 
     TEX "$\\omega_X^{-1}$", " is ample, there is some positive integer ",
     TEX "$N$", " such that for all ", TEX "$l \\geq \\ N$", " we have ",
     TEX "$H^i (L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega_X^{-l}) = 0, 
     \\ i > 0$", ". The value of ", TEX "$N$", " can be found using ",
     TO "bundlesNefCheck", ". By using the additional input ", 
     TEX "$N-1$", ", we can then use ", TO "doHigherSelfExtsVanish",
     " to determine if ", 
     TEX "$\\oplus_{0 \\leq \\ l <  N} 
     H^i (L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega_X^{-l}) = 0$.",
     
     EXAMPLE {
	  "bundlesNefCheck(Q,2)",
	  "doHigherSelfExtsVanish(Q,1)",
	  },
     PARA{}, 
     "We can now use the list of integers indexing the divisorial 
     contractions from before together with ", TEX "$N-1$", " as 
     additional inputs for ", TO "doHigherSelfExtsVanish", ". This checks 
     that ", TEX "$\\oplus_{0 \\leq \\ l <  N} 
     H^i (X_t, \\ L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega^{-l}) 
     = 0$.", " for each contraction ", TEX "$X_t$", ".", 
     
     EXAMPLE {
	  "doHigherSelfExtsVanish (Q,K,1)",
	  },  
                    
     SeeAlso => {fullStrExcColl, contractionList, quiver, bundlesNefCheck}
     }  



----------------------------------------------------------------------
-- bundlesNefCheck
----------------------------------------------------------------------

document { 
     Key => {bundlesNefCheck, 
	 (bundlesNefCheck,NormalToricVariety, List, ZZ),
	 (bundlesNefCheck,Quiver,ZZ)},
     Headline => "checks whether the cohomology of a list of line bundles
     tensored with powers of the anticanonical bundle vanishes",
     Usage => "bundlesNefCheck(X,L,n)",
     Inputs => {	 
	  "X" => NormalToricVariety , 
	  "L" => List => {"denoting line bundles on ", TEX "$X$"},
	  "n" => ZZ => {"the maximum tensor power of the anticanonical 
	      bundle"},   
	  },
     Outputs => {Boolean},
     
     "Let ", TEX "$\\lbrace \\ L_0 , L_1 , \\ldots \\ , L_m \\rbrace$",
     " be a full strong exceptional collection of line bundles containing 
     the structure sheaf on a smooth toric Fano variety ", TEX"$X$", ". To 
     check if this
     collection determines a tilting bundle on the total space of the 
     canonical bundle ", TEX "$\\omega_X$",
     ", we need to show that ", TEX "$H^i (L_j \\otimes \\ L_k^{-1} 
     \\otimes \\ \\omega_X^{-l}) = 0$", " for ", TEX "$i > 0, \\ l \\geq \\
     0$", " and all ", TEX "$j, \\ k$", ". As ", 
     TEX "$\\omega_X^{-1}$", " is ample, there is some positive integer ",
     TEX "$N$", " such that for all ", TEX "$l \\geq \\ N$", " we have 
     that ", TEX "$L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega_X^{-l}$", 
     " is nef, so ", 
     TEX "$H^i (L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega_X^{-l}) = 0$",
     " for ", TEX"$i > 0$", ". Given an exponent ", TEX "$n$", ", ", 
     TO "bundlesNefCheck", " determines if ", 
     TEX "$L_j \\otimes \\ L_k^{-1} \\otimes \\ \\omega_X^{-n}$", " is nef 
     for all ", TEX "$j, \\ k$.", 
     PARA{},	   
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,4);",
	  "L = fullStrExcColl(2,4);",
	  "bundlesNefCheck (X,L,1)",
	  },
     PARA{},
     "Alternatively we can use the quiver of sections defined by the
     line bundles on the toric variety as an input.",
     
     EXAMPLE {
	  "Q = quiver(L,X);",
	  "bundlesNefCheck(Q,1)",
	   },
     PARA{},
     "Given the full strong exceptional collections in the database
     accessed by ", TO "fullStrExcColl", ", the minimal exponent that can 
     be used for all smooth toric Fano surfaces is 1, for all smooth toric 
     Fano threefolds is 2 and for all smooth toric Fano fourfolds is 3.",
     
     EXAMPLE {
	 "all(0..4, i -> (
	 X = smoothFanoToricVariety(2,i);
	 L = fullStrExcColl(2,i);
	 bundlesNefCheck(X,L,1)))",
	 },
                         
     SeeAlso => {fullStrExcColl, quiver, 
	 (doHigherSelfExtsVanish,Quiver,ZZ)}
     }  


----------------------------------------------------------------------
-- forbiddenSets
----------------------------------------------------------------------

document { 
     Key => {forbiddenSets, (forbiddenSets, NormalToricVariety)},
     Headline => "computes the subsets of rays of a fan that determine
     non-vanishing cohomology cones",
     Usage => "forbiddenSets(X)",
     Inputs => {	 
	  "X" => NormalToricVariety  
	  },
     Outputs => {MutableHashTable},
     
     "Let ", TEX "$X$", " be a complete normal toric variety with a 
     torsion-free class group, and Cl", TEX "$(X) \\otimes \\mathbb{R}$",
     " be the vector space containing the class group lattice. We can use 
     the construction by Eisenbud, Mustata and Stillman (see ", 
     HREF "http://arxiv.org/abs/math/0001159", 
     ") to create cones in Cl", TEX "$(X) \\otimes 
     \\mathbb{R}$", " such that if a lattice point
     lies in one of the cones, its corresponding sheaf has non-vanishing 
     cohomology in a specified degree. The cones are determined by certain 
     subsets of rays of the fan associated to ", TEX "$X$", " and are 
     computed by ", TO "forbiddenSets", ". Let ", TEX "$deg$",
     " be the map from the lattice of Weil divisors to the 
     class group, given by ", TO "fromWDivToCl", ". Each ray ", 
     TEX "$\\rho$", " in the fan labels a divisor ",
     TEX "$D_\\rho$", ". For a subset of the rays ", TEX "$\\lbrace \\ 
     \\rho_i  \\rbrace , \\ i \\in \\ I$", ", with compliment ",
     TEX "$\\lbrace \\ \\rho_j  \\rbrace , \\ j \\in \\ J$", 
     ", the associated cone in Cl", TEX "$(X) \\otimes \\mathbb{R}$", 
     " is given by positive linear combinations of the vectors ", 
     TEX "$deg (\\ -D_{\\rho_i} \\ )$", 
     " and ", TEX "$deg (\\ D_{\\rho_j} \\ )$", ", based at the cone 
     apex ", TEX "$- \\sum_i deg ( \\ x_{\\rho_i} \\ )$.",
     PARA{},
     
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,2);",
	  "C = forbiddenSets X;",
	  "peek C",
	  },       
     PARA{},
     "The non-vanishing cohomology cones are computed when using ",
     TO "doHigherSelfExtsVanish", " and stored in the cache table for ",
     TEX "$X$", ". Each cone is given by a vector and a matrix ",
     TEX "$\\{\\mathbf{w},M\\}$", " encoding the supporting closed half 
     spaces of the cone, in which case the cone is ", TEX "$\\{ \\
     \\mathbf{v} \\in \\ Cl(X) \\otimes \\mathbb{R} \\ | \\ M 
     \\mathbf{v} \\leq \\ \\mathbf{w} \\}$", ".    
     Note that the ", TEX "$H^0$", " cone is computed but 
     not included in the ", TO "forbiddenSets", " output.",   
     	   
     EXAMPLE {
	  "L = {{0,0},{1,0}};",
	  "doHigherSelfExtsVanish( quiver(L,X) );",
	  "peek X.cache.cones",
	  "fromWDivToCl X",
	  },
     PARA{},
                              
     SeeAlso => {quiver, (doHigherSelfExtsVanish,Quiver)}
     }  


----------------------------------------------------------------------
-- quiverToResMap
----------------------------------------------------------------------

document { 
     Key => {quiverToResMap, (quiverToResMap, Quiver)},
     Headline => "computes the map of Cox ring modules determined by
                  a quiver of sections",
     Usage => "quiverToResMap Q",
     Inputs => {	 
	  "Q" => Quiver  
	  },
     Outputs => {Matrix},
     
     "Let ", TEX "$X$", " be a complete normal toric variety with a 
     torsion-free class group and a collection of line bundles ", 
     TEX "$\\{ L_0 = O_X , L_1 , \\ldots , L_m \\}$", ". Define ",
     TEX "$p_1 , p_2 : X \\times \\ X \\rightarrow X$", " to be the 
     projections onto the first and second component respectively. The 
     associated quiver of sections encodes an algebra ", TEX"$A$", " by 
     taking the quotient of the path algebra of the quiver by an ideal of
     relations determined by the labels on the arrows. 
     We can use the combinatorics of the quiver to calculate the last part 
     of the minimal projective resolution of ",
     TEX"$A$", " by ", TEX"$A,A$", "-bimodules (see [Prop. 5.1], ",
     HREF "http://www.maths.bath.ac.uk/~masadk/papers/tilt.pdf", "). The 
     final map in this resolution can then be used to define a map ",
     TEX "$f : \\oplus_{a \\in Q_1} p_1^* (L_{ta}) \\otimes p_2^* 
     (L_{ha}^{-1}) \\rightarrow \\oplus_{i \\in Q_0} p_1^* (L_{i}) \\otimes
     p_2^* (L_i^{-1})$",
     ", where the summands are considered as modules over the Cox 
     homogeneous coordinate ring for ", TEX "$X \\times \\ X$", ". The 
     method ",
     TO "quiverToResMap", " calculates this map of modules. The basis 
     elements ", TEX "$x_i$", " in the Cox homogeneous 
     coordinate ring for ", TEX "$X \\times \\ X$", " are the basis
     elements for the first copy of ", TEX "$X$", ", whilst the basis
     elements ", TEX "$w_i$", " are used for the second copy of ", 
     TEX "$X$", ".",
     PARA{},
     
     EXAMPLE {
	  "X = smoothFanoToricVariety(2,4);",
	  "L = fullStrExcColl(2,4);",
	  "Q = quiver(L,X);",
	  "quiverToResMap Q",
	  },       
     PARA{},
     "The function ", TO "resOfDiag", " recalls from a database a chain 
     complex of modules for certain smooth toric Fano varieties with a full
     strong exceptional collection of line bundles. We see that ",
     TO "quiverToResMap", " calculates the final map in this chain 
     complex.",   
     PARA{},	   
     EXAMPLE {
	  "C = resOfDiag(2,4);",
	  "SS = ring C;",
	  "C",
	  "C.cache.complexMaps#0",
	  },
     PARA{},
                              
     SeeAlso => {quiver, resOfDiag, fullStrExcColl}
     }  

--*************************************************************************
-- TESTS --
--*************************************************************************

-- REFERENCES

-- [Ki97] King, A., "Tilting Bundles on Some Rational Surfaces". Preprint. 
-- [EMS00] Eisenbud,D.; Mustaţǎ,M.; Stillman, M.; "Cohomology on toric 
-- varieties and local cohomology with monomial supports". Symbolic 
-- computation in algebra, analysis, and geometry (Berkeley, CA, 1998).
-- J. Symbolic Comput. 29 (2000), no. 4-5, 583–600. 
-- [Ue14] Uehara, H., "Exceptional collections on toric Fano threefolds 
-- Internat. J. Math. 25 (2014), no. 7, 1450072, 32 pp.
   
--------------------------------------------------------------
-- Test 0: Test for contractionList, blowupCone, tCharacterMap
--------------------------------------------------------------

TEST ///
assert (
all(2..4, t -> (
     all(contractionList(t), x -> (
     	X := smoothFanoToricVariety(t,x#0);
     	Y := smoothFanoToricVariety(t,x#1);
     	A := tCharacterMap(t,x);
     	C := blowUpCone(t,x);
     	CinY := entries ((matrix C)*(inverse A));
     	CinYRay := apply(CinY, i -> position(rays Y, j -> j == i));
     	Z := blowup(CinYRay,Y);
     	rayPerm := apply(entries ((matrix rays Z)*A), i -> 
	    position(rays X, j -> j == i));
     	maxZ := apply(max Z, i -> (
     		apply(i, j -> rayPerm#j)));
     	sort max X == sort apply(maxZ, i -> sort i) and
     	sort rays X ==
     	sort entries ((matrix rays Z)*A)
     	))
     )) == true)
///,

-- For smooth toric Fano varieties of dimension 2..4, we have a list
-- of divisorial contractions between them. This test checks that the
-- contraction of the divisor determined by the "blowupCone" function
-- is a contraction between two toric Fano varieties. The test uses the
-- "blowup" function from the "NormalToricVarieties" package to blow up the
-- toric Fano variety according to the cone specified by "blowupCone",
-- and then checks that the resulting variety is equal to the toric Fano
-- determined by "contractionList" by comparing the rays and cones
-- of the two fans. In the process, the "tCharacterMap" is checked to be
-- correct.

--------------------------------------------------------------
-- Test 1: Test for tDivisorMap, picardMap  
--------------------------------------------------------------

TEST ///
assert (
all(2..4, t -> (
all(contractionList(t), x -> (
	X := smoothFanoToricVariety(t,x#0);
	Y := smoothFanoToricVariety(t,x#1);
	(matrix rays Y)*tCharacterMap(t,x) ==
	tDivisorMap(t,x)*(matrix rays X) and
	(fromWDivToCl Y)*tDivisorMap(t,x) ==
	picardMap(t,x)*(fromWDivToCl X))) == true
)))
///,

-- confirms that the maps between the exact sequences of two Fano toric 
-- varieties involved in a divisorial contraction commute, for dimensions
-- 2,3,4. 

--------------------------------------------------------------
-- Test 2: Test for exceptionalDivisor  
--------------------------------------------------------------

TEST ///
assert (
all(2..4, t -> (
all(contractionList(t), x -> (
	X := smoothFanoToricVariety(t,x#0);
	Y := smoothFanoToricVariety(t,x#1);
	EDinY := (entries ((matrix {exceptionalDivisor(t,x)}) * (
		    inverse tCharacterMap(t,x))))#0;
--the exceptional divisor in the coordinates for the fan of Y
	BUCinY := entries ((matrix blowUpCone(t,x)) * (
		inverse tCharacterMap(t,x)));
--the blow up cone in the coordinates for the fan of Y
	pBUCinY := sort apply(BUCinY, i -> position(rays Y, j -> j == i));
--the position of the rays for the blow up cone in the sequence of rays for
--the fan of Y
	sum blowUpCone(t,x) == exceptionalDivisor(t,x) and
	member(exceptionalDivisor(t,x), rays X) and
	not member(EDinY, rays Y) and
	any(max Y, i -> isSubset(pBUCinY,i)))) == true
)))
///,

-- checks "exceptionalDivisor" in a contraction between two toric Fano
-- varieties is correct by showing that it is the sum of the blow up
-- cone, checking that the vector defines a ray for the blow up X but 
-- not for the contraction Y, and checking that the list given by 
-- blowUpCone is a cone on the Y

--------------------------------------------------------------
-- Test 2: Test for quiver  
--------------------------------------------------------------

TEST ///
X = smoothFanoToricVariety(2,2);
L = {{0,0},{1,0},{0,1},{1,1}};
Q = quiver(L,X);
SS = ring Q#0#1#0;
Q1 = quiver({{0,0},{1,0},{0,1},{1,1}}, {{(0,1),{x_0_SS,x_2_SS}},
		{(0,2),{x_3_SS}},
		{(1,2),{x_1_SS}},
		{(1,3),{x_3_SS}},
                {(2,3),{x_0_SS,x_2_SS}}}, X);
assert (all(Q_0, i -> Q#i === Q1#i) and
        all(Q1_0, i -> Q1#i === Q#i) == true)	
///,

-- checks that the quiver Q given by the collection of line bundles chosen
-- on the variety above and constructed by "quiver" is equal to Q1, the 
-- (opposite of the) quiver constructed in [Ki97] for the variety.

--------------------------------------------------------------
-- Test 3: Test for doHigherSelfExtsVanish  
--------------------------------------------------------------

TEST ///
X = smoothFanoToricVariety(2,4);
L = {{0,0,0,0},{0,0,1,1},{0,1,0,0},{0,1,1,0},{1,0,0,0},{1,0,0,1}};
Q = quiver(L,X);
assert (doHigherSelfExtsVanish Q == true)
///,
-- The collection above was shown in [Ki97] to be strong exceptional
-- on the maximal toric Fano surface.

TEST ///
X = smoothFanoToricVariety(2,4);
L = {{0,0,0,0},{0,0,1,1},{0,1,0,0},{0,1,1,0},{1,0,0,0},{1,0,0,1}};
Q = quiver(L,X);
K = {4,3,2,0};
assert (doHigherSelfExtsVanish (Q,K) == true)
///,

-- The collection above was shown by [Ue10] to be strong exceptional
-- on the chosen maximal variety, as well as all the toric Fano 
-- contractions listed in K. 

TEST ///
X = smoothFanoToricVariety(3,17);
L = {{0,0,0,0,0},{0,0,0,1,0},{0,0,1,0,0},{0,0,1,1,0},{1,1,0,0,0},
    {1,1,0,1,0},{0,1,0,0,1},{0,1,0,1,1},{0,0,0,0,1},{0,0,0,1,1},
    {1,0,1,0,0},{1,0,1,1,0}};
Q = quiver(L,X);
assert (doHigherSelfExtsVanish Q == true)
///,

-- The collection above was shown by [Ue10] to be strong exceptional
-- on the chosen maximal toric Fano variety

TEST ///
X = smoothFanoToricVariety(3,17);
L = {{0,0,0,0,0},{0,0,0,1,0},{0,0,1,0,0},{0,0,1,1,0},{1,1,0,0,0},
    {1,1,0,1,0},{0,1,0,0,1},{0,1,0,1,1},{0,0,0,0,1},{0,0,0,1,1},
    {1,0,1,0,0},{1,0,1,1,0}};
Q = quiver(L,X);
K = {17,13,6,2,0}
assert (doHigherSelfExtsVanish Q == true)
///,

-- The collection above was shown by [Ue10] to be strong exceptional
-- on the chosen maximal variety, as well as all the toric Fano 
-- contractions listed in K. 

--------------------------------------------------------------
-- Test 4: Test for forbiddenSets
--------------------------------------------------------------

TEST ///
X = normalToricVariety({{1,0},{0,1},{-1,1},{0,-1}},{{0,1},{1,2},
	{2,3},{0,3}});
C = forbiddenSets X;
assert (((C#1 == {{0,2},{1,3}}) and
    C#2 == {{0,1,2,3}}) == true)
///,

-- Checks the forbidden sets on the toric variety defined are the same
-- as those given in (Ex 3.6) [EMS00]. Note we can also check that the
-- resulting cones in the Picard lattice are the same as in (ex 3.6).
 
--------------------------------------------------------------
-- Test 5: Test for quiverToResMap
--------------------------------------------------------------

TEST ///
X = projectiveSpace 2;
L = {{0},{1},{2}};
Q = quiver(L,X);
M1 = quiverToResMap Q;
T = generators ring M1;
M2 = matrix{{-(T#3), -(T#4), -(T#5), 0, 0, 0},
       {T#0, T#1, T#2, -(T#3), -(T#4), -(T#5)}, 
       {0, 0, 0, T#0, T#1, T#2}};
assert ((M1 == M2) == true)
///, 

-- Checks that the matrix created by "quiverToResMap" from the choice
-- of line bundles on the projective plane is equal to the (negative
-- of the) matrix given in (Ex 5.2) [Ki97].

end

restart
installPackage "QuiversToricVarieties"
check "QuiversToricVarieties"

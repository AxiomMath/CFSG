module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCertInputs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

@[expose] def k0P : List ℕ × List ℕ :=
  ([1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0,
     1, 0, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0,
     0, 0, 1, 1, 1, 0, 1])

@[expose] def x0P : List ℕ × List ℕ :=
  ([0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1,
     0, 1, 0, 1, 0, 1, 1],
    [1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1,
     0, 1, 0, 1, 1, 1, 1])

@[expose] def gkP : List (List ℕ × List ℕ) :=
  [([0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0,
     0, 1, 1, 0, 0, 1, 1],
    [0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0,
     1, 1, 0, 0, 0, 0, 0]),
   ([1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0,
     0, 1, 1, 0, 1, 1, 1],
    [1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0,
     1, 1, 0, 0, 1, 0, 0])]

@[expose] def gxP : List (List ℕ × List ℕ) :=
  [([0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0,
     1, 1, 1, 0, 0, 0, 0],
    [1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1,
     0, 1, 1, 0, 0, 1, 1]),
   ([1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1,
     0, 0, 0, 0, 0, 0, 1],
    [1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1,
     1, 0, 0, 0, 0, 0, 1])]

@[expose] def gnP : List (List ℕ × List ℕ) :=
  [([1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1,
     1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 1,
     1, 1, 1, 0, 0, 0, 0]),
   ([1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0,
     0, 0, 0, 1, 0, 1, 1],
    [1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1,
     0, 0, 1, 1, 0, 1, 0])]

abbrev k0C : List ℕ := k0P.1

abbrev x0C : List ℕ := x0P.1

@[expose] def kPows : List (List ℕ) :=
  [k0C, mul6 k0C k0C, mul6 k0C (mul6 k0C k0C), mul6 k0C (mul6 k0C (mul6 k0C k0C))]

@[expose] def normK (y : List ℕ) : Bool := kPows.any fun p => mul6 y k0C == mul6 p y

@[expose] def orbitK (_ : Unit := ()) : Array (List ℕ) :=
  orbitBuild6 k0C gpsH (orbitParents6 k0C gpsH 60000)

@[expose] def orbitX (_ : Unit := ()) : Array (List ℕ) :=
  orbitBuild6 x0C gpsH (orbitParents6 x0C gpsH 1000)

@[expose] def tabK (_ : Unit := ()) : Array (List ℕ) := closureT (gkP.map Prod.fst)

@[expose] def tabX (_ : Unit := ()) : Array (List ℕ) := closureT (gxP.map Prod.fst)

@[expose] def tabN (_ : Unit := ()) : Array (List ℕ) := closureT (gnP.map Prod.fst)

@[expose] def eltsOK : Bool :=
  genP.all pairCheck && pairCheck k0P && pairCheck x0P && gkP.all pairCheck && gxP.all pairCheck &&
    gnP.all pairCheck &&
    mul6 k0C (mul6 k0C (mul6 k0C (mul6 k0C k0C))) == one6 && !(k0C == one6) &&
    mul6 x0C (mul6 x0C x0C) == one6 && !(x0C == one6) && commutes6 x0C k0C &&
    gkP.all (fun p => commutes6 p.1 k0C) && gxP.all (fun p => commutes6 p.1 x0C)

@[expose] def tabsOK (oK oX tK tX tN : Array (List ℕ)) : Bool :=
  orbitOK oK 48384 && orbitOK oX 672 && closureOK (gkP.map Prod.fst) tK 30 &&
    closureOK (gxP.map Prod.fst) tX 2160 && closureOK (gnP.map Prod.fst) tN 60 &&
    allCheck (fun c => !(mul6 c (mul6 c c) == one6) || c == one6 || c == x0C ||
      c == mul6 x0C x0C) tK &&
    (let m := indexMap tN
     allCheck (fun y => !(normK y) || found tN m y) tX)

set_option compiler.extract_closed false in
@[noinline, expose] def sp62OK (_ : Unit := ()) : Bool :=
  eltsOK && tabsOK (orbitK ()) (orbitX ()) (tabK ()) (tabX ()) (tabN ())

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS228Sp62

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Tables

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def h1408Gens : List Table := (List.finRange 7).map fun j => h1408T j.val

@[expose] def tabW (w : List ℕ) : Table := wordTbl 1408 h1408Gens w

@[expose] def wordA : List ℕ := [4, 7, 4, 3, 7, 6, 2, 6, 7, 2, 7, 2, 3]

@[expose] def wordZ : List ℕ := [7, 3, 2, 3, 7, 3, 2, 3]

@[expose] def wordB : List ℕ := [7]

@[expose] def wordZ₁ : List ℕ := [7, 3, 6, 5, 4, 5, 6, 3, 1, 5]

@[expose] def wordAZ : List ℕ := wordA ++ wordZ

@[expose] def preservesHalves (T : Table) : Bool :=
  (List.range 704).all fun k => decide (ap T k < 704) && decide (704 ≤ ap T (704 + k))

@[expose] def swapsZero (T : Table) : Bool := decide (704 ≤ ap T 0)

@[expose] def twoHSBasicOK : Bool :=
  h1408Gens.all (fun g => permOK 1408 g && invOK 1408 g (invT 1408 g)) &&
    involOK 1408 (tabW wordA) && involOK 1408 (tabW wordZ) && involOK 1408 (tabW wordB) &&
    involOK 1408 (tabW wordZ₁) && h1408Gens.all (fun g => commTT 1408 (tabW wordA) g) &&
    preservesHalves (tabW wordA) && preservesHalves (tabW wordZ) &&
    preservesHalves (tabW wordAZ) && swapsZero (tabW wordB) && swapsZero (tabW wordZ₁)

end CFSG.EvenSporadicStandard.HNRecog

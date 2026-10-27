module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsSub
public meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsSub
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public meta import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public meta import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public meta import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public meta import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Blueprint.Chevalley Timmesfeld.Co1Leaf
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

@[expose] def e6InnerVec : Fin 5 → Fin Tag.E6.rank → ZMod 3 :=
  fun i j => (Tag.E6.cartan j ⟨i.val, by have := i.2; decide +revert⟩ : ZMod 3)

namespace Native

@[expose] def e6Om3 : List ℤ := [4, 3, 5, 6, 4, 2]

@[expose] def e6WeylTest (t : List (List ℤ)) : Bool :=
  (List.finRange Tag.E6.rank).all fun j =>
    (((List.finRange Tag.E6.rank).map fun i =>
      e6Om3.getD i.val 0 * (t.getD i.val []).getD j.val 0).sum - e6Om3.getD j.val 0) % 3 == 0

@[expose] def famOKW (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (kb : List (List ℕ)) : Bool :=
  let FR := fibRoots RN kb
  let T := (tuplesL B FR E (E.map (fibL kb)) NE).filter e6WeylTest
  match kerRootsL FR (kb.map fun _ => 0) with
  | [] => T.all (· == E)
  | [α, β] => β == α.map (- ·) && T.all fun t => t == E || t == E.map (reflB B α)
  | _ => false

@[expose] def famOK0W (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (kb : List (List ℕ)) : Bool :=
  let FR := fibRoots RN kb
  (kerRootsL FR (kb.map fun _ => 0)).isEmpty &&
    ((tuplesL B FR E (E.map (fibL kb)) NE).filter e6WeylTest).all (· == E)

@[noinline, expose] def e6FourCoreCheck (_ : Unit := ()) : Bool :=
  let B := gramL .E6
  let RN := rootsN .E6
  let E := simpleL .E6
  let NE := E.map fun e => formB B e e
  (normVecs 3 5).all (fun fl => famOKW B RN E NE ((kerBasis 3 fl).map (liftL e6InnerVec))) &&
    famOK0W B RN E NE ((stdBasis 5).map (liftL e6InnerVec)) &&
    famOK0 B RN E NE (stdBasis 6)

end Native

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end

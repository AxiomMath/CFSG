module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GraphOrbitDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactChevGraphOrbitSimple : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R P : Subgroup Y), IsSimpleGroup ↥L →
    IsChevTwo ↥L → R ≤ Subgroup.normalizer (L : Set Y) →
    IsPGroup 2 R → IsSylowTwoOf (R ⊓ L) L → IsMinOverBorel L (R ⊓ L) P →
    ¬ R ≤ Subgroup.normalizer (P : Set Y) →
      Group.IsSolvable ↥(pElementSubgroup 2 (conjClosure P R)) ∨
      (∃ C : Subgroup Y, C ≤ pElementSubgroup 2 C ∧ C ≤ pElementSubgroup 2 (conjClosure P R) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ Subgroup.normalizer (C : Set Y) ∧
        pElementSubgroup 2 (conjClosure P R) ≤ conjClosure C R ∧
        ∀ r ∈ R, r ∉ Subgroup.normalizer (P : Set Y) →
          ⁅C, B6.conjSub r C⁆ ≤ pCoreOf 2 (pElementSubgroup 2 (conjClosure P R))) ∨
      QuasisimpleModTwoNonab ↥(twoResidual (pElementSubgroup 2 (conjClosure P R)))

end CFSG.AGLEmbeddingD2.Tits.GN516

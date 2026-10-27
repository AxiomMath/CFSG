module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def CompTypesElem : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup (MulAut S),
      IsElemAbelian p E → ∀ K : Subgroup S, IsComponentOf K (I142.centFix E) →
        IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)

end CFSG.LocalAnalysis.GLTheoremA.I142T

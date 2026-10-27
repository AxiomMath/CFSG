module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def OddLieResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

theorem childOddLie_of_children (h2 : ChildSmallAltOdd) (h3 : ChildSmallAltEven)
    (hR : OddLieResidual) : ChildOddLie := by
  intro G _ _ L hS hlie
  by_cases h5 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5))
  · rcases Nat.even_or_odd (Nat.card (center L)) with hev | hodd
    · exact Or.inr (Or.inl (h3 G L hS ⟨5, le_rfl, by norm_num, h5⟩ hev))
    · exact h2 G L hS ⟨5, le_rfl, by norm_num, h5⟩ hodd
  by_cases h6 : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6))
  · rcases Nat.even_or_odd (Nat.card (center L)) with hev | hodd
    · exact Or.inr (Or.inl (h3 G L hS ⟨6, by norm_num, by norm_num, h6⟩ hev))
    · exact h2 G L hS ⟨6, by norm_num, by norm_num, h6⟩ hodd
  exact hR G L hS hlie h5 h6

end CFSG.OddStandard

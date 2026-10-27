module

public import CFSG.LocalAnalysis.EvenBN.Tits.Setting
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenBNRankTwoFrontier

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def TitsCenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), TitsSetting G L → False

@[expose] def TitsDataExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (d : Data G), d.Hyp → False

theorem titsCenterlessExclusion_of_data
    (h : TitsDataExclusion) : TitsCenterlessExclusion := by
  intro G _ _ L hL
  obtain ⟨d, -, hd⟩ := Data.exists_data hL
  exact h G d hd

theorem bnFamily_Tits_of_exclusion (h : TitsCenterlessExclusion) :
    ComponentInitial.EvenResidual.BNFamilyStatement fun X _ => LieModel X .Tits 0 2 1 := by
  intro G _ _ _ hnonab hK L hL hcore S hS _ _ hm
  have h2 := ComponentInitial.EvenResidual.isPGroup_two_center hL hcore
  by_contra hodd
  have hZ : center L = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rcases k with _ | k
    · exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
    · exact (hodd (by rw [hk]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)).elim
  let e : L ≃* L ⧸ center L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hmL : LieModel L .Tits 0 2 1 := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm
  exact h G L ⟨⟨inferInstance, hnonab, hK, hL, hcore, ⟨S, hS⟩⟩, hZ, hmL⟩

end CFSG.LocalAnalysis.EvenBN.Tits

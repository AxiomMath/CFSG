module

public import CFSG.LocalAnalysis.EvenBN.U4.RootD1

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem normalizer_B1_inf_C_le_normalizer_L (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (L : Set G) :=
  inf_le_right.trans hS.centralizer_le_normalizer

theorem normalizer_B1_inf_C_le_normalizer_A1 (hS : Setting h L η t Q T) :
    normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) ≤
      normalizer (miyamotoA1G h L η : Set G) :=
  inf_le_left.trans hS.normalizer_B1_le_normalizer_A1

theorem card_normalizer_B1_inf_C_inf_centralizer_dvd_two (hS : Setting h L η t Q T) :
    Nat.card (normalizer (miyamotoB1 h L η t : Set G) ⊓ centralizer ({t} : Set G) ⊓
      centralizer (L : Set G) : Subgroup G) ∣ 2 := by
  rw [← hS.card_kernel]
  exact card_dvd_of_le fun x hx => mem_inf.2 ⟨hx.2, hx.1.2⟩

theorem not_sq_dvd_card_normalizer_B1_inf_C (hS : Setting h L η t Q T) :
    ¬(2 ^ f + 1) ^ 2 ∣ Nat.card (normalizer (miyamotoB1 h L η t : Set G) ⊓
      centralizer ({t} : Set G) : Subgroup G) :=
  not_sq_dvd_card_of_le_normalizer_A1 h L η hS.normalizer_B1_inf_C_le_normalizer_L
    hS.normalizer_B1_inf_C_le_normalizer_A1 hS.card_normalizer_B1_inf_C_inf_centralizer_dvd_two

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

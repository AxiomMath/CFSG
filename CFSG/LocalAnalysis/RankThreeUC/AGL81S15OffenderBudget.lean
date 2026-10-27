module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem two_pow_mul_card_le [Finite G] [Finite V] {B : Subgroup G} {U : Submodule (ZMod 2) V}
    (h : IsBestOffenderOn ρ B U) {D : Subgroup G} (hD : D ≤ cenOn ρ B U) :
    2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) * Nat.card D ≤ Nat.card B := by
  have hoff := (IsBestOffenderOn.isOffenderOn h).2
  have hDc : Nat.card D ≤ Nat.card (cenOn ρ B U) := Subgroup.card_le_of_le hD
  have hfu : finrank (ZMod 2) (fixOn ρ B U) ≤ finrank (ZMod 2) U :=
    Submodule.finrank_mono fixOn_le_left
  rw [card_eq_two_pow_finrank, card_eq_two_pow_finrank] at hoff
  have h2 : 2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) *
      2 ^ finrank (ZMod 2) (fixOn ρ B U) = 2 ^ finrank (ZMod 2) U := by
    rw [← pow_add]
    congr 1
    omega
  have key : (2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) * Nat.card D) *
      2 ^ finrank (ZMod 2) (fixOn ρ B U) ≤
        Nat.card B * 2 ^ finrank (ZMod 2) (fixOn ρ B U) := by
    calc (2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) * Nat.card D) *
          2 ^ finrank (ZMod 2) (fixOn ρ B U)
        = (2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) *
            2 ^ finrank (ZMod 2) (fixOn ρ B U)) * Nat.card D := by ring
      _ = 2 ^ finrank (ZMod 2) U * Nat.card D := by rw [h2]
      _ ≤ 2 ^ finrank (ZMod 2) U * Nat.card (cenOn ρ B U) := Nat.mul_le_mul_left _ hDc
      _ ≤ Nat.card B * 2 ^ finrank (ZMod 2) (fixOn ρ B U) := hoff
  exact Nat.le_of_mul_le_mul_right key (by positivity)

theorem finrank_sub_le_log_card_range [Finite G] [Finite V] {B : Subgroup G}
    {U : Submodule (ZMod 2) V} (h : IsBestOffenderOn ρ B U) {H : Type*} [Group H]
    (φ : ↥B →* H) (hφ : ∀ b : ↥B, φ b = 1 → (b : G) ∈ cenOn ρ B U) :
    finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U) ≤ Nat.log 2 (Nat.card φ.range) := by
  have hD : φ.ker.map B.subtype ≤ cenOn ρ B U := by
    rintro _ ⟨b, hb, rfl⟩
    exact hφ b hb
  have h1 := two_pow_mul_card_le h hD
  have hc : Nat.card (φ.ker.map B.subtype) = Nat.card φ.ker :=
    Nat.card_congr (Subgroup.equivMapOfInjective φ.ker B.subtype B.subtype_injective).toEquiv.symm
  rw [hc] at h1
  have h2 := Subgroup.card_ker_mul_card_range φ
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h3 : Nat.card φ.ker * 2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixOn ρ B U)) ≤
      Nat.card φ.ker * Nat.card φ.range := by
    rw [h2, mul_comm]
    exact h1
  exact Nat.le_of_mul_le_mul_left h3 hpos

end CFSG.LocalAnalysis.RankThreeUC.S15

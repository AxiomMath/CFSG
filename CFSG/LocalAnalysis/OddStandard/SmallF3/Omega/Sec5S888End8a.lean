module

public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem oddCore_eq_of_quotient {P : Type} [Group P] [Finite P] (O : Subgroup P) [O.Normal]
    (hO : Odd (Nat.card O)) (h : CFSG.oddCore (P ⧸ O) = ⊥) : CFSG.oddCore P = O := by
  refine le_antisymm ?_ (CFSG.ABGLocalTools.le_oddCore_of_normal (inferInstance : O.Normal) hO)
  have hN : (CFSG.oddCore P).Normal := CFSG.oddCore_normal P
  have hmap_normal : ((CFSG.oddCore P).map (QuotientGroup.mk' O)).Normal :=
    hN.map (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective (N := O))
  have hmap_odd : Odd (Nat.card ((CFSG.oddCore P).map (QuotientGroup.mk' O))) :=
    (CFSG.ABGLocalTools.odd_card_oddCore (H := P)).of_dvd_nat
      (Subgroup.card_map_dvd (H := CFSG.oddCore P) (QuotientGroup.mk' O))
  have hle : (CFSG.oddCore P).map (QuotientGroup.mk' O) ≤ CFSG.oddCore (P ⧸ O) :=
    CFSG.ABGLocalTools.le_oddCore_of_normal hmap_normal hmap_odd
  have hbot : (CFSG.oddCore P).map (QuotientGroup.mk' O) = ⊥ := by
    rw [h] at hle
    exact le_bot_iff.mp hle
  have hker : CFSG.oddCore P ≤ (QuotientGroup.mk' O).ker :=
    (Subgroup.map_eq_bot_iff (H := CFSG.oddCore P) (f := QuotientGroup.mk' O)).mp hbot
  rwa [QuotientGroup.ker_mk'] at hker

private abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private theorem sl23_card : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem sl23_oddCore_cube (x : SL23) (hx : x ∈ CFSG.oddCore SL23) : x ^ 3 = 1 := by
  have hdiv : orderOf x ∣ Nat.card (CFSG.oddCore SL23) :=
    Subgroup.orderOf_dvd_natCard (CFSG.oddCore SL23) hx
  have hoddN : Odd (Nat.card (CFSG.oddCore SL23)) :=
    CFSG.ABGLocalTools.odd_card_oddCore
  have hdvd24 : Nat.card (CFSG.oddCore SL23) ∣ 24 := by
    rw [← sl23_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd3 : Nat.card (CFSG.oddCore SL23) ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card (CFSG.oddCore SL23)) (2 ^ 3) :=
      (Nat.coprime_pow_right_iff (n := 3) (by norm_num) _ 2).mpr
        (Nat.coprime_two_right.mpr hoddN)
    have h24 : (24 : ℕ) = 3 * 2 ^ 3 := by norm_num
    rw [h24] at hdvd24
    exact (hcop.dvd_mul_right).mp hdvd24
  exact orderOf_dvd_iff_pow_eq_one.mp (dvd_trans hdiv hdvd3)

theorem oddCore_sl23_eq_bot :
    CFSG.oddCore (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  have hx3 : x ^ 3 = 1 := sl23_oddCore_cube x hx
  obtain ⟨h, hh⟩ :=
    (by decide : ∀ g : SL23, g ^ 3 = 1 → g ≠ 1 →
      ∃ h : SL23, (g * (h * g * h⁻¹)) ^ 3 ≠ 1) x hx3 hxne
  have hy : x * (h * x * h⁻¹) ∈ CFSG.oddCore SL23 :=
    (CFSG.oddCore SL23).mul_mem hx ((CFSG.oddCore_normal SL23).conj_mem x hx h)
  exact hh (sl23_oddCore_cube (x * (h * x * h⁻¹)) hy)

end CFSG.OddStandard.SmallF3.Omega

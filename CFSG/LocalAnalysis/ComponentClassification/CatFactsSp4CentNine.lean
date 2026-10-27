module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4SwapCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
public import CFSG.GH74.Generic.Context
public import CFSG.GroupTheory.TwoCentralInvolutionConj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag
open Subgroup

variable {K : Type} [Field K]

theorem orderOf_u1 (h2 : (2 : K) ≠ 0) : orderOf (u1 K) = 2 := by
  have hn : (negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) * negOneSL = 1 :=
    Subtype.ext (by
      change (-1 : Matrix (Fin 2) (Fin 2) K) * -1 = 1
      simp)
  have hsq : u1 K ^ 2 = 1 := by
    rw [u1_eq_proj_blkSL, sq_proj_blkSL, Prod.mk_mul_mk, one_mul, hn]
    change proj 2 K (blkSL K (1 : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K)) = 1
    rw [map_one, map_one]
  exact orderOf_eq_prime hsq (u1_ne_one h2)

theorem twentyFour_dvd_mul_sq_sub_one {q : ℕ} (hq : Odd q) : 24 ∣ q * (q ^ 2 - 1) := by
  have h8 : 8 ∣ q * (q ^ 2 - 1) :=
    Dvd.dvd.mul_left (Nat.eight_dvd_sq_sub_one_of_odd hq) q
  have h3 : 3 ∣ q * (q ^ 2 - 1) := by
    have h : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h with h | h | h
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
    · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
      have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
    · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
      have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
      omega
  have hcop : Nat.Coprime 8 3 := by norm_num
  simpa using hcop.mul_dvd_of_dvd_of_dvd h8 h3

private theorem card_SL2_eq [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem nine_dvd_and_sixtyFour_dvd_card_centralizer_u1 [Finite K] (hodd : Odd (Nat.card K)) :
    9 ∣ Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) ∧
      64 ∣ Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have h24 : 24 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [card_SL2_eq]
    exact twentyFour_dvd_mul_sq_sub_one hodd
  have h576 : 576 ∣ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) ^ 2 := by
    have h : (24 : ℕ) ^ 2 = 576 := by norm_num
    rw [← h]
    exact pow_dvd_pow_of_dvd h24 2
  have h576C : 576 ∣
      Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) :=
    h576.trans (card_sl2_sq_dvd_card_centralizer_u1 h2)
  exact ⟨(by norm_num : 9 ∣ 576).trans h576C, (by norm_num : 64 ∣ 576).trans h576C⟩

theorem nine_dvd_card_centralizer_of_psp4 {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hX : CFSG.Blueprint.LieModel X .PSp 2 p f) (hp2 : p ≠ 2) (P : Sylow 2 X)
    (hP : Nat.card P = 64) (hZ : Nat.card (center ↥(P : Subgroup X)) = 2) {t : X}
    (htP : t ∈ (P : Subgroup X)) (htc : ∀ s ∈ (P : Subgroup X), Commute t s)
    (ht : orderOf t = 2) :
    9 ∣ Nat.card (centralizer ({t} : Set X)) := by
  obtain ⟨hp, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hX
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  set u : X := e.symm (u1 K) with hu_def
  have hu : orderOf u = 2 := by
    rw [hu_def, MulEquiv.orderOf_eq, orderOf_u1 h2]
  have hcard : Nat.card (centralizer ({u} : Set X)) =
      Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) := by
    rw [hu_def, ← map_centralizer_singleton e.symm (u1 K)]
    exact Subgroup.card_map_of_injective e.symm.injective
  have h64 : 64 ∣ Nat.card (centralizer ({u} : Set X)) := by
    rw [hcard]
    exact (nine_dvd_and_sixtyFour_dvd_card_centralizer_u1 hodd).2
  have h9 : 9 ∣ Nat.card (centralizer ({u} : Set X)) := by
    rw [hcard]
    exact (nine_dvd_and_sixtyFour_dvd_card_centralizer_u1 hodd).1
  have hPu : Nat.card P ∣ Nat.card (centralizer ({u} : Set X)) := by
    rw [hP]
    exact h64
  rw [CFSG.GroupTheory.card_centralizer_eq_of_card_center_eq_two P hZ htP htc ht hu hPu]
  exact h9

end CFSG.ComponentClassification.CatFactsSp4

module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovSurj
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
open scoped MatrixGroups

theorem ivk93cov_center_pow {F : Type} [Field F] {a : ℕ} [NeZero a] (z : SL(a, F))
    (hz : z ∈ center SL(a, F)) : z ^ a = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz]
  simp only [Fintype.card_fin] at hr
  rw [← map_pow, hr]
  simp

theorem ivk93cov_center_card_le {F : Type} [Field F] {a : ℕ} [NeZero a] :
    Nat.card ↥(center SL(a, F)) ≤ a := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin a) (R := F)
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne a)⟩
  rw [Nat.card_congr e.toEquiv]
  simpa using card_rootsOfUnity F (Fintype.card (Fin a))

theorem ivk93cov_card_sl4 {F : Type} [Field F] [Finite F] :
    Nat.card SL(4, F) =
      Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 4 - 1) :=
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_specialLinear_four

theorem ivk93cov_sl4_ne {f n k : ℕ} (hf : 3 ≤ f) (hk : k = 1 ∨ k = 2) (hn8 : 8 ≤ n)
    (hn11 : n ≤ 11) :
    f ^ 6 * (f ^ 2 - 1) * (f ^ 3 - 1) * (f ^ 4 - 1) ≠ k * n.factorial := by
  intro h
  rcases Nat.lt_or_ge f 4 with hf3 | hf4
  · have : f = 3 := by omega
    subst this
    rcases hk with rfl | rfl <;> interval_cases n <;> simp [Nat.factorial] at h
  · have h1 : 4 ^ 6 ≤ f ^ 6 := Nat.pow_le_pow_left hf4 6
    have h2 : 4 ^ 2 - 1 ≤ f ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hf4 2) 1
    have h3 : 4 ^ 3 - 1 ≤ f ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hf4 3) 1
    have h4 : 4 ^ 4 - 1 ≤ f ^ 4 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hf4 4) 1
    have h5 : 4 ^ 6 * (4 ^ 2 - 1) * (4 ^ 3 - 1) * (4 ^ 4 - 1) ≤
        f ^ 6 * (f ^ 2 - 1) * (f ^ 3 - 1) * (f ^ 4 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
    have h6 : n.factorial ≤ Nat.factorial 11 := Nat.factorial_le hn11
    have h7 : k * n.factorial ≤ 2 * Nat.factorial 11 := by
      have : k ≤ 2 := by omega
      exact Nat.mul_le_mul this h6
    have h8 : Nat.factorial 11 = 39916800 := by decide
    norm_num at h5
    omega

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem false_of_surj_sl (h : Ivk93Cov x n B) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {a : ℕ} (ha2 : 2 ≤ a) (ha4 : a ≤ 4) (ψ : SL(a, F) →* ↥B)
    (hψ : Function.Surjective ψ) : False := by
  have hF3 : 3 ≤ Nat.card F := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    obtain ⟨m, hm⟩ := hodd
    omega
  have hq : ∀ {a : ℕ}, 3 ≤ a → CFSG.IsQuasisimple SL(a, F) := fun ha =>
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup ha
  interval_cases a
  ·
    by_cases h5 : 5 ≤ Nat.card F
    · exact h.false_of_surj_sl2 hodd h5 ψ hψ
    · have hF : Nat.card F = 3 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      have h1 : Nat.card ↥B ≤ Nat.card SL(2, F) := Nat.card_le_card_of_surjective ψ hψ
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hF] at h1
      have := h.card_ge_big
      omega
  ·
    have hZ : Odd (Nat.card ↥(center SL(3, F))) := by
      refine Ivk93Adapt.odd_card_of_forall_odd (center SL(3, F)) fun y hy => ?_
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (ivk93cov_center_pow y hy))
    exact h.false_of_surj_odd_center (hq (by norm_num)) ψ hψ hZ
  ·
    obtain ⟨N, hNle, h1, h2⟩ := h.surj_quasisimple_card (hq (by norm_num)) ψ hψ
    have hZ4 : Nat.card ↥(center SL(4, F)) ≤ 4 := ivk93cov_center_card_le
    have hN : Nat.card ↥N = 1 ∨ Nat.card ↥N = 2 := by
      have : 0 < Nat.card ↥N := Nat.card_pos
      omega
    rw [ivk93cov_card_sl4] at h1
    exact ivk93cov_sl4_ne hF3 hN h.eight h.le_eleven h1

end Ivk93Cov

end CFSG.GH74.GLS.IVK.Proofs2

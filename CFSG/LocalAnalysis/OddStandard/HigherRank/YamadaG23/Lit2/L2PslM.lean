module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

theorem l2_two_ne_zero {K : Type} [Field K] [Finite K] (hq : Nat.card K % 2 = 1) :
    (2 : K) ≠ 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  apply Ring.two_ne_zero
  intro hc
  have h := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card] at h
  omega

theorem l2_sl_neg_one {K : Type} [Field K] (hK : (2 : K) ≠ 0) {n : ℕ} (hn : 0 < n)
    (he : Even n) :
    ∃ m : Matrix.SpecialLinearGroup (Fin n) K, (m : Matrix (Fin n) (Fin n) K) = -1 ∧ m ≠ 1 ∧
      m * m = 1 ∧ m ∈ center (Matrix.SpecialLinearGroup (Fin n) K) ∧
      ∀ u ∈ center (Matrix.SpecialLinearGroup (Fin n) K), u * u = 1 → u = 1 ∨ u = m := by
  have hdet : (-1 : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin, he.neg_one_pow, mul_one]
  let m : Matrix.SpecialLinearGroup (Fin n) K := ⟨-1, hdet⟩
  have i0 : Fin n := ⟨0, hn⟩
  refine ⟨m, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K) i0 i0) h
    simp [m] at h'
    exact hK (by linear_combination -h')
  · apply Subtype.ext
    change (-1 : Matrix (Fin n) (Fin n) K) * (-1) = 1
    simp
  · rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Matrix (Fin n) (Fin n) K) * (-1) = (-1) * (g : Matrix (Fin n) (Fin n) K)
    simp
  · intro u hu huu
    obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu
    have hu' : (u : Matrix (Fin n) (Fin n) K) = r • 1 := by
      rw [← hru, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K) i0 i0) huu
    simp [hu'] at h1
    have hr2 : (r - 1) * (r + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp hr2 with h | h
    · left
      have : r = 1 := by linear_combination h
      apply Subtype.ext
      simp [hu', this]
    · right
      have : r = -1 := by linear_combination h
      apply Subtype.ext
      simp [hu', this, m]

end CFSG.OddStandard.HigherRank.YamadaG23

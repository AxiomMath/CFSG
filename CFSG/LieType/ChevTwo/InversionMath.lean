
module

public import CFSG.LieType.ChevTwo.InversionBase

open Polynomial

public section

namespace CFSG.LieType.ChevTwo.GL4Math

theorem cayley4 {R : Type} [CommRing R] [Nontrivial R] (A : Matrix (Fin 4) (Fin 4) R) :
    A ^ 4 + algebraMap R _ (A.charpoly.coeff 3) * A ^ 3 + algebraMap R _ (A.charpoly.coeff 2) * A ^ 2 +
      algebraMap R _ (A.charpoly.coeff 1) * A + algebraMap R _ (A.charpoly.coeff 0) = 0 := by
  have h := Matrix.aeval_self_charpoly A
  rw [(Matrix.charpoly_monic A).as_sum, Matrix.charpoly_natDegree_eq_dim] at h
  simp only [Fintype.card_fin, Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_mul,
    map_pow, aeval_X, aeval_C, zero_add, pow_zero, pow_one, mul_one] at h
  rw [← h]
  abel

theorem core_tr {S : Type} [CommRing S] [Algebra (ZMod 2) S] (a : S) (c3 c2 : ZMod 2)
    (hp : a ^ 4 + algebraMap _ S c3 * a ^ 3 + algebraMap _ S c2 * a ^ 2 + algebraMap _ S c3 * a + 1 = 0)
    (h315 : a ^ 315 = 1) : a = 1 ∨ a ^ 3 = 1 ∨ a ^ 5 = 1 := by
  have h2 : (2 : S) = 0 := by
    have e : (2 : ZMod 2) = 0 := rfl
    rw [← map_ofNat (algebraMap (ZMod 2) S) 2, e, map_zero]
  have of_six (e : a ^ 6 = 1) : a ^ 3 = 1 := by
    have : a ^ 315 = (a ^ 6) ^ 52 * a ^ 3 := by ring
    rw [this, e, one_pow, one_mul] at h315
    exact h315
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c3 with rfl | rfl <;> rcases hc c2 with rfl | rfl <;>
    simp only [map_zero, map_one, zero_mul, one_mul, add_zero] at hp
  · have h4 : a ^ 4 = 1 := by linear_combination hp - h2
    left
    have : a ^ 315 = (a ^ 4) ^ 78 * a ^ 3 := by ring
    rw [this, h4, one_pow, one_mul] at h315
    linear_combination h4 - a * h315
  · right
    left
    exact of_six (by linear_combination (a ^ 2 - 1) * hp)
  · right
    left
    exact of_six (by linear_combination (a ^ 2 + a + 1) * hp -
      (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * h2)
  · right
    right
    linear_combination (a - 1) * hp

theorem key_matrix_math (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h315 : A ^ 315 = 1) (htr : A.trace = (A ^ 314).trace) : A = 1 ∨ A ^ 3 = 1 ∨ A ^ 5 = 1 := by
  have hAB : A * A ^ 314 = 1 := by rw [← pow_succ']; exact h315
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse hAB)
  have hinv : A⁻¹ = A ^ 314 := Matrix.inv_eq_right_inv hAB
  have hdet : A.charpoly.coeff 0 = 1 := by
    have hd := Matrix.det_eq_sign_charpoly_coeff A
    have hdu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hu
    simp only [Fintype.card_fin] at hd
    norm_num at hd
    rw [← hd]
    have : ∀ d : ZMod 2, IsUnit d → d = 1 := by decide
    exact this _ hdu
  have hdet' : A.det = 1 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hdet]
    norm_num
  have ht1 : A.trace = A.charpoly.coeff 3 := by
    rw [Matrix.trace_eq_neg_charpoly_coeff]
    simp only [Fintype.card_fin]
    have : ∀ d : ZMod 2, -d = d := by decide
    exact this _
  have ht2 : (A ^ 314).trace = A.charpoly.coeff 1 := by
    rw [← hinv, Matrix.trace_eq_neg_charpoly_coeff, Matrix.charpoly_inv A hu, hdet',
      Ring.inverse_one, ← Matrix.reverse_charpoly]
    simp only [Fintype.card_fin, map_one, mul_one]
    rw [neg_one_pow_eq_pow_mod_two (R := Polynomial (ZMod 2))]
    norm_num
    rw [Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.revAt_le (by norm_num)]
    all_goals
      have : ∀ d : ZMod 2, -d = d := by decide
      exact this _
  have hc : A.charpoly.coeff 1 = A.charpoly.coeff 3 := by rw [← ht1, ← ht2, htr]
  have hpA := cayley4 A
  simp only [hdet, hc, map_one] at hpA
  let S := Algebra.adjoin (ZMod 2) ({A} : Set (Matrix (Fin 4) (Fin 4) (ZMod 2)))
  have := Algebra.isMulCommutative_adjoin (ZMod 2) (s := {A}) (by simp)
  let a : S := ⟨A, Algebra.self_mem_adjoin_singleton _ _⟩
  have key := core_tr a (A.charpoly.coeff 3) (A.charpoly.coeff 2)
    (Subtype.ext (by simpa [a] using hpA)) (Subtype.ext (by simpa [a] using h315))
  have back : ∀ n : ℕ, a ^ n = 1 → A ^ n = 1 := fun n h => by
    have := congrArg Subtype.val h
    simpa [a] using this
  rcases key with h | h | h
  · left
    simpa using back 1 (by simpa using h)
  · exact Or.inr (Or.inl (back 3 h))
  · exact Or.inr (Or.inr (back 5 h))

open CFSG.LieType.ChevTwo.GL4Native in
theorem chk_all_math : ∀ v : Fin 16 → ZMod 2, chk (List.ofFn v) = true := by
  intro v
  let A : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun i j => v ⟨4 * i.val + j.val, by omega⟩
  have hv : List.ofFn v = toL A := by
    unfold toL
    congr 1
    funext k
    simp only [A, Matrix.of_apply]
    congr 1
    apply Fin.ext
    simp only [ij]
    omega
  have hinj : ∀ X Y : Matrix (Fin 4) (Fin 4) (ZMod 2), toL X = toL Y ↔ X = Y :=
    fun X Y => ⟨toL_injective, congrArg _⟩
  rw [hv]
  unfold chk
  simp only [powL_toL, ← oneL_toL, trL_toL, hinj]
  by_cases h1 : A ^ 315 = 1
  · by_cases h2 : A.trace = (A ^ 314).trace
    · rcases key_matrix_math A h1 h2 with h | h | h <;> simp [h]
    · simp [h2]
  · simp [h1]

end CFSG.LieType.ChevTwo.GL4Math

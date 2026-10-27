module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMonomial
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.QuasithinUnique.K1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_smul_one_add_single_of_commute (hn : 2 ≤ n) (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → M * single i j (1 : K) = single i j (1 : K) * M) :
    ∃ a b : K, M = a • (1 : Matrix (Fin n) (Fin n) K) +
      b • single (⟨0, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n) (1 : K) := by
  have hoff : ∀ k l : Fin n, k ≠ l → ¬ ((k : ℕ) = 0 ∧ (l : ℕ) = n - 1) → M k l = 0 := by
    intro k l hkl hkl'
    by_cases hl : (l : ℕ) + 1 < n
    · have h := congrFun₂ (hM l ⟨(l : ℕ) + 1, hl⟩ rfl) k ⟨(l : ℕ) + 1, hl⟩
      rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hkl] at h
      simpa using h
    · have hl' : (l : ℕ) = n - 1 := by omega
      have hk0 : (k : ℕ) ≠ 0 := fun h => hkl' ⟨h, hl'⟩
      have hkl2 : (k : ℕ) ≠ n - 1 := fun h => hkl (Fin.ext (h.trans hl'.symm))
      have hk1 : (k : ℕ) - 1 + 1 = (k : ℕ) := by omega
      let i : Fin n := ⟨(k : ℕ) - 1, by omega⟩
      have h := congrFun₂ (hM i k (by simp [i]; omega)) i l
      have hlk : l ≠ k := fun h => hkl (h.symm)
      rw [mul_single_apply_of_ne _ _ _ _ _ hlk, single_mul_apply_same] at h
      simpa using h.symm
  have hdiag : ∀ m : ℕ, ∀ hm : m < n, M ⟨m, hm⟩ ⟨m, hm⟩ = M ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      have h := congrFun₂ (hM ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl) ⟨m, by omega⟩ ⟨m + 1, hm⟩
      rw [mul_single_apply_same, single_mul_apply_same] at h
      simp only [mul_one, one_mul] at h
      rw [← h]
      exact ih (by omega)
  refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, M ⟨0, by omega⟩ ⟨n - 1, by omega⟩, ?_⟩
  ext k l
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, single_apply]
  by_cases hkl : k = l
  · subst hkl
    have h0 : ¬ (((⟨0, by omega⟩ : Fin n) = k) ∧ ((⟨n - 1, by omega⟩ : Fin n) = k)) := by
      rintro ⟨h1, h2⟩
      have := congrArg Fin.val (h2.trans h1.symm)
      simp at this
      omega
    simp only [one_apply_eq, h0, ite_false, smul_eq_mul, mul_one, mul_zero, add_zero]
    exact hdiag k.val k.2
  · by_cases h : (k : ℕ) = 0 ∧ (l : ℕ) = n - 1
    · have hk : (⟨0, by omega⟩ : Fin n) = k := Fin.ext h.1.symm
      have hl : (⟨n - 1, by omega⟩ : Fin n) = l := Fin.ext h.2.symm
      simp only [one_apply_ne hkl, hk, hl, and_self, ite_true, smul_eq_mul, mul_zero, zero_add,
        mul_one]
    · have h2 : ¬ (((⟨0, by omega⟩ : Fin n) = k) ∧ ((⟨n - 1, by omega⟩ : Fin n) = l)) := by
        rintro ⟨h1, h2⟩
        exact h ⟨by rw [← h1], by rw [← h2]⟩
      simp only [one_apply_ne hkl, h2, ite_false, add_zero, smul_eq_mul, mul_zero]
      exact hoff k l hkl h

theorem fin_mk_ne {a b : ℕ} (ha : a < n) (hb : b < n) (h : a ≠ b) :
    (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ := fun e => h (congrArg Fin.val e)

theorem transvection_congr {i j i' j' : Fin n} (h : i ≠ j) (h' : i' ≠ j') (hi : i = i')
    (hj : j = j') (t : K) :
    SpecialLinearGroup.transvection h t = SpecialLinearGroup.transvection h' t := by
  subst hi
  subst hj
  rfl

theorem transvection_mem_unitriangular {i j : Fin n} (hij : i < j) (t : K) :
    SpecialLinearGroup.transvection hij.ne t ∈ unitriangular n K := by
  refine ⟨fun k l hlk => ?_, fun k => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply,
      one_apply_ne (ne_of_gt hlk)]
    have : ¬ (i = k ∧ j = l) := fun ⟨h1, h2⟩ => by
      subst h1
      subst h2
      exact absurd hlk (not_lt.mpr hij.le)
    simp [this]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply, one_apply_eq]
    have : ¬ (i = k ∧ j = k) := fun ⟨h1, h2⟩ => hij.ne (h1.trans h2.symm)
    simp [this]

theorem transvection_mul_self_of_charTwo [CharP K 2] {i j : Fin n} (hij : i ≠ j) (t : K) :
    SpecialLinearGroup.transvection hij t * SpecialLinearGroup.transvection hij t = 1 := by
  rw [← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    SpecialLinearGroup.transvection_coeff_zero]

theorem signedPermutation_mulVec_single [CharP K 2] (w : Equiv.Perm (Fin n)) (j : Fin n) :
    (signedPermutation n K w : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 =
      ((1 : Kˣ) : K) • (Pi.single (w j) 1 : Fin n → K) := by
  have hsign : ((Equiv.Perm.sign w : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h
    · rw [h]
      simp
    · rw [h]
      simp [CharTwo.neg_eq]
  rw [coe_signedPermutation, signedPermMatrix, ← mulVec_mulVec, permMatrix_mulVec_single]
  ext a
  have hd : (if (a : ℕ) = 0 then ((Equiv.Perm.sign w : ℤ) : K) else 1) = 1 := by
    split_ifs
    · exact hsign
    · rfl
  rw [mulVec_diagonal, hd, Pi.smul_apply, Units.val_one, one_smul, one_mul]

theorem signedPermutation_conj_transvection [CharP K 2] (w : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a ≠ b) (t : K) :
    signedPermutation n K w * SpecialLinearGroup.transvection hab t * (signedPermutation n K w)⁻¹ =
      SpecialLinearGroup.transvection (w.injective.ne hab) t := by
  have h := monomial_conj_transvection (M := signedPermutation n K w) (w := w)
    (c := fun _ => (1 : Kˣ)) (fun j => signedPermutation_mulVec_single w j) hab t
  simpa using h

end CFSG.QuasithinUnique.K1

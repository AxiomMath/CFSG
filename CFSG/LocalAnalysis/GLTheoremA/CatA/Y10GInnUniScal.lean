module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScalCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScalMat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open Matrix

theorem uScal_entry_mul_torus {K : Type} [Field K] {d : ℕ} (u : Kˣ) {a b : Fin d} (hab : a ≠ b)
    (X : Matrix (Fin d) (Fin d) K) :
    (X * uScal_torusMat u a b) a b = X a b * ((u⁻¹ : Kˣ) : K) := by
  simp [uScal_torusMat, Matrix.mul_diagonal, Ne.symm hab]

theorem uScal_entry_torus_mul {K : Type} [Field K] {d : ℕ} (u : Kˣ) {a b : Fin d}
    (X : Matrix (Fin d) (Fin d) K) :
    (uScal_torusMat u a b * X) a b = (u : K) * X a b := by
  simp [uScal_torusMat, Matrix.diagonal_mul]

theorem uniScalar_holds : UniScalar := by
  intro K _ _ Q d τ hτ hτQ hcard hd hdQ B hB
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' K
  have hdvd : Q ∣ p ^ (n : ℕ) := by
    rw [← hpn, ← Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self Q two_ne_zero
  obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect (StatedSU d (p ^ m) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard hd hdQ
  have hcomm := uScal_commute_of_isPerfect (StatedSU d (p ^ m) K) B hB
  have hQ2 : 2 ≤ p ^ m := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard] at h1
    by_contra hlt
    push Not at hlt
    interval_cases h : p ^ m <;> omega
  have hQ0 : p ^ m ≠ 0 := by omega
  have hcardU : Nat.card Kˣ = (p ^ m) ^ 2 - 1 :=
    CFSG.ClassicalGroups.Unitary.card_units_of_card hcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ m) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  obtain ⟨u, hu_def⟩ : ∃ u : Kˣ, u = g ^ (p ^ m - 1) := ⟨_, rfl⟩
  have hu1 : u ^ (p ^ m + 1) = 1 := by
    have hQ1 : 1 ≤ p ^ m := by omega
    have hQ1' : 1 ≤ (p ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have he : (p ^ m - 1) * (p ^ m + 1) = (p ^ m) ^ 2 - 1 := by
      zify [hQ1, hQ1']
      ring
    rw [hu_def, ← pow_mul, he, ← hord, pow_orderOf_eq_one]
  have hu2 : u⁻¹ ≠ u := by
    intro h
    have h2 : u * u = 1 := by
      calc u * u = u * u⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel u
    have h3 : g ^ (2 * (p ^ m - 1)) = 1 := by
      rw [two_mul, pow_add, ← hu_def]
      exact h2
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hord] at h4
    have h5 := Nat.le_of_dvd (by omega) h4
    obtain ⟨a, ha⟩ : ∃ a, p ^ m = a + 1 := ⟨p ^ m - 1, by omega⟩
    rw [ha] at h5
    have ha1 : 1 ≤ a := by omega
    have hsq : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
    have hpos : 0 < a ^ 2 := pow_pos (by omega) 2
    rw [hsq] at h5
    omega
  have hu1K : ((u : Kˣ) : K) ^ (p ^ m + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]
  have hdiagB : ∀ a b : Fin d, a ≠ b → (B : Matrix (Fin d) (Fin d) K) a b = 0 := by
    intro a b hab
    have hmem := uScal_torusGL_mem hQ0 u hu1 hab
    have hc := hcomm _ hmem
    have hmat : (B : Matrix (Fin d) (Fin d) K) * uScal_torusMat u a b =
        uScal_torusMat u a b * (B : Matrix (Fin d) (Fin d) K) := by
      have hv := congrArg Units.val hc
      rw [Units.val_mul, Units.val_mul, uScal_torusGL_val] at hv
      exact hv
    have e : ((B : Matrix (Fin d) (Fin d) K) * uScal_torusMat u a b) a b =
        (uScal_torusMat u a b * (B : Matrix (Fin d) (Fin d) K)) a b := by
      rw [hmat]
    rw [uScal_entry_mul_torus u hab, uScal_entry_torus_mul u] at e
    have h0 : (B : Matrix (Fin d) (Fin d) K) a b *
        (((u⁻¹ : Kˣ) : K) - (u : K)) = 0 := by
      linear_combination e
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact absurd (Units.ext (sub_eq_zero.1 h)) hu2
  have hsameB : ∀ a b : Fin d, a ≠ b →
      (B : Matrix (Fin d) (Fin d) K) a a = (B : Matrix (Fin d) (Fin d) K) b b := by
    intro a b hab
    have hmem := uScal_rotGL_mem hQ0 τ hτQ hab
    have hc := hcomm _ hmem
    have hmat : (B : Matrix (Fin d) (Fin d) K) * uScal_rotMat (K := K) a b =
        uScal_rotMat (K := K) a b * (B : Matrix (Fin d) (Fin d) K) := by
      have hv := congrArg Units.val hc
      rw [Units.val_mul, Units.val_mul, uScal_rotGL_val] at hv
      exact hv
    have e : ((B : Matrix (Fin d) (Fin d) K) * uScal_rotMat (K := K) a b) a b =
        (uScal_rotMat (K := K) a b * (B : Matrix (Fin d) (Fin d) K)) a b := by
      rw [hmat]
    have h1 : ((B : Matrix (Fin d) (Fin d) K) * uScal_rotMat (K := K) a b) a b =
        (B : Matrix (Fin d) (Fin d) K) a a * uScal_rotMat (K := K) a b a b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro k _ hk
        rw [hdiagB a k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a) h
    have h2 : (uScal_rotMat (K := K) a b * (B : Matrix (Fin d) (Fin d) K)) a b =
        uScal_rotMat (K := K) a b a b * (B : Matrix (Fin d) (Fin d) K) b b := by
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · intro k _ hk
        rw [hdiagB k b hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ b) h
    rw [h1, h2, uScal_rotMat_swap_entry] at e
    linear_combination -e
  have hsame : ∀ x y : Fin d, (B : Matrix (Fin d) (Fin d) K) x x =
      (B : Matrix (Fin d) (Fin d) K) y y := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy]
    · exact hsameB x y hxy
  let i0 : Fin d := ⟨0, by omega⟩
  refine ⟨(B : Matrix (Fin d) (Fin d) K) i0 i0, ?_⟩
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.one_apply, hsame x i0]
  · simp [Matrix.one_apply, hxy, hdiagB x y hxy]

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end

module

public import CFSG.Fischer.Classification.PartIII.U.Linear3

public section

namespace CFSG.Fischer.Classification.LocalU4

open CFSG.ClassicalGroups.Unitary CFSG.Fischer.Classification.Unitary
  CFSG.Fischer.Classification.LocalU
open CFSG.Blueprint.Fischer (K)

noncomputable abbrev v2 (a b : K) : Fin 2 → K := ![a, b]

theorem herm_v2 (a b a' b' : K) : herm frob (v2 a b) (v2 a' b') = frob a * a' + frob b * b' := by
  simp [herm_def, Fin.sum_univ_two]

theorem eq_v2 (z : Fin 2 → K) : z = v2 (z 0) (z 1) := by
  funext i
  fin_cases i <;> rfl

theorem smul_v2 (t a b : K) : t • v2 a b = v2 (t * a) (t * b) := by
  funext i
  fin_cases i <;> simp

theorem add_v2 (a b a' b' : K) : v2 a b + v2 a' b' = v2 (a + a') (b + b') := by
  funext i
  fin_cases i <;> simp

theorem v2_ne_zero_of_left {a : K} (ha : a ≠ 0) (b : K) : v2 a b ≠ 0 := fun h =>
  ha (by simpa using congrFun h 0)

theorem isotropic_two {z : Fin 2 → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    ∃ t c : K, t ≠ 0 ∧ c ≠ 0 ∧ z = t • v2 1 c := by
  rw [eq_v2 z] at hz0 hz ⊢
  generalize z 0 = a, z 1 = b at hz0 hz ⊢
  rw [herm_v2] at hz
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · exact (hz0 (by rw [ha, hb]; funext i; fin_cases i <;> rfl)).elim
  · simp only [ha, map_zero, zero_mul, zero_add, frob_mul_self hb] at hz
    exact (h1 hz).elim
  · simp only [hb, map_zero, zero_mul, add_zero, frob_mul_self ha] at hz
    exact (h1 hz).elim
  · refine ⟨a, b / a, ha, div_ne_zero hb ha, ?_⟩
    rw [smul_v2, mul_one, mul_div_cancel₀ b ha]

theorem isotropic_v2 {c : K} (hc : c ≠ 0) : herm frob (v2 1 c) (v2 1 c) = 0 := by
  rw [herm_v2, map_one, one_mul, frob_mul_self hc, one_add_one_K]

theorem eq_zero_of_section_two {δ : (Fin 2 → K) → K} (hδ : IsSectionFun δ)
    (h1 : δ (v2 1 1) = 0) (h2 : δ (v2 1 ω) = 0) {z : Fin 2 → K} (hz0 : z ≠ 0)
    (hz : herm frob z z = 0) : δ z = 0 := by
  have hω0 : ω ≠ 0 := omega_ne_zero
  have hω1 : ω + 1 ≠ 0 := fun h => omega_ne_one (by linear_combination h - one_add_one_K)
  have hA : ∀ c : K, c ≠ 0 → δ (v2 1 c) = 0 := by
    have h12 : herm frob (v2 1 1) (v2 1 ω) = ω + 1 := by
      rw [herm_v2]; simp; ring
    have hstep := hδ.2 (v2 1 1) (v2 1 ω) (v2_ne_zero_of_left one_ne_zero _)
      (isotropic_v2 one_ne_zero) (v2_ne_zero_of_left one_ne_zero _) (isotropic_v2 hω0)
      (by rw [h12]; exact hω1)
    rw [h12, h1, h2, mul_zero, add_zero, smul_v2, add_v2] at hstep
    have hv : v2 (1 + (ω + 1) * 1) (ω + (ω + 1) * 1) = ω • v2 1 (ω + 1) := by
      rw [smul_v2]
      congr 1
      · linear_combination one_add_one_K
      · linear_combination (-1 : K) * omega_mul_omega
    rw [hv, hδ.1 _ (v2_ne_zero_of_left one_ne_zero _) (isotropic_v2 hω1) ω hω0] at hstep
    have h3 : δ (v2 1 (ω + 1)) = 0 := (mul_eq_zero.1 hstep).resolve_left hω0
    intro c hc
    rcases K_cases c with rfl | rfl | rfl | rfl
    · exact (hc rfl).elim
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨t, c, ht, hc, rfl⟩ := isotropic_two hz0 hz
  rw [hδ.1 _ (v2_ne_zero_of_left one_ne_zero _) (isotropic_v2 hc) t ht, hA c hc, mul_zero]

theorem exists_eq_herm_of_section_two {γ : (Fin 2 → K) → K} (hγ : IsSectionFun γ) :
    ∃ y : Fin 2 → K, ∀ z : Fin 2 → K, z ≠ 0 → herm frob z z = 0 → γ z = herm frob y z := by
  set b := ω * (γ (v2 1 1) + γ (v2 1 ω))
  set a := γ (v2 1 1) + b
  refine ⟨v2 (frob a) (frob b), fun z hz0 hz => ?_⟩
  have hδ := hγ.sub_herm (v2 (frob a) (frob b))
  have key := eq_zero_of_section_two hδ ?_ ?_ hz0 hz
  · exact sub_eq_zero.1 key
  · simp only [herm_v2, frob_frob, mul_one]
    simp only [a]
    linear_combination (-1 : K) * add_self_K b
  · simp only [herm_v2, frob_frob, mul_one]
    simp only [a, b]
    linear_combination (-(γ (v2 1 1) + γ (v2 1 ω))) * omega_mul_omega -
      (γ (v2 1 1) + ω * (γ (v2 1 1) + γ (v2 1 ω))) * one_add_one_K

end CFSG.Fischer.Classification.LocalU4

module

public import CFSG.Fischer.Classification.PartIII.U.Defect
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.ClassicalGroups.Unitary CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

@[expose] def IsSectionFun {n : ℕ} (γ : (Fin n → K) → K) : Prop :=
  (∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ c : K, c ≠ 0 → γ (c • x) = c * γ x) ∧
  ∀ x x' : Fin n → K, x ≠ 0 → herm frob x x = 0 → x' ≠ 0 → herm frob x' x' = 0 →
    herm frob x x' ≠ 0 → γ (x' + herm frob x x' • x) = γ x' + herm frob x x' * γ x

theorem IsSectionFun.sub_herm {n : ℕ} {γ : (Fin n → K) → K} (h : IsSectionFun γ)
    (y : Fin n → K) : IsSectionFun (fun z => γ z - herm frob y z) := by
  refine ⟨fun x hx0 hx c hc => ?_, fun x x' hx0 hx hx0' hx' hxx' => ?_⟩
  · simp only [h.1 x hx0 hx c hc, herm_smul_right]
    ring
  · simp only [h.2 x x' hx0 hx hx0' hx' hxx', herm_add_right, herm_smul_right]
    ring

theorem K_cases (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω + 1 := by
  obtain ⟨x, rfl⟩ := eF4.surjective c
  have hx : x = 0 ∨ x = 1 ∨ x = CFSG.Fischer.F4.ω ∨ x = CFSG.Fischer.F4.ω + 1 := by
    revert x; decide
  rcases hx with rfl | rfl | rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl (map_one _))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_add, map_one]; rfl)))

noncomputable abbrev v3 (a b c : K) : Fin 3 → K := ![a, b, c]

theorem herm_v3 (a b c a' b' c' : K) :
    herm frob (v3 a b c) (v3 a' b' c') = frob a * a' + frob b * b' + frob c * c' := by
  simp [herm_def, Fin.sum_univ_three]

theorem eq_v3 (z : Fin 3 → K) : z = v3 (z 0) (z 1) (z 2) := by
  funext i
  fin_cases i <;> rfl

theorem smul_v3 (t a b c : K) : t • v3 a b c = v3 (t * a) (t * b) (t * c) := by
  funext i
  fin_cases i <;> simp

theorem add_v3 (a b c a' b' c' : K) :
    v3 a b c + v3 a' b' c' = v3 (a + a') (b + b') (c + c') := by
  funext i
  fin_cases i <;> simp

theorem v3_ne_zero_of_left {a : K} (ha : a ≠ 0) (b c : K) : v3 a b c ≠ 0 := fun h =>
  ha (by simpa using congrFun h 0)

theorem v3_ne_zero_of_mid {b : K} (hb : b ≠ 0) (a c : K) : v3 a b c ≠ 0 := fun h =>
  hb (by simpa using congrFun h 1)

theorem isotropic_three {z : Fin 3 → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) :
    ∃ t c : K, t ≠ 0 ∧ c ≠ 0 ∧
      (z = t • v3 1 c 0 ∨ z = t • v3 1 0 c ∨ z = t • v3 0 1 c) := by
  rw [eq_v3 z] at hz0 hz ⊢
  generalize z 0 = a, z 1 = b, z 2 = c at hz0 hz ⊢
  rw [herm_v3] at hz
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have h3 : (1 : K) + 1 + 1 ≠ 0 := by rw [one_add_one_K, zero_add]; exact h1
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0
  · exact (hz0 (by rw [ha, hb, hc]; funext i; fin_cases i <;> rfl)).elim
  · simp only [ha, hb, map_zero, zero_mul, zero_add, frob_mul_self hc] at hz
    exact (h1 hz).elim
  · simp only [ha, hc, map_zero, zero_mul, zero_add, add_zero, frob_mul_self hb] at hz
    exact (h1 hz).elim
  · refine ⟨b, c / b, hb, div_ne_zero hc hb, Or.inr (Or.inr ?_)⟩
    rw [smul_v3, ha, mul_zero, mul_one, mul_div_cancel₀ c hb]
  · simp only [hb, hc, map_zero, zero_mul, add_zero, frob_mul_self ha] at hz
    exact (h1 hz).elim
  · refine ⟨a, c / a, ha, div_ne_zero hc ha, Or.inr (Or.inl ?_)⟩
    rw [smul_v3, hb, mul_zero, mul_one, mul_div_cancel₀ c ha]
  · refine ⟨a, b / a, ha, div_ne_zero hb ha, Or.inl ?_⟩
    rw [smul_v3, hc, mul_zero, mul_one, mul_div_cancel₀ b ha]
  · rw [frob_mul_self ha, frob_mul_self hb, frob_mul_self hc] at hz
    exact (h3 hz).elim

theorem isotropic_v3_left {c : K} (hc : c ≠ 0) : herm frob (v3 1 c 0) (v3 1 c 0) = 0 := by
  rw [herm_v3, map_one, one_mul, frob_mul_self hc, map_zero, mul_zero, add_zero,
    one_add_one_K]

theorem isotropic_v3_mid {c : K} (hc : c ≠ 0) : herm frob (v3 1 0 c) (v3 1 0 c) = 0 := by
  rw [herm_v3, map_one, one_mul, frob_mul_self hc, map_zero, mul_zero, add_zero,
    one_add_one_K]

theorem isotropic_v3_right {c : K} (hc : c ≠ 0) : herm frob (v3 0 1 c) (v3 0 1 c) = 0 := by
  rw [herm_v3, map_one, one_mul, frob_mul_self hc, map_zero, mul_zero, zero_add,
    one_add_one_K]

theorem eq_zero_of_section {δ : (Fin 3 → K) → K} (hδ : IsSectionFun δ)
    (h1 : δ (v3 1 1 0) = 0) (h2 : δ (v3 1 ω 0) = 0) (h3 : δ (v3 0 1 1) = 0)
    {z : Fin 3 → K} (hz0 : z ≠ 0) (hz : herm frob z z = 0) : δ z = 0 := by
  have hω0 : ω ≠ 0 := omega_ne_zero
  have hω1 : ω + 1 ≠ 0 := fun h => omega_ne_one (by linear_combination h - one_add_one_K)
  have hA : ∀ c : K, c ≠ 0 → δ (v3 1 c 0) = 0 := by
    have h12 : herm frob (v3 1 1 0) (v3 1 ω 0) = ω + 1 := by
      rw [herm_v3]; simp; ring
    have hstep := hδ.2 (v3 1 1 0) (v3 1 ω 0) (v3_ne_zero_of_left one_ne_zero _ _)
      (isotropic_v3_left one_ne_zero) (v3_ne_zero_of_left one_ne_zero _ _)
      (isotropic_v3_left hω0) (by rw [h12]; exact hω1)
    rw [h12, h1, h2, mul_zero, add_zero, smul_v3, add_v3] at hstep
    have hv : v3 (1 + (ω + 1) * 1) (ω + (ω + 1) * 1) (0 + (ω + 1) * 0) =
        ω • v3 1 (ω + 1) 0 := by
      rw [smul_v3]
      congr 1
      · linear_combination one_add_one_K
      · linear_combination (-1 : K) * omega_mul_omega
      · simp
    rw [hv, hδ.1 _ (v3_ne_zero_of_left one_ne_zero _ _) (isotropic_v3_left hω1) ω hω0]
      at hstep
    have h3' : δ (v3 1 (ω + 1) 0) = 0 :=
      (mul_eq_zero.1 hstep).resolve_left hω0
    intro c hc
    rcases K_cases c with rfl | rfl | rfl | rfl
    · exact (hc rfl).elim
    · exact h1
    · exact h2
    · exact h3'
  have hB : ∀ c : K, c ≠ 0 → δ (v3 1 0 c) = 0 := fun c hc => by
    have h12 : herm frob (v3 0 1 1) (v3 1 c 0) = c := by rw [herm_v3]; simp
    have hstep := hδ.2 (v3 0 1 1) (v3 1 c 0) (v3_ne_zero_of_mid one_ne_zero _ _)
      (isotropic_v3_right one_ne_zero) (v3_ne_zero_of_left one_ne_zero _ _)
      (isotropic_v3_left hc) (by rw [h12]; exact hc)
    rw [h12, hA c hc, h3, mul_zero, add_zero, smul_v3, add_v3] at hstep
    have hv : v3 (1 + c * 0) (c + c * 1) (0 + c * 1) = v3 1 0 c := by
      congr 1 <;> simp [add_self_K]
    rwa [hv] at hstep
  have hC : ∀ c : K, c ≠ 0 → δ (v3 0 1 c) = 0 := fun c hc => by
    have h12 : herm frob (v3 1 0 c) (v3 1 1 0) = 1 := by rw [herm_v3]; simp
    have hstep := hδ.2 (v3 1 0 c) (v3 1 1 0) (v3_ne_zero_of_left one_ne_zero _ _)
      (isotropic_v3_mid hc) (v3_ne_zero_of_left one_ne_zero _ _)
      (isotropic_v3_left one_ne_zero) (by rw [h12]; exact one_ne_zero)
    rw [h12, h1, hB c hc, mul_zero, add_zero, one_smul, add_v3] at hstep
    have hv : v3 (1 + 1) (1 + 0) (0 + c) = v3 0 1 c := by
      congr 1 <;> simp [one_add_one_K]
    rwa [hv] at hstep
  obtain ⟨t, c, ht, hc, h | h | h⟩ := isotropic_three hz0 hz <;> rw [h]
  · rw [hδ.1 _ (v3_ne_zero_of_left one_ne_zero _ _) (isotropic_v3_left hc) t ht, hA c hc,
      mul_zero]
  · rw [hδ.1 _ (v3_ne_zero_of_left one_ne_zero _ _) (isotropic_v3_mid hc) t ht, hB c hc,
      mul_zero]
  · rw [hδ.1 _ (v3_ne_zero_of_mid one_ne_zero _ _) (isotropic_v3_right hc) t ht, hC c hc,
      mul_zero]

theorem exists_eq_herm_of_section {γ : (Fin 3 → K) → K} (hγ : IsSectionFun γ) :
    ∃ y : Fin 3 → K, ∀ z : Fin 3 → K, z ≠ 0 → herm frob z z = 0 → γ z = herm frob y z := by
  set b := ω * (γ (v3 1 1 0) + γ (v3 1 ω 0))
  set a := γ (v3 1 1 0) + b
  set c := γ (v3 0 1 1) + b
  refine ⟨v3 (frob a) (frob b) (frob c), fun z hz0 hz => ?_⟩
  have hδ := hγ.sub_herm (v3 (frob a) (frob b) (frob c))
  have key := eq_zero_of_section hδ ?_ ?_ ?_ hz0 hz
  · exact sub_eq_zero.1 key
  · simp only [herm_v3, frob_frob, mul_one, mul_zero, add_zero]
    simp only [a]
    linear_combination (-1 : K) * add_self_K b
  · simp only [herm_v3, frob_frob, mul_one, mul_zero, add_zero]
    simp only [a, b]
    linear_combination (-(γ (v3 1 1 0) + γ (v3 1 ω 0))) * omega_mul_omega -
      (γ (v3 1 1 0) + ω * (γ (v3 1 1 0) + γ (v3 1 ω 0))) * one_add_one_K
  · simp only [herm_v3, frob_frob, mul_one, mul_zero, zero_add]
    simp only [c]
    linear_combination (-1 : K) * add_self_K b

end CFSG.Fischer.Classification.LocalU

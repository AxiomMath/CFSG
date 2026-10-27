module

public import CFSG.Fischer.Classification.Unitary.Basic

public section

namespace CFSG.Fischer.Classification.LocalU

open CFSG.ClassicalGroups.Unitary CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

@[expose] noncomputable def tvv (y z : Fin n → K) : Fin n → K := z + herm frob y z • y

noncomputable abbrev ee (i : Fin n) : Fin n → K := Pi.single i 1

theorem tvv_add (y a b : Fin n → K) : tvv y (a + b) = tvv y a + tvv y b := by
  simp only [tvv, herm_add_right, add_smul]
  abel

theorem herm_tvv_self {y z : Fin n → K} (hy : herm frob y y = 0) :
    herm frob (tvv y z) (tvv y z) = herm frob z z := by
  have hc : herm frob z y = frob (herm frob y z) := herm_conj frob frob_frob y z
  simp only [tvv, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hy, mul_zero,
    add_zero, hc]
  have h : herm frob y z * frob (herm frob y z) + frob (herm frob y z) * herm frob y z = 0 := by
    rw [mul_comm]
    exact add_self_K _
  linear_combination h

theorem tvv_tvv {y z : Fin n → K} (hy : herm frob y y = 0) : tvv y (tvv y z) = z := by
  simp only [tvv, herm_add_right, herm_smul_right, hy, mul_zero, add_zero, add_assoc]
  rw [← add_smul, add_self_K, zero_smul, add_zero]

theorem tvv_ne_zero {y z : Fin n → K} (hy : herm frob y y = 0) (hz : z ≠ 0) : tvv y z ≠ 0 :=
  fun h => hz (by rw [← tvv_tvv (z := z) hy, h, tvv, herm_zero_right, zero_smul, add_zero])

theorem tvv_of_herm_eq_zero {y z : Fin n → K} (h : herm frob y z = 0) : tvv y z = z := by
  rw [tvv, h, zero_smul, add_zero]

@[expose] def GoodPair (a b : Fin n → K) : Prop :=
  a ≠ 0 ∧ herm frob a a = 0 ∧ b ≠ 0 ∧ herm frob b b = 0 ∧ a + b ≠ 0 ∧
    herm frob (a + b) (a + b) = 0

theorem GoodPair.tvv {y a b : Fin n → K} (hy : herm frob y y = 0) (h : GoodPair a b) :
    GoodPair (tvv y a) (tvv y b) := by
  obtain ⟨ha0, ha, hb0, hb, hab0, hab⟩ := h
  refine ⟨tvv_ne_zero hy ha0, by rw [herm_tvv_self hy]; exact ha, tvv_ne_zero hy hb0,
    by rw [herm_tvv_self hy]; exact hb, ?_, ?_⟩
  · rw [← tvv_add]; exact tvv_ne_zero hy hab0
  · rw [← tvv_add, herm_tvv_self hy]; exact hab

theorem one_add_one_K : (1 : K) + 1 = 0 := add_self_K 1

theorem goodPair_std (i : Fin 5 ↪ Fin n) :
    GoodPair (ee (i 0) + ee (i 1)) (ee (i 2) + ee (i 3)) := by
  refine ⟨fun h => ?_, ?_, fun h => ?_, ?_, fun h => ?_, ?_⟩
  · have := congrFun h (i 0); simp at this
  · simp [herm_single_left, add_self_K]
  · have := congrFun h (i 2); simp at this
  · simp [herm_single_left, add_self_K]
  · have := congrFun h (i 0); simp at this
  · simp [herm_single_left]
    linear_combination (1 + 1 : K) * one_add_one_K

theorem herm_std (i : Fin 5 ↪ Fin n) :
    herm frob (ee (i 0) + ee (i 1)) (ee (i 2) + ee (i 3)) = 0 := by
  simp [herm_single_left]

theorem std_ne_smul (i : Fin 5 ↪ Fin n) (c : K) :
    ee (i 2) + ee (i 3) ≠ c • (ee (i 0) + ee (i 1)) := fun h => by
  have := congrFun h (i 2); simp at this

section Section

variable (γ : (Fin n → K) → K)
  (h1 : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ c : K, c ≠ 0 → γ (c • x) = c * γ x)
  (h2 : ∀ x x' : Fin n → K, x ≠ 0 → herm frob x x = 0 → x' ≠ 0 → herm frob x' x' = 0 →
    herm frob x x' ≠ 0 → γ (x' + herm frob x x' • x) = γ x' + herm frob x x' * γ x)

include h2 in
theorem γ_tvv {y z : Fin n → K} (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hz0 : z ≠ 0)
    (hz : herm frob z z = 0) : γ (tvv y z) = γ z + herm frob y z * γ y := by
  by_cases hyz : herm frob y z = 0
  · rw [tvv_of_herm_eq_zero hyz, hyz, zero_mul, add_zero]
  · exact h2 y z hy0 hy hz0 hz hyz

include h2 in
theorem defect_tvv {y a b : Fin n → K} (hy0 : y ≠ 0) (hy : herm frob y y = 0)
    (h : GoodPair a b) :
    γ (tvv y a + tvv y b) - γ (tvv y a) - γ (tvv y b) = γ (a + b) - γ a - γ b := by
  obtain ⟨ha0, ha, hb0, hb, hab0, hab⟩ := h
  rw [← tvv_add, γ_tvv γ h2 hy0 hy hab0 hab, γ_tvv γ h2 hy0 hy ha0 ha,
    γ_tvv γ h2 hy0 hy hb0 hb, herm_add_right]
  ring

theorem omega_mul_omega : ω * ω = ω + 1 := by
  rw [← sq, ← frob_apply, frob_omega]

theorem frobenius_omega : (frobenius K 2) ω = ω + 1 := frob_omega

theorem add_self_vec (x : Fin n → K) : x + x = 0 := by
  rw [← two_smul K, two_eq_zero, zero_smul]

include h1 h2 in
theorem map_add_eq (i : Fin 5 ↪ Fin n) :
    γ (ee (i 0) + ee (i 1) + (ee (i 2) + ee (i 3))) =
      γ (ee (i 0) + ee (i 1)) + γ (ee (i 2) + ee (i 3)) := by
  have hy : ∀ {j k : Fin 5}, j ≠ k → ∀ c : K, c ≠ 0 →
      ee (i j) + c • ee (i k) ≠ 0 ∧ herm frob (ee (i j) + c • ee (i k)) (ee (i j) + c • ee (i k))
        = 0 := fun {j k} hjk c hc => by
    have hne : i j ≠ i k := i.injective.ne hjk
    refine ⟨fun h => ?_, ?_⟩
    · have := congrFun h (i j)
      simp [hne] at this
    · have := isotropic_single_add_single hne hc
      rwa [← Pi.single_smul', smul_eq_mul, mul_one]
  obtain ⟨hy₁0, hy₁⟩ := hy (by decide : (3 : Fin 5) ≠ 4) ω omega_ne_zero
  obtain ⟨hy₂0, hy₂⟩ := hy (by decide : (3 : Fin 5) ≠ 4) 1 one_ne_zero
  obtain ⟨hy₃0, hy₃⟩ := hy (by decide : (1 : Fin 5) ≠ 2) 1 one_ne_zero
  obtain ⟨hy₄0, hy₄⟩ := hy (by decide : (1 : Fin 5) ≠ 2) ω omega_ne_zero
  obtain ⟨hy₅0, hy₅⟩ := hy (by decide : (0 : Fin 5) ≠ 1) ω omega_ne_zero
  rw [one_smul] at hy₂0 hy₂ hy₃0 hy₃
  have g0 := goodPair_std i
  have c1 := defect_tvv γ h2 hy₁0 hy₁ g0
  have g1 := g0.tvv hy₁
  have t1a : tvv (ee (i 3) + ω • ee (i 4)) (ee (i 0) + ee (i 1)) = ee (i 0) + ee (i 1) :=
    tvv_of_herm_eq_zero (by simp [herm_single_left])
  have t1b : tvv (ee (i 3) + ω • ee (i 4)) (ee (i 2) + ee (i 3)) = ee (i 2) + ω • ee (i 4) := by
    have hh : herm frob (ee (i 3) + ω • ee (i 4)) (ee (i 2) + ee (i 3)) = 1 := by
      simp [herm_single_left]
    rw [tvv, hh, one_smul, show ee (i 2) + ee (i 3) + (ee (i 3) + ω • ee (i 4)) =
      ee (i 2) + (ee (i 3) + ee (i 3)) + ω • ee (i 4) by abel, add_self_vec, add_zero]
  rw [t1a, t1b] at c1 g1
  have c2 := defect_tvv γ h2 hy₂0 hy₂ g1
  have g2 := g1.tvv hy₂
  have t2a : tvv (ee (i 3) + ee (i 4)) (ee (i 0) + ee (i 1)) = ee (i 0) + ee (i 1) :=
    tvv_of_herm_eq_zero (by simp [herm_single_left])
  have t2b : tvv (ee (i 3) + ee (i 4)) (ee (i 2) + ω • ee (i 4)) = ee (i 2) + ω • ee (i 3) := by
    have hh : herm frob (ee (i 3) + ee (i 4)) (ee (i 2) + ω • ee (i 4)) = ω := by
      simp [herm_single_left]
    rw [tvv, hh]
    funext j
    simp only [ee, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hj4 : j = i 4
    · subst hj4; simp [add_self_K]
    · by_cases hj3 : j = i 3
      · subst hj3; simp
      · simp [hj4, hj3]
  rw [t2a, t2b] at c2 g2
  have c3 := defect_tvv γ h2 hy₃0 hy₃ g2
  have g3 := g2.tvv hy₃
  have t3a : tvv (ee (i 1) + ee (i 2)) (ee (i 0) + ee (i 1)) = ee (i 0) + ee (i 2) := by
    have hh : herm frob (ee (i 1) + ee (i 2)) (ee (i 0) + ee (i 1)) = 1 := by
      simp [herm_single_left]
    rw [tvv, hh, one_smul, show ee (i 0) + ee (i 1) + (ee (i 1) + ee (i 2)) =
      ee (i 0) + (ee (i 1) + ee (i 1)) + ee (i 2) by abel, add_self_vec, add_zero]
  have t3b : tvv (ee (i 1) + ee (i 2)) (ee (i 2) + ω • ee (i 3)) = ee (i 1) + ω • ee (i 3) := by
    have hh : herm frob (ee (i 1) + ee (i 2)) (ee (i 2) + ω • ee (i 3)) = 1 := by
      simp [herm_single_left]
    rw [tvv, hh, one_smul, show ee (i 2) + ω • ee (i 3) + (ee (i 1) + ee (i 2)) =
      ee (i 1) + (ee (i 2) + ee (i 2)) + ω • ee (i 3) by abel, add_self_vec, add_zero]
  rw [t3a, t3b] at c3 g3
  have c4 := defect_tvv γ h2 hy₄0 hy₄ g3
  have g4 := g3.tvv hy₄
  have t4a : tvv (ee (i 1) + ω • ee (i 2)) (ee (i 0) + ee (i 2)) =
      ee (i 0) + (ω + 1) • ee (i 1) := by
    have hh : herm frob (ee (i 1) + ω • ee (i 2)) (ee (i 0) + ee (i 2)) = ω + 1 := by
      simp [herm_single_left, frobenius_omega]
    rw [tvv, hh]
    funext j
    simp only [ee, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hj0 : j = i 0
    · subst hj0; simp
    by_cases hj1 : j = i 1
    · subst hj1; simp [hj0]
    by_cases hj2 : j = i 2
    · subst hj2; simp [hj0, hj1]
      linear_combination omega_mul_omega + (1 + ω) * one_add_one_K
    · simp [hj0, hj1, hj2]
  have t4b : tvv (ee (i 1) + ω • ee (i 2)) (ee (i 1) + ω • ee (i 3)) =
      ω • ee (i 2) + ω • ee (i 3) := by
    have hh : herm frob (ee (i 1) + ω • ee (i 2)) (ee (i 1) + ω • ee (i 3)) = 1 := by
      simp [herm_single_left]
    rw [tvv, hh, one_smul, show ee (i 1) + ω • ee (i 3) + (ee (i 1) + ω • ee (i 2)) =
      (ee (i 1) + ee (i 1)) + ω • ee (i 2) + ω • ee (i 3) by abel, add_self_vec, zero_add]
  rw [t4a, t4b] at c4 g4
  have c5 := defect_tvv γ h2 hy₅0 hy₅ g4
  have t5a : tvv (ee (i 0) + ω • ee (i 1)) (ee (i 0) + (ω + 1) • ee (i 1)) =
      ω • (ee (i 0) + ee (i 1)) := by
    have hh : herm frob (ee (i 0) + ω • ee (i 1)) (ee (i 0) + (ω + 1) • ee (i 1)) = 1 + ω := by
      simp [herm_single_left, frobenius_omega]
      linear_combination omega_mul_omega + one_add_one_K + ω * one_add_one_K
    rw [tvv, hh]
    funext j
    simp only [ee, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hj0 : j = i 0
    · subst hj0; simp; linear_combination one_add_one_K
    by_cases hj1 : j = i 1
    · subst hj1; simp [hj0]; linear_combination omega_mul_omega + (1 + ω) * one_add_one_K
    · simp [hj0, hj1]
  have t5b : tvv (ee (i 0) + ω • ee (i 1)) (ω • ee (i 2) + ω • ee (i 3)) =
      ω • ee (i 2) + ω • ee (i 3) :=
    tvv_of_herm_eq_zero (by simp [herm_single_left])
  rw [t5a, t5b] at c5
  obtain ⟨ha0, ha, hb0, hb, hab0, hab⟩ := g0
  have hscale : γ (ω • (ee (i 0) + ee (i 1)) + (ω • ee (i 2) + ω • ee (i 3))) -
      γ (ω • (ee (i 0) + ee (i 1))) - γ (ω • ee (i 2) + ω • ee (i 3)) =
      ω * (γ (ee (i 0) + ee (i 1) + (ee (i 2) + ee (i 3))) - γ (ee (i 0) + ee (i 1)) -
        γ (ee (i 2) + ee (i 3))) := by
    rw [← smul_add, ← smul_add, h1 _ hab0 hab ω omega_ne_zero, h1 _ ha0 ha ω omega_ne_zero,
      h1 _ hb0 hb ω omega_ne_zero]
    ring
  have hδ := c5.trans (c4.trans (c3.trans (c2.trans c1)))
  rw [hscale] at hδ
  have h3 : (1 - ω) * (γ (ee (i 0) + ee (i 1) + (ee (i 2) + ee (i 3))) - γ (ee (i 0) + ee (i 1)) -
      γ (ee (i 2) + ee (i 3))) = 0 := by
    linear_combination -hδ
  have hzero := (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 (Ne.symm omega_ne_one))
  linear_combination hzero

end Section

end CFSG.Fischer.Classification.LocalU

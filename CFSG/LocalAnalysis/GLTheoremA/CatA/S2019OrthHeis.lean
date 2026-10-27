module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

structure OrthHeisData (Q : QuadraticForm K W) where
  P₁ : HypPair Q
  P₂ : HypPair Q
  a : W
  orth : P₁.Orth P₂
  ha₁ : a ∈ P₁.perp
  ha₂ : a ∈ P₂.perp
  hQa : Q a ≠ 0

namespace OrthHeisData

variable (D : OrthHeisData Q)

@[expose] noncomputable def eA (s : K) : W ≃ₗ[K] W := eichler Q D.P₁.e (s • D.a)

@[expose] noncomputable def eB (t : K) : W ≃ₗ[K] W := eichler Q D.P₂.e (t • D.a)

@[expose] noncomputable def eC (c : K) : W ≃ₗ[K] W := eichler Q D.P₁.e (c • D.P₂.e)

@[expose] noncomputable def elt (s t c : K) : W ≃ₗ[K] W := D.eA s * D.eB t * D.eC c

@[expose] noncomputable def γ : K := polar Q D.a D.a

theorem polar_e₁_a : polar Q D.P₁.e D.a = 0 := (HypPair.mem_perp.1 D.ha₁).1
theorem polar_f₁_a : polar Q D.P₁.f D.a = 0 := (HypPair.mem_perp.1 D.ha₁).2
theorem polar_e₂_a : polar Q D.P₂.e D.a = 0 := (HypPair.mem_perp.1 D.ha₂).1
theorem polar_f₂_a : polar Q D.P₂.f D.a = 0 := (HypPair.mem_perp.1 D.ha₂).2
theorem polar_a_e₁ : polar Q D.a D.P₁.e = 0 := by rw [polar_comm]; exact D.polar_e₁_a
theorem polar_a_e₂ : polar Q D.a D.P₂.e = 0 := by rw [polar_comm]; exact D.polar_e₂_a
theorem polar_a_f₂ : polar Q D.a D.P₂.f = 0 := by rw [polar_comm]; exact D.polar_f₂_a

private theorem pe₁ (s : K) : polar Q D.P₁.e (s • D.a) = 0 := by
  rw [polar_smul_right_eq, D.polar_e₁_a, mul_zero]

private theorem pe₂ (t : K) : polar Q D.P₂.e (t • D.a) = 0 := by
  rw [polar_smul_right_eq, D.polar_e₂_a, mul_zero]

private theorem pe₁₂ (c : K) : polar Q D.P₁.e (c • D.P₂.e) = 0 := by
  rw [polar_smul_right_eq, D.orth.ee, mul_zero]

theorem eA_add (s s' : K) : D.eA (s + s') = D.eA s * D.eA s' := by
  rw [eA, eA, eA, eichler_mul (D.pe₁ s) (D.pe₁ s'), add_smul]

theorem eB_add (t t' : K) : D.eB (t + t') = D.eB t * D.eB t' := by
  rw [eB, eB, eB, eichler_mul (D.pe₂ t) (D.pe₂ t'), add_smul]

theorem eC_add (c c' : K) : D.eC (c + c') = D.eC c * D.eC c' := by
  rw [eC, eC, eC, eichler_mul (D.pe₁₂ c) (D.pe₁₂ c'), add_smul]

theorem eA_zero : D.eA 0 = 1 := by rw [eA, zero_smul, eichler_zero_right]
theorem eB_zero : D.eB 0 = 1 := by rw [eB, zero_smul, eichler_zero_right]
theorem eC_zero : D.eC 0 = 1 := by rw [eC, zero_smul, eichler_zero_right]

theorem eA_eC_comm (s c : K) : D.eA s * D.eC c = D.eC c * D.eA s := by
  rw [eA, eC, eichler_mul (D.pe₁ s) (D.pe₁₂ c), eichler_mul (D.pe₁₂ c) (D.pe₁ s), add_comm]

private theorem eichler_symm {u w : W} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hw, polar_neg_right, QuadraticMap.map_neg, hu]
  module

theorem eC_eq (c : K) : D.eC c = eichler Q D.P₂.e (c • (-D.P₁.e)) := by
  rw [eC, eichler_symm D.P₁.Q_e (by rw [map_smul_eq_sq, D.P₂.Q_e, mul_zero]) (D.pe₁₂ c),
    eichler_smul_left, smul_neg]

private theorem pe₂₁ (c : K) : polar Q D.P₂.e (c • (-D.P₁.e)) = 0 := by
  rw [polar_smul_right_eq, polar_neg_right, polar_comm, D.orth.ee, neg_zero, mul_zero]

theorem eB_eC_comm (t c : K) : D.eB t * D.eC c = D.eC c * D.eB t := by
  rw [eC_eq, eB, eichler_mul (D.pe₂ t) (D.pe₂₁ c), eichler_mul (D.pe₂₁ c) (D.pe₂ t), add_comm]

private theorem eA_e₂ (s : K) : D.eA s D.P₂.e = D.P₂.e := by
  rw [eA]
  refine eichler_apply_of_polar_eq_zero ?_ ?_
  · rw [polar_comm]; exact D.orth.ee
  · rw [polar_smul_right_eq, D.polar_e₂_a, mul_zero]

private theorem eB_e₁ (t : K) : D.eB t D.P₁.e = D.P₁.e := by
  rw [eB]
  refine eichler_apply_of_polar_eq_zero D.orth.ee ?_
  rw [polar_smul_right_eq, D.polar_e₁_a, mul_zero]

private theorem eA_a (s t : K) : D.eA s (t • D.a) = t • D.a + (-(D.γ * s * t)) • D.P₁.e := by
  rw [eA, eichler_apply D.P₁.Q_e (D.pe₁ s), polar_smul_left_eq, polar_comm, D.polar_e₁_a,
    polar_smul_left_eq, polar_smul_right_eq, OrthHeisData.γ]
  simp only [mul_zero, zero_smul, add_zero, zero_mul]
  module

private theorem eB_a (s t : K) : D.eB t (s • D.a) = s • D.a + (-(D.γ * s * t)) • D.P₂.e := by
  rw [eB, eichler_apply D.P₂.Q_e (D.pe₂ t), polar_smul_left_eq, polar_comm, D.polar_e₂_a,
    polar_smul_left_eq, polar_smul_right_eq, OrthHeisData.γ]
  simp only [mul_zero, zero_smul, add_zero, zero_mul]
  module

theorem eB_mem (t : K) : D.eB t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  eichler_mem_orthogonalGroup Q _ _

theorem eB_conj_eA (s t : K) : D.eB t * D.eA s * (D.eB t)⁻¹ = D.eA s * D.eC (-(D.γ * s * t)) := by
  have h1 := eichler_conj (D.eB_mem t) D.P₁.e (s • D.a)
  rw [eA, h1, D.eB_e₁, D.eB_a, ← eichler_mul (D.pe₁ s) (D.pe₁₂ _), eC]

private theorem eB_eA (s t : K) : D.eB t * D.eA s = D.eA s * D.eC (-(D.γ * s * t)) * D.eB t := by
  rw [← D.eB_conj_eA, inv_mul_cancel_right]

theorem elt_mul (s t c s' t' c' : K) :
    D.elt s t c * D.elt s' t' c' = D.elt (s + s') (t + t') (c + c' - D.γ * s' * t) := by
  have hCA : ∀ (c₀ s₀ : K) (z : W ≃ₗ[K] W), D.eC c₀ * (D.eA s₀ * z) = D.eA s₀ * (D.eC c₀ * z) :=
    fun c₀ s₀ z => by rw [← mul_assoc, ← D.eA_eC_comm, mul_assoc]
  have hCB : ∀ (c₀ t₀ : K) (z : W ≃ₗ[K] W), D.eC c₀ * (D.eB t₀ * z) = D.eB t₀ * (D.eC c₀ * z) :=
    fun c₀ t₀ z => by rw [← mul_assoc, ← D.eB_eC_comm, mul_assoc]
  have hBA : ∀ (t₀ s₀ : K) (z : W ≃ₗ[K] W),
      D.eB t₀ * (D.eA s₀ * z) = D.eA s₀ * (D.eC (-(D.γ * s₀ * t₀)) * (D.eB t₀ * z)) :=
    fun t₀ s₀ z => by rw [← mul_assoc, D.eB_eA, mul_assoc, mul_assoc]
  have hCs : D.eC (c + c' - D.γ * (s' * t)) = D.eC (-(D.γ * (s' * t))) * (D.eC c * D.eC c') := by
    rw [← D.eC_add, ← D.eC_add]
    congr 1
    ring
  simp only [elt, mul_assoc]
  rw [hCA c s', hBA t s', hCB c t', hCB (-(D.γ * s' * t)) t, hCB (-(D.γ * s' * t)) t',
    D.eA_add, D.eB_add, hCs]
  simp only [mul_assoc]

theorem elt_zero : D.elt 0 0 0 = 1 := by rw [elt, D.eA_zero, D.eB_zero, D.eC_zero, mul_one, mul_one]

theorem elt_inv (s t c : K) : (D.elt s t c)⁻¹ = D.elt (-s) (-t) (-c - D.γ * s * t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [D.elt_mul, add_neg_cancel, add_neg_cancel, ← D.elt_zero]
  congr 1
  ring

@[expose] noncomputable def heisGroupO : Subgroup (W ≃ₗ[K] W) where
  carrier := {g | ∃ s t c : K, g = D.elt s t c}
  one_mem' := ⟨0, 0, 0, D.elt_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, t, c, rfl⟩ ⟨s', t', c', rfl⟩
    exact ⟨_, _, _, D.elt_mul s t c s' t' c'⟩
  inv_mem' := by
    rintro _ ⟨s, t, c, rfl⟩
    exact ⟨_, _, _, D.elt_inv s t c⟩

theorem eC_sub_one_sq (c : K) : (((D.eC c : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) ^ 2 = 0 := by
  have hQw : Q (c • D.P₂.e) = 0 := by rw [map_smul_eq_sq, D.P₂.Q_e, mul_zero]
  have hN : ∀ y, (((D.eC c : W ≃ₗ[K] W) : W →ₗ[K] W) - 1) y =
      polar Q y D.P₁.e • (c • D.P₂.e) - polar Q y (c • D.P₂.e) • D.P₁.e := by
    intro y
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, eC,
      eichler_apply D.P₁.Q_e (D.pe₁₂ c), hQw, zero_mul, add_zero]
    abel
  refine LinearMap.ext fun y => ?_
  rw [pow_two, Module.End.mul_apply, hN y, hN, LinearMap.zero_apply]
  simp only [polar_sub_left, polar_smul_left_eq, polar_smul_right_eq, polar_self_eq_zero D.P₁.Q_e,
    polar_self_eq_zero D.P₂.Q_e, D.orth.ee, polar_comm Q D.P₂.e D.P₁.e]
  simp

private theorem polar_elt_f₁ (s t : K) : polar Q (D.elt s t 0 D.P₁.f) D.a = D.γ * s := by
  have hBf : D.eB t D.P₁.f = D.P₁.f := by
    rw [eB]
    refine eichler_apply_of_polar_eq_zero D.orth.fe ?_
    rw [polar_smul_right_eq, D.polar_f₁_a, mul_zero]
  rw [elt, D.eC_zero, mul_one, LinearEquiv.mul_apply, hBf, eA,
    eichler_apply D.P₁.Q_e (D.pe₁ s)]
  simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, polar_smul_right_eq,
    D.P₁.polar_fe, D.polar_f₁_a, D.polar_a_e₁, D.polar_e₁_a, OrthHeisData.γ]
  ring

private theorem polar_elt_f₂ (s t : K) : polar Q (D.elt s t 0 D.P₂.f) D.a = D.γ * t := by
  have hAf : D.eA s D.P₂.f = D.P₂.f := by
    rw [eA]
    refine eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact D.orth.ef) ?_
    rw [polar_smul_right_eq, D.polar_f₂_a, mul_zero]
  have hBf : D.eB t D.P₂.f = D.P₂.f + t • D.a - (Q (t • D.a)) • D.P₂.e := by
    rw [eB, eichler_apply D.P₂.Q_e (D.pe₂ t), D.P₂.polar_fe, polar_smul_right_eq, D.polar_f₂_a]
    simp
  rw [elt, D.eC_zero, mul_one, LinearEquiv.mul_apply, hBf, map_sub, map_add, map_smul, hAf,
    map_smul, D.eA_e₂]
  have hAa : D.eA s D.a = D.a + (-(D.γ * s * 1)) • D.P₁.e := by
    have := D.eA_a s 1
    rwa [one_smul] at this
  rw [hAa]
  simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, D.polar_a_f₂,
    D.polar_f₂_a, D.polar_a_e₁, D.polar_e₁_a, D.polar_a_e₂, D.polar_e₂_a, OrthHeisData.γ]
  ring

theorem elt_injective (hγ : D.γ ≠ 0) {s t s' t' : K} (h : D.elt s t 0 = D.elt s' t' 0) :
    s = s' ∧ t = t' := by
  have h1 := D.polar_elt_f₁ s t
  have h2 := D.polar_elt_f₂ s t
  rw [h, D.polar_elt_f₁] at h1
  rw [h, D.polar_elt_f₂] at h2
  exact ⟨(mul_left_cancel₀ hγ h1).symm, (mul_left_cancel₀ hγ h2).symm⟩

theorem eC_injective {c c' : K} (h : D.eC c = D.eC c') : c = c' := by
  have h1 := congrArg (fun g : W ≃ₗ[K] W => polar Q (g D.P₁.f) D.P₂.f) h
  simp only [eC] at h1
  rw [eichler_apply D.P₁.Q_e (D.pe₁₂ c), eichler_apply D.P₁.Q_e (D.pe₁₂ c')] at h1
  simp only [polar_add_left, polar_sub_left, polar_smul_left_eq, polar_smul_right_eq,
    D.P₁.polar_fe, D.P₂.polar_ef, D.orth.ff, D.orth.ef, polar_comm Q D.P₁.f D.P₂.e,
    D.orth.fe, polar_self_eq_zero D.P₂.Q_e, D.P₂.Q_e, map_smul_eq_sq] at h1
  linear_combination h1

theorem elt_pow_three [CharP K 3] (s t c : K) : D.elt s t c ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [pow_succ, pow_two, D.elt_mul, D.elt_mul, ← D.elt_zero]
  congr 1
  · linear_combination s * h3
  · linear_combination t * h3
  · linear_combination (c - D.γ * s * t) * h3

theorem eq_eC_of_central (hγ : D.γ ≠ 0) {s t c : K}
    (h : ∀ w ∈ D.heisGroupO, D.elt s t c * w = w * D.elt s t c) : D.elt s t c = D.eC c := by
  have hB := h (D.elt 0 1 0) ⟨0, 1, 0, rfl⟩
  have hA := h (D.elt 1 0 0) ⟨1, 0, 0, rfl⟩
  rw [D.elt_mul, D.elt_mul] at hB hA
  have hs : s = 0 := by
    have e1 : D.elt (s + 0) (t + 1) (c + 0 - D.γ * 0 * t) =
        D.elt (0 + s) (1 + t) (0 + c - D.γ * s * 1) := hB
    simp only [elt, add_zero, zero_add, mul_zero, zero_mul, sub_zero, mul_one] at e1
    rw [add_comm 1 t] at e1
    have e2 := D.eC_injective (mul_left_cancel e1)
    have : D.γ * s = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_left hγ
  have ht : t = 0 := by
    have e1 : D.elt (s + 1) (t + 0) (c + 0 - D.γ * 1 * t) =
        D.elt (1 + s) (0 + t) (0 + c - D.γ * s * 0) := hA
    simp only [elt, add_zero, zero_add, mul_zero, sub_zero, mul_one] at e1
    rw [add_comm 1 s] at e1
    have e2 := D.eC_injective (mul_left_cancel e1)
    have : D.γ * t = 0 := by linear_combination -e2
    exact (mul_eq_zero.1 this).resolve_left hγ
  rw [hs, ht, elt, D.eA_zero, D.eB_zero, one_mul, one_mul]

end OrthHeisData

end CFSG.LocalAnalysis.GLTheoremA.S2019

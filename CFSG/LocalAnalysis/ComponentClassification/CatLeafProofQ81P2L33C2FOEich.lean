module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2LWit

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_sub_apply {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (z : V) : eichler Q u w z - z = polar Q z u • w - polar Q z w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero]
  abel

theorem eichler_pair_pow_three [CharP K 2] {x₁ y₁ x₂ y₂ : V} (hx₁ : Q x₁ = 0)
    (hx₂ : Q x₂ = 0) (hy₁ : Q y₁ = 0) (hy₂ : Q y₂ = 0) (h11 : polar Q x₁ y₁ = 0)
    (h22 : polar Q x₂ y₂ = 0) (hxx : polar Q x₁ x₂ = 0) (hyy : polar Q y₁ y₂ = 0)
    (h12 : polar Q x₁ y₂ = 1) (h21 : polar Q x₂ y₁ = 1) :
    (eichler Q x₁ y₁ * eichler Q x₂ y₂) ^ 3 = 1 ∧ eichler Q x₁ y₁ * eichler Q x₂ y₂ ≠ 1 := by
  have e₁ : polar Q x₁ x₁ = 0 := polar_self_eq_zero hx₁
  have e₂ : polar Q x₂ x₂ = 0 := polar_self_eq_zero hx₂
  have e₃ : polar Q y₁ y₁ = 0 := polar_self_eq_zero hy₁
  have e₄ : polar Q y₂ y₂ = 0 := polar_self_eq_zero hy₂
  have e₅ : polar Q y₁ x₁ = 0 := by rw [polar_comm, h11]
  have e₆ : polar Q y₂ x₂ = 0 := by rw [polar_comm, h22]
  have e₇ : polar Q x₂ x₁ = 0 := by rw [polar_comm, hxx]
  have e₈ : polar Q y₂ y₁ = 0 := by rw [polar_comm, hyy]
  have e₉ : polar Q y₂ x₁ = 1 := by rw [polar_comm, h12]
  have e₁₀ : polar Q y₁ x₂ = 1 := by rw [polar_comm, h21]
  obtain ⟨a, ha⟩ : ∃ a : Module.End K V, a = (eichler Q x₁ y₁ : Module.End K V) - 1 :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Module.End K V, b = (eichler Q x₂ y₂ : Module.End K V) - 1 :=
    ⟨_, rfl⟩
  have haz : ∀ z, a z = polar Q z x₁ • y₁ - polar Q z y₁ • x₁ := fun z => by
    rw [ha, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_sub_apply hx₁ hy₁ h11]
  have hbz : ∀ z, b z = polar Q z x₂ • y₂ - polar Q z y₂ • x₂ := fun z => by
    rw [hb, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      eichler_sub_apply hx₂ hy₂ h22]
  have hadd : ∀ f : Module.End K V, f + f = 0 := fun f => by
    ext z
    rw [LinearMap.add_apply, ← two_smul K (f z), CharTwo.two_eq_zero, zero_smul,
      LinearMap.zero_apply]
  have haa : a * a = 0 := by
    ext z
    simp only [Module.End.mul_apply, haz, polar_sub_left, polar_smul_left, smul_eq_mul, e₁, e₃,
      e₅, h11, mul_zero, sub_zero, zero_smul, LinearMap.zero_apply]
  have hbb : b * b = 0 := by
    ext z
    simp only [Module.End.mul_apply, hbz, polar_sub_left, polar_smul_left, smul_eq_mul, e₂, e₄,
      e₆, h22, mul_zero, sub_zero, zero_smul, LinearMap.zero_apply]
  have hba : ∀ z, b (a z) = polar Q z x₁ • y₂ + polar Q z y₁ • x₂ := fun z => by
    rw [haz, hbz]
    simp only [polar_sub_left, polar_smul_left, smul_eq_mul, e₁₀, hxx, hyy, h12]
    module
  have hab : ∀ z, a (b z) = polar Q z x₂ • y₁ + polar Q z y₂ • x₁ := fun z => by
    rw [hbz, haz]
    simp only [polar_sub_left, polar_smul_left, smul_eq_mul, e₉, e₇, e₈, h21]
    module
  have haba : a * b * a = a := by
    ext z
    rw [Module.End.mul_apply, Module.End.mul_apply, hba, haz, haz]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, e₉, e₇, e₈, h21]
    module
  have hbab : b * a * b = b := by
    ext z
    rw [Module.End.mul_apply, Module.End.mul_apply, hab, hbz, hbz]
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, e₁₀, hxx, hyy, h12]
    module
  have hE₁ : (eichler Q x₁ y₁ : Module.End K V) = 1 + a := by rw [ha, add_sub_cancel]
  have hE₂ : (eichler Q x₂ y₂ : Module.End K V) = 1 + b := by rw [hb, add_sub_cancel]
  set φ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V) with hφ
  have hφg : φ (eichler Q x₁ y₁ * eichler Q x₂ y₂) = (1 + a) * (1 + b) := by
    rw [map_mul, ← hE₁, ← hE₂]
    rfl
  have hinj : Function.Injective φ := fun g g' hgg' =>
    LinearEquiv.toLinearMap_injective hgg'
  refine ⟨hinj ?_, fun h1 => ?_⟩
  · rw [map_pow, hφg, map_one]
    exact pow_three_of_rel hadd haa hbb haba hbab
  · have h1' : (1 + a) * (1 + b) = 1 := by rw [← hφg, h1, map_one]
    have hab : a = b := by
      have h2 : (1 + a) * ((1 + a) * (1 + b)) = 1 + a := by rw [h1', mul_one]
      rw [← mul_assoc, show (1 + a) * (1 + a) = 1 + (a + a) + a * a by noncomm_ring, hadd,
        haa, add_zero, add_zero, one_mul] at h2
      exact (add_left_cancel h2).symm
    have ha0 : a = 0 := by rw [← haba, ← hab, haa, zero_mul]
    have hy₁0 : y₁ ≠ 0 := fun h0 => by
      rw [h0, polar_zero_right] at h21
      exact zero_ne_one h21
    apply hy₁0
    have h3 := congrArg (fun f : Module.End K V => f y₂) ha0
    simp only [haz, e₉, e₈, one_smul, zero_smul, sub_zero, LinearMap.zero_apply] at h3
    exact h3

theorem eichler_comm_self [CharP K 2] {N : V →ₗ[K] V}
    (hN : ∀ u v, polar Q (N u) v = polar Q u (N v)) (hNN : ∀ v, N (N v) = 0) {x : V}
    (hx : Q x = 0) (hNx : Q (N x) = 0) (hxN : polar Q x (N x) = 0) (z : V) :
    eichler Q x (N x) (N z) = N (eichler Q x (N x) z) := by
  have h2 : ∀ w : V, -w = w := fun w => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul K w, CharTwo.two_eq_zero, zero_smul]
  rw [eichler_apply hx hxN, eichler_apply hx hxN, hNx]
  simp only [zero_mul, add_zero, map_add, map_sub, map_smul, hNN, smul_zero, hN z x, hN z (N x),
    polar_zero_right, zero_smul, sub_zero]
  rw [sub_eq_add_neg, h2]

theorem eichler_comm_ker {N : V →ₗ[K] V} (hN : ∀ u v, polar Q (N u) v = polar Q u (N v))
    {u w : V} (hu : N u = 0) (hw : N w = 0) (z : V) :
    eichler Q u w (N z) = N (eichler Q u w z) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · simp only [eichler_apply h.1 h.2, map_add, map_sub, map_smul, hu, hw, hN z u, hN z w,
      polar_zero_right, mul_zero, add_zero, zero_smul, smul_zero, sub_zero]
  · rw [eichler_of_not h]
    rfl

end CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo

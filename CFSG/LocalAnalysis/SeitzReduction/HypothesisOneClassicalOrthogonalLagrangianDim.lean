module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalOrthogonalLagrangianCore

public section

namespace CFSG.SeitzReduction

namespace OrthogonalLagrangian

open Module QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_le_finrank_add_one_of_sq [FiniteDimensional K V] [CharP K 2]
    (hsq : ∀ a : K, IsSquare a)
    {S P : Submodule K V} (f : V → K) (hf0 : ∀ x ∈ S, f x = 0 → x ∈ P)
    (hfadd : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y)
    (hfsmul : ∀ (a : K) x, x ∈ S → f (a • x) = a * a * f x) :
    finrank K S ≤ finrank K P + 1 := by
  by_cases h : ∀ x ∈ S, f x = 0
  · have hle : S ≤ P := fun x hx => hf0 x hx (h x hx)
    exact (Submodule.finrank_mono hle).trans (Nat.le_succ _)
  · push Not at h
    obtain ⟨x₁, hx₁, hfx₁⟩ := h
    have hle : S ≤ P ⊔ K ∙ x₁ := by
      intro x hx
      obtain ⟨t, ht⟩ := hsq (f x / f x₁)
      have hmem : x + (-t) • x₁ ∈ P := by
        refine hf0 _ (S.add_mem hx (S.smul_mem _ hx₁)) ?_
        rw [hfadd _ hx _ (S.smul_mem _ hx₁), hfsmul _ _ hx₁, neg_mul_neg, ← ht,
          div_mul_cancel₀ _ hfx₁, CharTwo.add_self_eq_zero]
      refine Submodule.mem_sup.mpr ⟨_, hmem, t • x₁,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₁), ?_⟩
      rw [neg_smul, neg_add_cancel_right]
    calc finrank K S ≤ finrank K ↥(P ⊔ K ∙ x₁) := Submodule.finrank_mono hle
      _ ≤ finrank K P + finrank K (K ∙ x₁) := Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ finrank K P + 1 := by
        gcongr
        exact (finrank_span_le_card ({x₁} : Set V)).trans (by simp)

variable {Q : QuadraticForm K V} {N : V →ₗ[K] V}

namespace IsLagrangianDisplacement

variable (hL : IsLagrangianDisplacement Q N)
include hL

theorem range_eq_ker : LinearMap.range N = LinearMap.ker N := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact LinearMap.mem_ker.mpr (hL.sq y)
  · intro x hx
    obtain ⟨y, hy⟩ := hL.ker_le x (LinearMap.mem_ker.mp hx)
    exact ⟨y, hy⟩

theorem finrank_eq_two_mul [FiniteDimensional K V] :
    finrank K V = 2 * finrank K (LinearMap.ker N) := by
  have h := LinearMap.finrank_range_add_finrank_ker N
  rw [hL.range_eq_ker] at h
  omega

@[expose] def singularPart : Submodule K V where
  carrier := {x | N x = 0 ∧ Q x = 0}
  add_mem' {x y} hx hy := ⟨by rw [map_add, hx.1, hy.1, add_zero],
    by rw [hL.map_add_of_ker hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨map_zero N, QuadraticMap.map_zero Q⟩
  smul_mem' a x hx := ⟨by rw [map_smul, hx.1, smul_zero],
    by rw [QuadraticMap.map_smul, hx.2, smul_zero]⟩

theorem mem_singularPart {x : V} : x ∈ hL.singularPart ↔ N x = 0 ∧ Q x = 0 := Iff.rfl

@[expose] def singularPreimage : Submodule K V where
  carrier := {y | Q (N y) = 0}
  add_mem' {x y} hx hy := by
    change Q (N (x + y)) = 0
    rw [map_add, hL.map_add_of_ker (hL.sq x) (hL.sq y), hx, hy, add_zero]
  zero_mem' := by
    change Q (N 0) = 0
    rw [map_zero, QuadraticMap.map_zero]
  smul_mem' a x hx := by
    change Q (N (a • x)) = 0
    rw [map_smul, QuadraticMap.map_smul, hx, smul_zero]

theorem mem_singularPreimage {y : V} : y ∈ hL.singularPreimage ↔ Q (N y) = 0 := Iff.rfl

theorem finrank_ker_le [FiniteDimensional K V] [CharP K 2] (hsq : ∀ a : K, IsSquare a) :
    finrank K (LinearMap.ker N) ≤ finrank K hL.singularPart + 1 :=
  finrank_le_finrank_add_one_of_sq hsq Q (fun x hx h => ⟨LinearMap.mem_ker.mp hx, h⟩)
    (fun x hx y hy => hL.map_add_of_ker (LinearMap.mem_ker.mp hx) (LinearMap.mem_ker.mp hy))
    (fun a x _ => by rw [QuadraticMap.map_smul, smul_eq_mul])

theorem finrank_le_singularPreimage [FiniteDimensional K V] [CharP K 2]
    (hsq : ∀ a : K, IsSquare a) :
    finrank K V ≤ finrank K hL.singularPreimage + 1 := by
  have h := finrank_le_finrank_add_one_of_sq hsq (S := ⊤) (P := hL.singularPreimage)
    (fun y => Q (N y)) (fun x _ h => h)
    (fun x _ y _ => by rw [map_add, hL.map_add_of_ker (hL.sq x) (hL.sq y)])
    (fun a x _ => by rw [map_smul, QuadraticMap.map_smul, smul_eq_mul])
  rwa [finrank_top] at h

theorem exists_second_partner [FiniteDimensional K V] [CharP K 2] (hsq : ∀ a : K, IsSquare a)
    (hdim : 8 ≤ finrank K V) {u v : V} (hu : Q (N u) = 0) (huv : polar Q u (N v) = 1) :
    ∃ z, Q (N z) = 0 ∧ polar Q u (N z) = 0 ∧ N z ∉ Submodule.span K {N u, N v} := by
  set f : V →ₗ[K] K := (polarBilin Q).flip u with hf
  have hfx : ∀ x, f x = polar Q x u := fun x => rfl
  set S := hL.singularPart ⊓ LinearMap.ker f with hS
  have hker : finrank K V ≤ finrank K (LinearMap.ker f) + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : finrank K (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      rwa [finrank_self] at this
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq hL.singularPart (LinearMap.ker f)
  have hsup := Submodule.finrank_le (hL.singularPart ⊔ LinearMap.ker f)
  have hW := hL.finrank_ker_le hsq
  have h2m := hL.finrank_eq_two_mul
  have hS2 : 2 ≤ finrank K S := by rw [hS]; omega
  by_contra hcon
  push Not at hcon
  have hle : S ≤ K ∙ N u := by
    intro x hx
    by_contra hxu
    obtain ⟨y, hy⟩ := hL.ker_le x (Submodule.mem_inf.mp hx).1.1
    have hyH : Q (N y) = 0 := by rw [hy]; exact (Submodule.mem_inf.mp hx).1.2
    have hyu : polar Q u (N y) = 0 := by
      rw [polar_comm, hy, ← hfx]
      exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
    have hspan := hcon y hyH hyu
    rw [hy, Submodule.mem_span_pair] at hspan
    obtain ⟨a, b, hab⟩ := hspan
    have hb : b = 0 := by
      have e := congrArg (fun x => polar Q x u) hab
      simp only [polar_add_left, polar_smul_left, smul_eq_mul] at e
      rw [hL.polar_N_self, hu, polar_comm Q (N v) u, huv, mul_zero, zero_add, mul_one] at e
      rw [e, ← hfx]
      exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
    rw [hb, zero_smul, add_zero] at hab
    exact hxu (hab ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _))
  have h1 : finrank K S ≤ 1 :=
    (Submodule.finrank_mono hle).trans ((finrank_span_le_card ({N u} : Set V)).trans (by simp))
  omega

theorem exists_hyperbolic_pair [FiniteDimensional K V] [CharP K 2] (hsq : ∀ a : K, IsSquare a)
    (hnd : (polarBilin Q).Nondegenerate) (hdim : 8 ≤ finrank K V) :
    ∃ u v, Q (N u) = 0 ∧ Q (N v) = 0 ∧ polar Q u (N v) = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 0 := by
    intro u v hu hv
    by_contra hne
    refine hcon u ((polar Q u (N v))⁻¹ • v) hu ?_ ?_
    · rw [map_smul, QuadraticMap.map_smul, hv, smul_zero]
    · rw [map_smul, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hne]
  have hle : hL.singularPart ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) hL.singularPreimage := by
    intro x hx
    obtain ⟨v, rfl⟩ := hL.ker_le x hx.1
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact h0 y v hy hx.2
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
  have h2 := hL.finrank_le_singularPreimage hsq
  have h3 := hL.finrank_ker_le hsq
  have h4 := hL.finrank_eq_two_mul
  omega

end IsLagrangianDisplacement

theorem semilinear_lagrangian_rigidity_of_finrank [FiniteDimensional K V] [CharP K 2]
    (hsq : ∀ a : K, IsSquare a)
    (hnd : (polarBilin Q).Nondegenerate) (hdim : 8 ≤ finrank K V)
    (hL : IsLagrangianDisplacement Q N) {φ : K ≃+* K} (T : V ≃+ V)
    (hTs : ∀ (a : K) x, T (a • x) = φ a • T x) (hTQ : ∀ x, Q (T x) = φ (Q x))
    (hTN : ∀ x, T (N x) = N (T x))
    (hG1 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 1 →
      ∀ x, T (leviPair Q N u v x) = leviPair Q N u v (T x))
    (hG2 : ∀ u v, Q (N u) = 0 → Q (N v) = 0 → polar Q u (N v) = 1 → ∀ w, N w = 0 →
      ∀ x, T ((CFSG.ClassicalGroups.Orthogonal.eichler Q (N v) w * leviPair Q N u v *
          (CFSG.ClassicalGroups.Orthogonal.eichler Q (N v) w)⁻¹) x) =
        (CFSG.ClassicalGroups.Orthogonal.eichler Q (N v) w * leviPair Q N u v *
          (CFSG.ClassicalGroups.Orthogonal.eichler Q (N v) w)⁻¹) (T x)) :
    (∀ a, φ a = a) ∧ ∀ x, T (T x) = x :=
  semilinear_lagrangian_rigidity hL
    (fun _ _ hu _ huv => hL.exists_second_partner hsq hdim hu huv)
    (hL.exists_hyperbolic_pair hsq hnd hdim) T hTs hTQ hTN hG1 hG2

end OrthogonalLagrangian

end CFSG.SeitzReduction

module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussBasis

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {g : V ≃ₗ[F] V}

namespace AB

variable (ab : AdaptedBasis Q g 4)

@[expose] noncomputable def x0 (k l : Fin 4) : V :=
  ab.basis (.inl k) + ab.basis (.inl l) + ab.basis (.inr l)

@[expose] noncomputable def x1 (k l : Fin 4) : V :=
  ab.basis (.inr k) + ab.basis (.inr l) - ab.basis (.inl l)

@[expose] noncomputable def gen : Fin 4 → V := ![x0 ab 0 1, x1 ab 0 1, x0 ab 2 3, x1 ab 2 3]

@[expose] noncomputable def dual : Fin 4 → V :=
  ![ab.basis (.inl 0), ab.basis (.inr 0), ab.basis (.inl 2), ab.basis (.inr 2)]

@[expose] noncomputable def U₀ : Submodule F V := Submodule.span F (Set.range (gen ab))

theorem orth' (i j : Fin 4 ⊕ Fin 4) :
    polar Q (ab.basis i) (ab.basis j) = if i = j then 1 else 0 := ab.orth i j

theorem polar_gen_dual (i j : Fin 4) :
    polar Q (gen ab i) (dual ab j) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [gen, dual, x0, x1, polar_add_left, polar_sub_left, orth', -polar_self]

theorem polar_gen_gen (h3 : (3 : F) = 0) (i j : Fin 4) : polar Q (gen ab i) (gen ab j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [gen, x0, x1, polar_add_left, polar_sub_left, polar_add_right, polar_sub_right,
      orth', -polar_self] <;> linear_combination h3

theorem g_basis (hg2 : ∀ x, g (g x) = -x) (k : Fin 4) :
    g (ab.basis (.inl k)) = ab.basis (.inr k) ∧ g (ab.basis (.inr k)) = -ab.basis (.inl k) := by
  rw [ab.inr_eq]
  exact ⟨rfl, hg2 _⟩

theorem g_x0 (hg2 : ∀ x, g (g x) = -x) (k l : Fin 4) : g (x0 ab k l) = x1 ab k l := by
  rw [x0, x1, map_add, map_add, (g_basis ab hg2 k).1, (g_basis ab hg2 l).1, (g_basis ab hg2 l).2]
  abel

theorem g_x1 (hg2 : ∀ x, g (g x) = -x) (k l : Fin 4) : g (x1 ab k l) = -x0 ab k l := by
  rw [x0, x1, map_sub, map_add, (g_basis ab hg2 k).2, (g_basis ab hg2 l).1, (g_basis ab hg2 l).2]
  abel

theorem linearIndependent_gen : LinearIndependent F (gen ab) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h : polarBilin Q (∑ i, c i • gen ab i) (dual ab j) = 0 := by
    rw [hc, map_zero, LinearMap.zero_apply]
  rw [map_sum, LinearMap.sum_apply] at h
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, polar_gen_dual, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

theorem finrank_U₀ : Module.finrank F (U₀ ab) = 4 := by
  rw [U₀, finrank_span_eq_card (linearIndependent_gen ab)]
  simp

theorem U₀_singular (h3 : (3 : F) = 0) (h2 : (2 : F) ≠ 0) : ∀ v ∈ U₀ ab, Q v = 0 := by
  have hpol : ∀ v ∈ U₀ ab, ∀ i, polar Q v (gen ab i) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact polar_gen_gen ab h3 j
    | zero => exact fun i => by simp
    | add x y _ _ hx hy => exact fun i => by rw [polar_add_left, hx i, hy i, add_zero]
    | smul c x _ hx => exact fun i => by rw [polar_smul_left_eq, hx i, mul_zero]
  have hpol' : ∀ v ∈ U₀ ab, ∀ w ∈ U₀ ab, polar Q v w = 0 := by
    intro v hv w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hpol v hv j
    | zero => simp
    | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [polar_smul_right_eq, hx, mul_zero]
  intro v hv
  have h := hpol' v hv v hv
  rw [polar_self, two_smul] at h
  have : (2 : F) * Q v = 0 := by rw [two_mul]; exact h
  exact (mul_eq_zero.mp this).resolve_left h2

theorem map_U₀ (hg2 : ∀ x, g (g x) = -x) : (U₀ ab).map (g : V →ₗ[F] V) = U₀ ab := by
  have hmem : ∀ i, gen ab i ∈ U₀ ab := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hle : (U₀ ab).map (g : V →ₗ[F] V) ≤ U₀ ab := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    change g (gen ab j) ∈ U₀ ab
    fin_cases j
    · change g (x0 ab 0 1) ∈ U₀ ab
      rw [g_x0 ab hg2]
      exact hmem 1
    · change g (x1 ab 0 1) ∈ U₀ ab
      rw [g_x1 ab hg2]
      exact neg_mem (hmem 0)
    · change g (x0 ab 2 3) ∈ U₀ ab
      rw [g_x0 ab hg2]
      exact hmem 3
    · change g (x1 ab 2 3) ∈ U₀ ab
      rw [g_x1 ab hg2]
      exact neg_mem (hmem 2)
  have : FiniteDimensional F (U₀ ab) := FiniteDimensional.span_of_finite F (Set.finite_range _)
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

end AB

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviCore
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module
open LinearMap (BilinForm)

section Wall

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (B : LinearMap.BilinForm K V) (N : V →ₗ[K] V) (hadj : ∀ x y, B (N x) y = B x (N y))

include hadj in
theorem wall_vanish (u : LinearMap.range N) : LinearMap.ker N ≤ LinearMap.ker (B (u : V)) := by
  intro y hy
  obtain ⟨x, hx⟩ := u.2
  rw [LinearMap.mem_ker] at hy ⊢
  rw [← hx, hadj, hy, map_zero]

@[expose] noncomputable def wallForm : BilinForm K (LinearMap.range N) :=
  LinearMap.mk₂ K
    (fun u u' => (LinearMap.ker N).liftQ (B (u : V)) (wall_vanish B N hadj u)
      ((N.quotKerEquivRange).symm u'))
    (fun u₁ u₂ u' => by
      generalize (N.quotKerEquivRange).symm u' = q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      simp only [Submodule.liftQ_apply, Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c u u' => by
      generalize (N.quotKerEquivRange).symm u' = q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      simp only [Submodule.liftQ_apply, Submodule.coe_smul, map_smul, LinearMap.smul_apply])
    (fun u u₁ u₂ => by simp only [map_add])
    (fun c u u' => by simp only [map_smul])

theorem wallForm_apply (x y : V) :
    wallForm B N hadj ⟨N x, LinearMap.mem_range_self N x⟩ ⟨N y, LinearMap.mem_range_self N y⟩ =
      B (N x) y := by
  have he : (N.quotKerEquivRange).symm ⟨N y, LinearMap.mem_range_self N y⟩ =
      Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  simp only [wallForm, LinearMap.mk₂_apply, he, Submodule.liftQ_apply]

theorem wallForm_isAlt (hQN : ∀ x, B (N x) x = 0) : (wallForm B N hadj).IsAlt := by
  rintro ⟨_, x, rfl⟩
  exact (wallForm_apply B N hadj x x).trans (hQN x)

theorem wallForm_nondegenerate (hB : B.Nondegenerate) : (wallForm B N hadj).Nondegenerate := by
  constructor
  · rintro ⟨_, x, rfl⟩ hu
    have h : ∀ y, B (N x) y = 0 := fun y => by
      have := hu ⟨N y, LinearMap.mem_range_self N y⟩
      rwa [wallForm_apply] at this
    exact Subtype.ext (hB.1 _ h)
  · rintro ⟨_, y, rfl⟩ hu
    have h : ∀ x, B x (N y) = 0 := fun x => by
      have := hu ⟨N x, LinearMap.mem_range_self N x⟩
      rwa [wallForm_apply, hadj] at this
    exact Subtype.ext (hB.2 _ h)

theorem wallForm_map {g : V →ₗ[K] V} (hgN : ∀ x, g (N x) = N (g x))
    (hgB : ∀ x y, B (g x) (g y) = B x y) (u u' : LinearMap.range N) :
    wallForm B N hadj (g.restrict (mem_range_of_commute hgN) u)
      (g.restrict (mem_range_of_commute hgN) u') = wallForm B N hadj u u' := by
  obtain ⟨_, x, rfl⟩ := u
  obtain ⟨_, y, rfl⟩ := u'
  have h1 : g.restrict (mem_range_of_commute hgN) ⟨N x, LinearMap.mem_range_self N x⟩ =
      ⟨N (g x), LinearMap.mem_range_self N (g x)⟩ := Subtype.ext (hgN x)
  have h2 : g.restrict (mem_range_of_commute hgN) ⟨N y, LinearMap.mem_range_self N y⟩ =
      ⟨N (g y), LinearMap.mem_range_self N (g y)⟩ := Subtype.ext (hgN y)
  rw [h1, h2, wallForm_apply, wallForm_apply, ← hgN, hgB]

end Wall

section Involution

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [CharP K 2] in
theorem matrixLinearEquiv_mem_orthogonalGroup (s : matrixIsometries Q) :
    matrixLinearEquiv s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2

omit [CharP K 2] in
theorem polar_sNil_left (s : matrixIsometries Q) (hss : s * s = 1) (x y : Fin d → K) :
    QuadraticMap.polarBilin Q (sNil s.val x) y = QuadraticMap.polarBilin Q x (sNil s.val y) := by
  have hs2 : matrixLinearEquiv s.val (matrixLinearEquiv s.val y) = y := by
    rw [← LinearEquiv.mul_apply, ← matrixLinearEquiv_mul, ← Subgroup.coe_mul, hss,
      Subgroup.coe_one, matrixLinearEquiv_apply]
    simp
  simp only [QuadraticMap.polarBilin_apply_apply, sNil_apply, QuadraticMap.polar_sub_left,
    QuadraticMap.polar_sub_right]
  congr 1
  conv_lhs => rw [← hs2]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (matrixLinearEquiv_mem_orthogonalGroup s) x (matrixLinearEquiv s.val y)

theorem polar_projLift (hQ : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) (a b : Fin d → K) :
    QuadraticMap.polarBilin Q (projLift hQ x a) (projLift hQ x b) =
      QuadraticMap.polarBilin Q a b := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
    (Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ x)) a b

end Involution

end CFSG.SeitzReduction.OmegaPilot

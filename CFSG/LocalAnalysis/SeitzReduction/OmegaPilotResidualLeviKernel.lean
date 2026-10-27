module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSection
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviUnipotent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module LinearMap

section Commute

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sub_one_pow_eq_zero_of_commute_flag {N g : V →ₗ[K] V} (hgN : ∀ x, g (N x) = N (g x))
    (F : ℕ → Submodule K V) (hF0 : F 0 = ⊥) (k : ℕ)
    (hstep : ∀ i < k, ∀ x ∈ F (i + 1), g x - x ∈ F i) (hFk : F k = range N)
    (hker : ∀ x ∈ ker N, g x - x ∈ range N) : (g - 1) ^ (2 * k + 1) = 0 := by
  have hu : ∀ x, (g - 1) x = g x - x := fun x => rfl
  have hA : ∀ i ≤ k, ∀ x ∈ F i, ((g - 1) ^ i) x = 0 := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rw [hF0, Submodule.mem_bot] at hx
      rw [hx, map_zero]
    | succ i ih =>
      intro hi x hx
      rw [pow_succ, Module.End.mul_apply, hu]
      exact ih (by omega) _ (hstep i (by omega) x hx)
  have hB : ∀ i ≤ k, ∀ x, N x ∈ F i → ((g - 1) ^ (k + 1 + i)) x = 0 := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rw [hF0, Submodule.mem_bot] at hx
      rw [Nat.add_zero, pow_succ, Module.End.mul_apply, hu]
      exact hA k le_rfl _ (hFk ▸ hker x hx)
    | succ i ih =>
      intro hi x hx
      have hN : N (g x - x) ∈ F i := by
        rw [map_sub, ← hgN]
        exact hstep i (by omega) _ hx
      rw [show k + 1 + (i + 1) = k + 1 + i + 1 by ring, pow_succ, Module.End.mul_apply, hu]
      exact ih (by omega) _ hN
  ext x
  have h := hB k le_rfl x (by rw [hFk]; exact LinearMap.mem_range_self N x)
  rw [show 2 * k + 1 = k + 1 + k by ring, h]
  rfl

theorem sub_one_pow_three_eq_zero_of_commute {N g : V →ₗ[K] V} (hgN : ∀ x, g (N x) = N (g x))
    (hW : ∀ x ∈ range N, g x = x) (hker : ∀ x ∈ ker N, g x - x ∈ range N) :
    (g - 1) ^ 3 = 0 := by
  have h := sub_one_pow_eq_zero_of_commute_flag hgN (fun i => if i = 0 then ⊥ else range N)
    (by simp) 1 (fun i hi x hx => by
      obtain rfl : i = 0 := by omega
      have hx' : x ∈ range N := by simpa using hx
      simp [hW x hx']) (by simp) hker
  simpa using h

end Commute

section Core

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem projLift_one' (hQ : ∃ v, Q v ≠ 0) : projLift hQ (1 : matrixProjectiveDerived Q) = 1 := by
  rw [← projLiftHom_apply, map_one]

theorem isPGroup_of_sub_one_pow_eq_zero (hQ : ∃ v, Q v ≠ 0)
    {X : Subgroup (matrixProjectiveDerived Q)} (H : Subgroup ↥X) {m : ℕ}
    (h : ∀ x ∈ H, ((projLift hQ ((x : ↥X) : matrixProjectiveDerived Q) :
      (Fin d → K) →ₗ[K] (Fin d → K)) - 1) ^ m = 0) : IsPGroup 2 H := by
  intro x
  refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
  apply projLiftHom_injective hQ
  simp only [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one, projLiftHom_apply]
  exact pow_two_pow_eq_one_of_sub_one_pow_eq_zero (h x x.2)

variable (hQ : ∃ v, Q v ≠ 0) (X : Subgroup (matrixProjectiveDerived Q))
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v))

@[expose] noncomputable def rangeRestrictHom : ↥X →* Module.End K (range N) where
  toFun x := (projLift hQ (x : matrixProjectiveDerived Q) :
    (Fin d → K) →ₗ[K] (Fin d → K)).restrict (mem_range_of_commute (hXN x x.2))
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [projLift_one']
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [projLift_mul]

omit [CharP K 2] in
theorem kerQuotMap_mk' (g : (Fin d → K) →ₗ[K] (Fin d → K)) (hgN : ∀ x, g (N x) = N (g x))
    (z : ker N) :
    kerQuotMap N g hgN (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨g z, mem_ker_of_commute hgN z z.2⟩ :=
  rfl

omit [CharP K 2] in
theorem kerQuotMap_congr' {g g' : (Fin d → K) →ₗ[K] (Fin d → K)} (hg : g = g')
    (h : ∀ x, g (N x) = N (g x)) (h' : ∀ x, g' (N x) = N (g' x)) :
    kerQuotMap N g h = kerQuotMap N g' h' := by
  subst hg
  rfl

omit [CharP K 2] in
theorem kerQuotMap_one' (h : ∀ x, (1 : (Fin d → K) →ₗ[K] (Fin d → K)) (N x) =
    N ((1 : (Fin d → K) →ₗ[K] (Fin d → K)) x)) : kerQuotMap N 1 h = 1 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro z
  rfl

omit [CharP K 2] in
theorem kerQuotMap_mul' {g g' : (Fin d → K) →ₗ[K] (Fin d → K)} (h : ∀ x, g (N x) = N (g x))
    (h' : ∀ x, g' (N x) = N (g' x)) (h'' : ∀ x, (g * g') (N x) = N ((g * g') x)) :
    kerQuotMap N (g * g') h'' = kerQuotMap N g h * kerQuotMap N g' h' := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro z
  rfl

@[expose] noncomputable def kerQuotHom :
    ↥X →* Module.End K (ker N ⧸ rangeInKer N) where
  toFun x := kerQuotMap N (projLift hQ (x : matrixProjectiveDerived Q) :
    (Fin d → K) →ₗ[K] (Fin d → K)) (hXN x x.2)
  map_one' := by
    refine (kerQuotMap_congr' N (g' := 1) ?_ _ fun x => rfl).trans
      (kerQuotMap_one' N fun x => rfl)
    rw [OneMemClass.coe_one, projLift_one']
    rfl
  map_mul' x y := by
    refine (kerQuotMap_congr' N (g' := (projLift hQ (x : matrixProjectiveDerived Q) :
      (Fin d → K) →ₗ[K] (Fin d → K)) * (projLift hQ (y : matrixProjectiveDerived Q) :
        (Fin d → K) →ₗ[K] (Fin d → K))) ?_ _ ?_).trans (kerQuotMap_mul' N _ _ _)
    · rw [Subgroup.coe_mul, projLift_mul]
      rfl
    · intro v
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
      rw [hXN y y.2, hXN x x.2]

theorem isPGroup_ker_inf_ker :
    IsPGroup 2 ↥((rangeRestrictHom hQ X N hXN).ker ⊓ (kerQuotHom hQ X N hXN).ker) := by
  refine isPGroup_of_sub_one_pow_eq_zero hQ _ (m := 3) fun x hx => ?_
  obtain ⟨h1', h2'⟩ := hx
  have h1 : rangeRestrictHom hQ X N hXN x = 1 := h1'
  have h2 : kerQuotHom hQ X N hXN x = 1 := h2'
  refine sub_one_pow_three_eq_zero_of_commute (N := N) (hXN x x.2) (fun w hw => ?_)
    (fun v hv => ?_)
  · have h := congrArg (fun f : Module.End K (range N) => (f ⟨w, hw⟩ : Fin d → K)) h1
    simpa [rangeRestrictHom] using h
  · have h := congrArg (fun f : Module.End K (ker N ⧸ rangeInKer N) =>
      f (Submodule.Quotient.mk ⟨v, hv⟩)) h2
    change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk ⟨v, hv⟩) =
      Submodule.Quotient.mk ⟨v, hv⟩ at h
    rw [kerQuotMap_mk'] at h
    have h' := (Submodule.Quotient.eq _).mp h
    simpa [rangeInKer] using h'

end Core

end CFSG.SeitzReduction.OmegaPilot

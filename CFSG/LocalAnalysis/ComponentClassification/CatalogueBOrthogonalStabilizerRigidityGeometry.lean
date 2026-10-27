module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalStabilizerRigidity

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

abbrev elementaryStabilizer (Q : QuadraticForm K V) (M : Submodule K V) :
    Subgroup (elementaryGroup Q) :=
  MulAction.stabilizer (elementaryGroup Q) M

theorem polar_eq_zero_of_totally_singular {Q : QuadraticForm K V} {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    polar Q x y = 0 := by
  rw [polar, hM (x + y) (M.add_mem hx hy), hM x hx, hM y hy]
  simp

theorem totally_singular_eq_orthogonal [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) (hdim : Module.finrank K V = 2 * Module.finrank K M) :
    M = LinearMap.BilinForm.orthogonal Q.polarBilin M := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro y hy
    exact polar_eq_zero_of_totally_singular hM hy hx
  · rw [LinearMap.BilinForm.finrank_orthogonal hQ, hdim]
    omega

theorem mem_elementaryStabilizer_iff {Q : QuadraticForm K V} {M : Submodule K V}
    (g : elementaryGroup Q) :
    g ∈ elementaryStabilizer Q M ↔
      (∀ x ∈ M, (g : V ≃ₗ[K] V) x ∈ M) ∧
      (∀ x ∈ M, (g : V ≃ₗ[K] V)⁻¹ x ∈ M) := by
  change M.map (g : V ≃ₗ[K] V).toLinearMap = M ↔ _
  constructor
  · intro h
    constructor
    · intro x hx
      rw [← h]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    · intro x hx
      have hx' : x ∈ M.map (g : V ≃ₗ[K] V).toLinearMap := by rwa [h]
      obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx'
      change (g : V ≃ₗ[K] V) y = x at hxy
      rw [← hxy, LinearEquiv.inv_apply_apply']
      exact hy
  · rintro ⟨hf, hi⟩
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
      change (g : V ≃ₗ[K] V) y = x at hxy
      rw [← hxy]
      exact hf y hy
    · intro x hx
      exact Submodule.mem_map.mpr
        ⟨(g : V ≃ₗ[K] V)⁻¹ x, hi x hx, LinearEquiv.apply_inv_apply' _ _⟩

theorem elementaryStabilizer_apply_mem {Q : QuadraticForm K V} {M : Submodule K V}
    {g : elementaryGroup Q} (hg : g ∈ elementaryStabilizer Q M)
    {x : V} (hx : x ∈ M) : (g : V ≃ₗ[K] V) x ∈ M :=
  ((mem_elementaryStabilizer_iff g).mp hg).1 x hx

theorem eichler_apply_mem {Q : QuadraticForm K V} {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) {u p x : V} (hu : u ∈ M)
    (hp : polar Q u p = 0) (hx : x ∈ M) : eichler Q u p x ∈ M := by
  rw [eichler_apply (hM u hu) hp, polar_eq_zero_of_totally_singular hM hx hu]
  simp only [zero_smul, add_zero, mul_zero]
  exact M.sub_mem hx (M.smul_mem _ hu)

theorem eichler_mem_elementaryStabilizer {Q : QuadraticForm K V} {M : Submodule K V}
    (hM : ∀ x ∈ M, Q x = 0) {u p : V} (hu : u ∈ M) (hp : polar Q u p = 0) :
    (⟨eichler Q u p, eichler_mem_elementaryGroup Q u p⟩ : elementaryGroup Q) ∈
      elementaryStabilizer Q M := by
  apply (mem_elementaryStabilizer_iff _).mpr
  constructor
  · intro x hx
    exact eichler_apply_mem hM hu hp hx
  · intro x hx
    change (eichler Q u p)⁻¹ x ∈ M
    rw [eichler_inv hp]
    exact eichler_apply_mem hM hu (by rw [polar_neg_right, hp, neg_zero]) hx

end CFSG.ComponentClassification.CatalogueBOrthogonalStabilizerRigidity

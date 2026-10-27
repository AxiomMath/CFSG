module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftTools

public section

namespace CFSG.QuasithinUnique.Setup.Lift

theorem retraction_of_selfdual_splitting {K : Type*} [Field K] {G : Type*} [Group G]
    {D V : Type*} [AddCommGroup D] [Module K D] [AddCommGroup V] [Module K V] [Finite D]
    [Finite V] (ρD : Representation K G D) (ρV : Representation K G V)
    (B : D →ₗ[K] D →ₗ[K] K) (hBnd : ∀ x : D, (∀ y, B x y = 0) → x = 0)
    (hBsymm : ∀ x y, B x y = B y x) (hBinv : ∀ g x y, B (ρD g x) (ρD g y) = B x y)
    (hsplit : ∀ π : Module.Dual K V →ₗ[K] D, Function.Surjective π →
      (∀ g f, π (ρV.dual g f) = ρD g (π f)) →
      ∃ j : D →ₗ[K] Module.Dual K V, (∀ x, π (j x) = x) ∧
        ∀ g x, j (ρD g x) = ρV.dual g (j x))
    (ι : D →ₗ[K] V) (hι : Function.Injective ι) (hιeq : ∀ g x, ι (ρD g x) = ρV g (ι x)) :
    ∃ P : V →ₗ[K] D, (∀ x, P (ι x) = x) ∧ ∀ g v, P (ρV g v) = ρD g (P v) := by
  classical
  have : Module.Finite K D := Module.Finite.of_finite
  have : Module.Finite K V := Module.Finite.of_finite
  let B' : D →ₗ[K] Module.Dual K D := B
  have hinj : Function.Injective B' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hBnd x (fun y => by rw [show B x = 0 from hx]; rfl)
  have hfin : Module.finrank K D = Module.finrank K (Module.Dual K D) :=
    (Subspace.dual_finrank_eq).symm
  have hsurj : Function.Surjective B' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  have hbij : Function.Bijective B' := ⟨hinj, hsurj⟩
  let E : D ≃ₗ[K] Module.Dual K D := LinearEquiv.ofBijective B' hbij
  have hE : ∀ x y, E x y = B x y := fun x y => rfl
  have hρD_inv : ∀ (g : G) (y : D), ρD g (ρD g⁻¹ y) = y := by
    intro g y
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hdual : ∀ (g : G) (f : Module.Dual K V) (v : V), ρV.dual g f v = f (ρV g⁻¹ v) := by
    intro g f v
    rw [Representation.dual_apply]
    rfl
  let π : Module.Dual K V →ₗ[K] D :=
    (E.symm : Module.Dual K D →ₗ[K] D) ∘ₗ ι.dualMap
  have hπE : ∀ f, E (π f) = ι.dualMap f := fun f => by simp [π]
  have hπs : Function.Surjective π :=
    E.symm.surjective.comp (LinearMap.dualMap_surjective_of_injective hι)
  have hπ : ∀ g f, π (ρV.dual g f) = ρD g (π f) := by
    intro g f
    apply E.injective
    rw [hπE]
    apply LinearMap.ext
    intro y
    have h1 : (ι.dualMap (ρV.dual g f)) y = f (ι (ρD g⁻¹ y)) := by
      rw [LinearMap.dualMap_apply, hdual, hιeq]
    have h2 : (E (ρD g (π f))) y = B (π f) (ρD g⁻¹ y) := by
      rw [hE]
      have := hBinv g (π f) (ρD g⁻¹ y)
      rw [hρD_inv] at this
      exact this
    rw [h1, h2, ← hE, hπE]
    rfl
  obtain ⟨j, hj1, hj2⟩ := hsplit π hπs hπ
  let P : V →ₗ[K] D :=
    (E.symm : Module.Dual K D →ₗ[K] D) ∘ₗ (j.dualMap ∘ₗ Module.Dual.eval K V)
  have hPE : ∀ v z, E (P v) z = j z v := by
    intro v z
    simp [P]
  refine ⟨P, fun x => ?_, fun g v => ?_⟩
  · apply E.injective
    apply LinearMap.ext
    intro z
    rw [hPE, hE]
    have h1 : ι.dualMap (j z) = E z := by
      have := congrArg E (hj1 z)
      rw [hπE] at this
      exact this
    have h2 : (j z) (ι x) = B z x := by
      have := congrArg (fun φ => φ x) h1
      exact this
    rw [h2, hBsymm]
  · apply E.injective
    apply LinearMap.ext
    intro z
    rw [hPE]
    have h1 : j z (ρV g v) = j (ρD g⁻¹ z) v := by
      have := hj2 g⁻¹ z
      have h3 := congrArg (fun f => f v) this
      simp only [hdual] at h3
      rw [inv_inv] at h3
      exact h3.symm
    rw [h1, hE (ρD g (P v)) z]
    have h4 := hBinv g (P v) (ρD g⁻¹ z)
    rw [hρD_inv] at h4
    rw [h4]
    have h5 := hPE v (ρD g⁻¹ z)
    rw [hE] at h5
    exact h5.symm

end CFSG.QuasithinUnique.Setup.Lift

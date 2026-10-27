module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {W : Type} [Group W]

@[expose] def Acts (θ : W ≃* Multiplicative (ι → ZMod 2)) (g : MulAut W)
    (M : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ w : W, Multiplicative.toAdd (θ (g w)) = M *ᵥ Multiplicative.toAdd (θ w)

theorem Acts.mul {θ : W ≃* Multiplicative (ι → ZMod 2)} {g g' : MulAut W}
    {M M' : Matrix ι ι (ZMod 2)} (h : Acts θ g M) (h' : Acts θ g' M') :
    Acts θ (g * g') (M * M') := by
  intro w
  rw [MulAut.mul_apply, h (g' w), h' w, Matrix.mulVec_mulVec]

theorem acts_one (θ : W ≃* Multiplicative (ι → ZMod 2)) : Acts θ (1 : MulAut W) 1 := by
  intro w
  simp

theorem Acts.matrix_eq {θ : W ≃* Multiplicative (ι → ZMod 2)} {g : MulAut W}
    {M M' : Matrix ι ι (ZMod 2)} (h : Acts θ g M) (h' : Acts θ g M') : M = M' := by
  have hv : ∀ v : ι → ZMod 2, M *ᵥ v = M' *ᵥ v := by
    intro v
    obtain ⟨w, hw⟩ := θ.surjective (Multiplicative.ofAdd v)
    have hw' : Multiplicative.toAdd (θ w) = v := by rw [hw]; rfl
    rw [← hw', ← h w, ← h' w]
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hv v)

theorem Acts.ext {θ : W ≃* Multiplicative (ι → ZMod 2)} {g g' : MulAut W}
    {M : Matrix ι ι (ZMod 2)} (h : Acts θ g M) (h' : Acts θ g' M) : g = g' := by
  refine MulEquiv.ext fun w => ?_
  apply θ.injective
  apply Multiplicative.toAdd.injective
  rw [h w, h' w]

theorem exists_acts (θ : W ≃* Multiplicative (ι → ZMod 2)) (g : MulAut W) :
    ∃ M : Matrix ι ι (ZMod 2), Acts θ g M := by
  let f : (ι → ZMod 2) →+ (ι → ZMod 2) :=
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (θ (g (θ.symm (Multiplicative.ofAdd v)))))
      (fun v w => by
        show Multiplicative.toAdd (θ (g (θ.symm (Multiplicative.ofAdd (v + w))))) =
          Multiplicative.toAdd (θ (g (θ.symm (Multiplicative.ofAdd v)))) +
            Multiplicative.toAdd (θ (g (θ.symm (Multiplicative.ofAdd w))))
        rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul])
  let lin : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) := AddMonoidHom.toZModLinearMap 2 f
  refine ⟨LinearMap.toMatrix' lin, fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  change Multiplicative.toAdd (θ (g w)) =
    Multiplicative.toAdd (θ (g (θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (θ w))))))
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem Acts.exists_inv {θ : W ≃* Multiplicative (ι → ZMod 2)} {g : MulAut W}
    {M : Matrix ι ι (ZMod 2)} (h : Acts θ g M) :
    ∃ N : Matrix ι ι (ZMod 2), M * N = 1 ∧ N * M = 1 := by
  obtain ⟨N, hN⟩ := exists_acts θ g⁻¹
  refine ⟨N, ?_, ?_⟩
  · have h1 : Acts θ (g * g⁻¹) (M * N) := h.mul hN
    rw [mul_inv_cancel] at h1
    exact h1.matrix_eq (acts_one θ)
  · have h2 : Acts θ (g⁻¹ * g) (N * M) := hN.mul h
    rw [inv_mul_cancel] at h2
    exact h2.matrix_eq (acts_one θ)

theorem Acts.card_fix {θ : W ≃* Multiplicative (ι → ZMod 2)} {g : MulAut W}
    {M : Matrix ι ι (ZMod 2)} (h : Acts θ g M) :
    Nat.card {w : W // g w = w} =
      (Finset.univ.filter fun v : ι → ZMod 2 => M *ᵥ v = v).card := by
  have hequiv : {w : W // g w = w} ≃ {v : ι → ZMod 2 // M *ᵥ v = v} :=
    Equiv.subtypeEquiv (θ.toEquiv.trans Multiplicative.toAdd) fun w => by
      change g w = w ↔ M *ᵥ Multiplicative.toAdd (θ w) = Multiplicative.toAdd (θ w)
      rw [← h w, Multiplicative.toAdd.injective.eq_iff, θ.injective.eq_iff]
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype]

end T84Mod

end CFSG.OddStandard.SmallF3.Omega

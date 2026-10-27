module


public import Mathlib.RepresentationTheory.Irreducible

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.FiniteOrderIntertwinerNormalize

theorem exists_normalized {F : Type*} [Field F] [IsAlgClosed F]
    {E : Type*} [Group E] {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    [Nontrivial W] (η : Representation F E W) (hη : η.IsIrreducible)
    (α : MulAut E) (r : ℕ) (hr : 0 < r) (hα : α ^ r = 1)
    (U : W ≃ₗ[F] W) (hU : ∀ e w, U (η e w) = η (α e) (U w)) :
    ∃ U' : W ≃ₗ[F] W, U' ^ r = 1 ∧ ∀ e w, U' (η e w) = η (α e) (U' w) := by
  have hpow : ∀ n : ℕ, ∀ e w, (U ^ n) (η e w) = η ((α ^ n) e) ((U ^ n) w) := by
    intro n
    induction n with
    | zero => intro e w; simp
    | succ n ih =>
      intro e w
      rw [pow_succ, LinearEquiv.mul_apply, hU, ih, pow_succ, LinearEquiv.mul_apply]
      simp [MulAut.mul_apply]
  have hcomm : ∀ e w, (U ^ r : W ≃ₗ[F] W) (η e w) = η e ((U ^ r : W ≃ₗ[F] W) w) := by
    intro e w
    rw [hpow, hα]; rfl
  let f : Representation.IntertwiningMap η η :=
    { toLinearMap := ((U ^ r : W ≃ₗ[F] W) : W →ₗ[F] W)
      isIntertwining' := fun g => by ext v; exact hcomm g v }
  haveI := hη
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (k := F) (ρ := η)).2 f
  have hc' : ∀ w, (U ^ r : W ≃ₗ[F] W) w = c • w := by
    intro w
    have := congrArg (fun g : Representation.IntertwiningMap η η => g w) hc
    exact (by simpa using this.symm : f w = c • w)
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have := hc' w
    rw [h0, zero_smul] at this
    exact hw ((U ^ r : W ≃ₗ[F] W).map_eq_zero_iff.1 this)
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hr
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne'] at hd
    exact hc0 hd.symm
  let U' : W ≃ₗ[F] W := U.trans (LinearEquiv.smulOfNeZero F W d⁻¹ (inv_ne_zero hd0))
  have hU'pow : ∀ n : ℕ, ∀ w, (U' ^ n) w = (d⁻¹) ^ n • (U ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, LinearEquiv.mul_apply, ih]
      have h1 : U' w = d⁻¹ • U w := rfl
      rw [h1, map_smul, smul_smul, ← pow_succ, ← LinearEquiv.mul_apply, ← pow_succ]
  refine ⟨U', ?_, ?_⟩
  · ext w
    rw [hU'pow, hc', smul_smul, ← hd, ← mul_pow, inv_mul_cancel₀ hd0]
    simp
  · intro e w
    simp [U', hU]

end CFSG.GroupTheory.CoprimeActionSupport.FiniteOrderIntertwinerNormalize

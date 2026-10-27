module


public import CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition
public import CFSG.LinearAlgebra.CoprimeActions.MovedWeightDimension

public section

namespace CFSG.LinearAlgebra.CoprimeActions.AbelianNormalizerSmallDimension

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

theorem eq_one {F V E : Type*} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [CommGroup E] [Finite E]
    (τ : Representation F E V) (hfaith : Function.Injective τ)
    (hcard : (Nat.card E : F) ≠ 0)
    (q : ℕ) (hq : q.Prime) (hdim : Module.finrank F V < q)
    (α : MulAut E) (hα : α ^ q = 1)
    (σ : V ≃ₗ[F] V) (hcov : ∀ g v, σ (τ g v) = τ (α g) (σ v)) :
    α = 1 := by
  classical
  have htop := CFSG.LinearAlgebra.CoprimeActions.AbelianCoprimeWeightSpaceDecomposition.span_eq_top τ hcard
  have hfix : ∀ χ : E →* Fˣ, weightSpace τ χ ≠ ⊥ → χ.comp α.toMonoidHom = χ := by
    intro χ hχ
    by_contra hmv
    have := MovedWeightDimension.bound τ σ α q hq hα hcov χ hχ hmv
    omega
  ext g
  have key : ∀ h : E, τ (α h) = τ h := by
    intro h
    refine ext_on_weights (W := V) τ (fun χ : E →* Fˣ => χ) htop (τ (α h)) (τ h)
      (fun χ v hv => ?_)
    by_cases hb : weightSpace τ χ = ⊥
    · rw [hb] at hv
      rw [(Submodule.mem_bot F).1 hv]; simp
    · have h1 := DFunLike.congr_fun (hfix χ hb) h
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      rw [(mem_weightSpace τ χ v).1 hv, (mem_weightSpace τ χ v).1 hv, h1]
  simpa using hfaith (key g)

end CFSG.LinearAlgebra.CoprimeActions.AbelianNormalizerSmallDimension

module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSLGraph

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)

section Generic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] {G : Type} [Group G]

theorem conj_comp_graphParamEquiv_symm (ε : F ≃+* K)
    {Φ₁ : Matrix.SpecialLinearGroup (Fin 6) F →* G} {t : G}
    (hc : ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) g))
    (x y : e6ScLevi K e6A5Nodes)
    (hxy : (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x) :
    t * Φ₁.comp (graphParamEquiv K ε).symm.toMonoidHom x * t⁻¹ =
      Φ₁.comp (graphParamEquiv K ε).symm.toMonoidHom y := by
  have hy : (graphParamEquiv K ε).symm y =
      (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) ((graphParamEquiv K ε).symm x) := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_graphParamEquiv, ← sigma_graphParamHom, ← coe_graphParamEquiv,
      MulEquiv.apply_symm_apply, hxy]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hy, hc]

theorem range_comp_graphParamEquiv_symm (ε : F ≃+* K)
    (Φ₁ : Matrix.SpecialLinearGroup (Fin 6) F →* G) :
    (Φ₁.comp (graphParamEquiv K ε).symm.toMonoidHom).range = Φ₁.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (graphParamEquiv K ε).symm.surjective,
    ← MonoidHom.range_eq_map]

theorem ker_comp_graphParamEquiv_symm_le_center (ε : F ≃+* K)
    {Φ₁ : Matrix.SpecialLinearGroup (Fin 6) F →* G}
    (hker : Φ₁.ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) F)) :
    (Φ₁.comp (graphParamEquiv K ε).symm.toMonoidHom).ker ≤ center (e6ScLevi K e6A5Nodes) := by
  intro x hx
  have h1 : (graphParamEquiv K ε).symm x ∈ center (Matrix.SpecialLinearGroup (Fin 6) F) :=
    hker hx
  rw [← Subgroup.map_center_eq (graphParamEquiv K ε)]
  exact ⟨_, h1, MulEquiv.apply_symm_apply _ x⟩

end Generic

end CFSG.SeitzReduction.F4Pilot

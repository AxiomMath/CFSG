module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrIsolatedFourEscape
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.SFL

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G]

theorem conjugate_centralizer_eq (a g : G) :
    conjugate (centralizer ({a} : Set G)) g = centralizer ({g⁻¹ * a * g} : Set G) := by
  ext x
  change x ∈ (centralizer ({a} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g⁻¹ * y * g * (g⁻¹ * a * g) = g⁻¹ * (y * a) * g := by group
      _ = g⁻¹ * (a * y) * g := by rw [hy]
      _ = g⁻¹ * a * g * (g⁻¹ * y * g) := by group
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, by group⟩
    calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * x) * g⁻¹ := by rw [hx]
      _ = a * (g * x * g⁻¹) := by group

end CFSG.ComponentClassification.GrSLit.SFL

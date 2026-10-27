module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

section Basic

variable {Γ : Type} [Group Γ] {K P R : Subgroup Γ}

theorem comm_inf_le (hK : K.Normal) (hR : R ≤ normalizer (P : Set Γ)) {x y : Γ}
    (hx : x ∈ R ⊓ K) (hy : y ∈ P) : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ K := by
  refine ⟨?_, ?_⟩
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hR hx.1) y).mp hy) (P.inv_mem hy)
  · have h1 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [h1]
    exact mul_mem hx.2 (hK.conj_mem _ (K.inv_mem hx.2) y)

end Basic

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

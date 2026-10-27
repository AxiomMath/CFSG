module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitElemAb
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement Pointwise

variable {W : Type} [Group W] [Finite W]

theorem map_coreActionKernel_eq_centralizer {D : Subgroup W} (hD : D.Normal) :
    (coreActionKernel D).map (QuotientGroup.mk' (pPrimeCore 2 W)) =
      centralizer ((D.map (QuotientGroup.mk' (pPrimeCore 2 W)) :
        Subgroup (W ⧸ pPrimeCore 2 W)) : Set (W ⧸ pPrimeCore 2 W)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : W →* W ⧸ pPrimeCore 2 W := QuotientGroup.mk' (pPrimeCore 2 W) with hπ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have hcommD : d⁻¹ * x⁻¹ * d * x ∈ (pPrimeCore 2 ↥D).map D.subtype :=
      (mem_coreActionKernel.mp hx).2 d hd
    have hcommO : d⁻¹ * x⁻¹ * d * x ∈ pPrimeCore 2 W := by
      rw [CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 2) hD] at hcommD
      exact hcommD.2
    have hinner : (π d)⁻¹ * (π x)⁻¹ * π d * π x = 1 := by
      have h1 : π (d⁻¹ * x⁻¹ * d * x) = 1 := (QuotientGroup.eq_one_iff _).mpr hcommO
      simpa using h1
    calc
      π d * π x = (π x * π d) * ((π d)⁻¹ * (π x)⁻¹ * π d * π x) := by group
      _ = π x * π d := by rw [hinner, mul_one]
  · rintro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 W) q
    refine ⟨x, mem_coreActionKernel.mpr ⟨?_, fun d hd => ?_⟩, rfl⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr hD]
      exact mem_top x
    · have hcomm : π d * π x = π x * π d :=
        (mem_centralizer_iff.mp hq) (π d) ⟨d, hd, rfl⟩
      have hinner : (π d)⁻¹ * (π x)⁻¹ * π d * π x = 1 := by
        calc
          (π d)⁻¹ * (π x)⁻¹ * π d * π x = (π x * π d)⁻¹ * (π d * π x) := by group
          _ = (π d * π x)⁻¹ * (π d * π x) := by rw [hcomm]
          _ = 1 := inv_mul_cancel _
      have hker : d⁻¹ * x⁻¹ * d * x ∈ pPrimeCore 2 W := by
        have h1 : π (d⁻¹ * x⁻¹ * d * x) = 1 := by
          simpa using hinner
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hmemD : d⁻¹ * x⁻¹ * d * x ∈ D := by
        have h1 : x⁻¹ * d * x ∈ D := by
          simpa using hD.conj_mem d hd x⁻¹
        simpa [mul_assoc] using mul_mem (inv_mem hd) h1
      have hinf : d⁻¹ * x⁻¹ * d * x ∈ D ⊓ pPrimeCore 2 W := ⟨hmemD, hker⟩
      rwa [← CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 2) hD] at hinf

end CFSG.ComponentClassification.UnbalancedLayer

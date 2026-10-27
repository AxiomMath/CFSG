module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {H : Type} [Group H]

theorem cp_isIsoOn_conj_cent (g t : H) :
    IsIsoOn (Gx t) (Gx (g * t * g⁻¹)) (fun x => g * x * g⁻¹) where
  map_mul x _ y _ := by group
  mem x hx := by
    rw [mem_Gx] at hx ⊢
    calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [hx]
      _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
  injOn x _ y _ h := by simpa using h
  surjOn y hy := by
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    rw [mem_Gx] at hy ⊢
    calc t * (g⁻¹ * y * g) = g⁻¹ * (g * t * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * t * g⁻¹)) * g := by rw [hy]
      _ = g⁻¹ * y * g * t := by group

theorem cp_isIsoOn_conj_cent_inv (g t : H) :
    IsIsoOn (Gx (g * t * g⁻¹)) (Gx t) (fun x => g⁻¹ * x * g) := by
  have h := cp_isIsoOn_conj_cent g⁻¹ (g * t * g⁻¹)
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  rw [e] at h
  simpa using h

end CFSG.EvenSporadicStandard.HNRecog.Section4

module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MAFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MB

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

namespace MA

@[expose] def E0WList : List MA := [1, z, u, k, z * u, z * k, u * k, z * u * k]

theorem mix_cert : ∀ e ∈ E0WList, ∀ c ∈ ZList,
    (w₁ * (e * t)⁻¹) * (v * w₁ * c⁻¹) * (w₁ * (e * t)⁻¹)⁻¹ * (v * w₁ * c⁻¹)⁻¹ ≠ 1 ∧
      (w₁ * (e * t)⁻¹) * (v * w₁ * c⁻¹) * (w₁ * (e * t)⁻¹)⁻¹ * (v * w₁ * c⁻¹)⁻¹ ≠ z := by
  decide +kernel

end MA

namespace MB

@[expose] def ZList : List MB := [1, z, k, z * k]

@[expose] def E0WList : List MB := [1, z, u, k, z * u, z * k, u * k, z * u * k]

theorem mix_cert : ∀ e ∈ E0WList, ∀ c ∈ ZList,
    (w₁ * y * (e * t)⁻¹) * (v * (w₁ * y) * c⁻¹) * (w₁ * y * (e * t)⁻¹)⁻¹ *
        (v * (w₁ * y) * c⁻¹)⁻¹ ≠ 1 ∧
      (w₁ * y * (e * t)⁻¹) * (v * (w₁ * y) * c⁻¹) * (w₁ * y * (e * t)⁻¹)⁻¹ *
        (v * (w₁ * y) * c⁻¹)⁻¹ ≠ z := by
  decide +kernel

end MB

end CFSG.ComponentClassification.HSFLit.Sec8

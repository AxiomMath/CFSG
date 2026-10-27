module

public import Certificates.Certificate27650

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open CFSG.Blueprint.NativeSporadic


theorem hs_C3 : ∃ a b g : Carrier .HS, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧
    g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b :=
  hsC3_of_checks Certificates.certificate27650

theorem hs_C5 : ∃ x y z g : Carrier .HS, z = x * y * x⁻¹ * y⁻¹ ∧ z ^ 5 = 1 ∧ z ≠ 1 ∧
    x * z = z * x ∧ y * z = z * y ∧ g * z * g⁻¹ = z ^ 2 :=
  hsC5_of_checks Certificates.certificate27650

theorem hs_C11 : ∃ u h : Carrier .HS, u ^ 11 = 1 ∧ u ≠ 1 ∧ h * u * h⁻¹ = u ^ 3 :=
  hsC11_of_checks Certificates.certificate27650

end CFSG.ComponentClassification.CatFC.KGHS3

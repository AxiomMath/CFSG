module

public import Certificates.Certificate840004

public section

namespace CFSG.CGT.Hall82.DModel

open CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81.Hexa

theorem lift :
    ∀ a : Fin 3 → Fin 64,
      (∀ i j, hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = 1 ∨
        hallXi a i * hallXi a j * (hallXi a i)⁻¹ * (hallXi a j)⁻¹ = transl 5) →
      (∀ i, hallXi a i * hallXi a i = 1 ∨ hallXi a i * hallXi a i = transl 5) →
      (∀ s ∈ hexaM, s 5 = 5 → ∀ i, ∃ u, InHallU u ∧ ∃ e, s * hallXi a i * s⁻¹ =
        transl u * hallXProd a e) →
      ∀ i, InHallU (a i) :=
  Certificates.certificate840004.1

theorem xcode_mul :
    ∀ x ∈ hallX1, ∀ y ∈ hallX1, xcode (x * y) = xorF (xcode x) (xcode y) :=
  Certificates.certificate840004.2.1

theorem xcode_eq_zero :
    ∀ x ∈ hallX1, xcode x = 0 ↔ x = 1 ∨ x = transl 5 :=
  Certificates.certificate840004.2.2.1

theorem xcode_surj : ∀ k, ∃ x ∈ hallX1, xcode x = k :=
  Certificates.certificate840004.2.2.2.1

theorem xcode_sq :
    ∀ x ∈ hallX1, x * x = transl 5 ↔ hallQ0 (xcode x) = true :=
  Certificates.certificate840004.2.2.2.2.1

theorem xcode_orb :
    ∀ x ∈ hallX1, IsHallOrb (xcode x) → ∃ h, IsOvalVec h ∧ x = transl h :=
  Certificates.certificate840004.2.2.2.2.2.1

theorem xcode_conj :
    ∀ b, ∀ s ∈ hexaM, s 5 = 5 → ∃ σ ∈ hallS40, ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) :=
  Certificates.certificate840004.2.2.2.2.2.2.1

theorem xcode_conj_surj :
    ∀ σ ∈ hallS40, ∃ b, ∃ s ∈ hexaM, s 5 = 5 ∧ ∀ x ∈ hallX1,
      xcode (transl b * s * x * (transl b * s)⁻¹) = σ (xcode x) :=
  Certificates.certificate840004.2.2.2.2.2.2.2.1

theorem reducible :
    ∀ y : Fin 64 → Fin 64, (∀ k l, y (xorF k l) = xorF (y k) (y l)) →
      (∀ k, hallQ0 (y k) = hallQ0 k) → (∀ k, y k = 0 → k = 0) → GoodHall y →
      (∀ t ∈ hallS40, GoodHall (y ∘ t ∘ y)) →
      (∀ t ∈ hallS40, ∀ u ∈ hallS40, GoodHall (y ∘ t ∘ y ∘ u ∘ y)) →
      ∀ k, InHallW k → InHallW (y k) :=
  Certificates.certificate840004.2.2.2.2.2.2.2.2

end CFSG.CGT.Hall82.DModel

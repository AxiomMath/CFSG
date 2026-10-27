module

public import Certificates.Certificate19780
public import CFSG.LargeExtraspecial.AS62C36RigidSpec

public section

namespace CFSG.LargeExtraspecial

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42

namespace AS62

theorem amalgamAut_eq_conj
    (α₁ : U42.P1 ≃* U42.P1) (α₂ : U42.P2 ≃* U42.P2)
    (h : ∀ (b : U42.Y) (h1 : b ∈ U42.P1) (h2 : b ∈ U42.P2),
      ((α₁ ⟨b, h1⟩ : U42.Y) : P45) = ((α₂ ⟨b, h2⟩ : U42.Y) : P45)) :
    ∃ f : U42Aut.Ah, f ∈ U42Aut.Bh ∧
      (∀ p : U42.P1, ((α₁ p : U42.Y) : P45) = (f : P45) * ((p : U42.Y) : P45) * (f : P45)⁻¹) ∧
      (∀ p : U42.P2, ((α₂ p : U42.Y) : P45) = (f : P45) * ((p : U42.Y) : P45) * (f : P45)⁻¹) := by
  obtain ⟨hR, hbd, hp1, hp2⟩ := Certificates.certificate19780
  exact Rigid.amalgamAut_eq_conj_of_check hR hbd hp1 hp2 α₁ α₂ h

end AS62

end CFSG.LargeExtraspecial

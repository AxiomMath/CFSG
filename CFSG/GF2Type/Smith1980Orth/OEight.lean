module

public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G]

@[expose] def OEight (S : Setting G) : Prop := ∀ h₁ h₂ : G, h₁ * S.z * h₁⁻¹ ∈ S.QG →
  h₁ * S.z * h₁⁻¹ ≠ S.z → h₂ * S.z * h₂⁻¹ ∈ S.QG → h₂ * S.z * h₂⁻¹ ≠ S.z →
  h₁ * S.z * h₁⁻¹ * (h₂ * S.z * h₂⁻¹) = h₂ * S.z * h₂⁻¹ * (h₁ * S.z * h₁⁻¹) →
  8 ≤ Nat.card (S.Qa h₁ ⊓ S.Qa h₂ : Subgroup G)

theorem card_Qa_mul_inf_Qa_mul (S : Setting G) (g h₁ h₂ : G) :
    Nat.card (S.Qa (g * h₁) ⊓ S.Qa (g * h₂) : Subgroup G) =
      Nat.card (S.Qa h₁ ⊓ S.Qa h₂ : Subgroup G) := by
  rw [S.Qa_mul h₁ g, S.Qa_mul h₂ g, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem eight_le_card_QG_inf_Qa_of_oEight {S : Setting G} (hE : OEight S) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {k : G}
    (hxM : k * S.z * k⁻¹ ∈ S.M) (hxQ : k * S.z * k⁻¹ ∉ S.QG) (hxa : k * S.z * k⁻¹ ∈ S.Qa g) :
    8 ≤ Nat.card (S.QG ⊓ S.Qa k : Subgroup G) := by
  have hz : S.z ∈ S.Qa g := S.z_mem_Qa haQ hne
  have h1Q : g⁻¹ * S.z * g ∈ S.QG := by
    have h := (S.mem_Qa_mul_iff (g := 1) (h := g)).mp (by simpa using hz)
    simpa [S.Qa_one] using h
  have h1ne : g⁻¹ * S.z * g ≠ S.z := by
    intro h
    apply hne
    have := congrArg (fun x => g * x * g⁻¹) h
    simpa [mul_assoc] using this.symm
  have h2Q : g⁻¹ * (k * S.z * k⁻¹) * g ∈ S.QG := by
    have h := (S.mem_Qa_mul_iff (g := 1) (h := g)).mp (by simpa using hxa)
    simpa [S.Qa_one] using h
  have h2ne : g⁻¹ * (k * S.z * k⁻¹) * g ≠ S.z := by
    intro h
    apply hxQ
    have h' : k * S.z * k⁻¹ = g * S.z * g⁻¹ := by
      have := congrArg (fun x => g * x * g⁻¹) h
      simpa [mul_assoc] using this
    rwa [h']
  have hcomm : (g⁻¹ * S.z * g) * (g⁻¹ * (k * S.z * k⁻¹) * g) =
      (g⁻¹ * (k * S.z * k⁻¹) * g) * (g⁻¹ * S.z * g) := by
    have hzx : S.z * (k * S.z * k⁻¹) = (k * S.z * k⁻¹) * S.z :=
      (S.mem_M_iff.mp hxM).symm
    calc (g⁻¹ * S.z * g) * (g⁻¹ * (k * S.z * k⁻¹) * g)
        = g⁻¹ * (S.z * (k * S.z * k⁻¹)) * g := by group
      _ = g⁻¹ * ((k * S.z * k⁻¹) * S.z) * g := by rw [hzx]
      _ = (g⁻¹ * (k * S.z * k⁻¹) * g) * (g⁻¹ * S.z * g) := by group
  have h2Q' : (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ ∈ S.QG := by
    simpa [mul_assoc] using h2Q
  have h2ne' : (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹ ≠ S.z := by
    simpa [mul_assoc] using h2ne
  have hcomm' : (g⁻¹ * S.z * (g⁻¹)⁻¹) * ((g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹) =
      ((g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹) * (g⁻¹ * S.z * (g⁻¹)⁻¹) := by
    simpa [mul_assoc] using hcomm
  have h8 := hE (g⁻¹) (g⁻¹ * k) (by simpa using h1Q) (by simpa using h1ne) h2Q' h2ne' hcomm'
  rwa [← card_Qa_mul_inf_Qa_mul S g (g⁻¹) (g⁻¹ * k), mul_inv_cancel,
    show g * (g⁻¹ * k) = k by group, S.Qa_one] at h8

end CFSG.GF2Type.Smith1980Orth

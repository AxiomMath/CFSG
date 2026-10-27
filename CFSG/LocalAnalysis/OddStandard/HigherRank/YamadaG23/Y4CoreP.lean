module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JStr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4M2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_prod_cases (c : Ctx4 s e) {k : G} (hk : Y52K s k) {x : G} (hx : x ∈ M2 s)
    (hxB : x ∉ s.fr.B) :
    x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ thompsonSubgroup s.fr.B ∨
      ∃ j ∈ thompsonSubgroup s.fr.B,
        x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) = j * (s.fr.a₁ * s.fr.a₂) := by
  have hxC : x ∈ s.C₂ := y4_M2_le_C2 c.toF33 hx
  have hxP : x ∉ f3P s := fun hxP =>
    hxB (by
      have h : x ∈ M2 s ⊓ f3P s := ⟨hx, hxP⟩
      rwa [y4_M2_inf_P c] at h)
  have hkH : k ∈ normIn s.H s.fr.B := ⟨s3_L_le_H s c.hS hk.mem.1, hk.mem.2⟩
  have hk2H : k ^ 2 ∈ normIn s.H s.fr.B := (normIn s.H s.fr.B).pow_mem hkH 2
  have hkx : k * x * k⁻¹ ∈ M2 s := y54_M2_inv c.toF33 k hkH x hx
  have hk2x : k ^ 2 * x * (k ^ 2)⁻¹ ∈ M2 s := y54_M2_inv c.toF33 (k ^ 2) hk2H x hx
  have hprodP : x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ f3P s :=
    y52_cover_prod c.toF33 hk hxC hxP
  have hprodM : x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ M2 s :=
    (M2 s).mul_mem ((M2 s).mul_mem hx hkx) hk2x
  have hprodB : x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ s.fr.B := by
    have h : x * (k * x * k⁻¹) * (k ^ 2 * x * (k ^ 2)⁻¹) ∈ M2 s ⊓ f3P s := ⟨hprodM, hprodP⟩
    rwa [y4_M2_inf_P c] at h
  exact y4_B_cases c.toF33 _ hprodB

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import CFSG.ClassicalInvolution.Generic.TypeCSetup2P1
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupBridge

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime]

theorem smallTypeCSetup_of_frame (hexotic : ExoticLeviBlock p f)
    (hframe : TypeCBalancedFrame p f) : SmallTypeCSetup p f :=
  smallTypeCSetup_of_inputs hexotic hframe typeCP1Step

theorem smallTypeCSetup_of_parts_P1 (hexotic : ExoticLeviBlock p f)
    (h1 : TypeCEdgeTriangle p f) (h2a : TypeCAxisWeakClassical p f)
    (h2b : TypeCAxisWeakS p f) (h2c : TypeCAxisTwo p f) (h3 : TypeCFrameSide p f) :
    SmallTypeCSetup p f :=
  smallTypeCSetup_of_parts hexotic h1 h2a h2b h2c h3 typeCP1Step

theorem smallTypeCSetup_of_baseS_P1 (hexotic : ExoticLeviBlock p f)
    (h1 : TypeCEdgeTriangle p f) (h2a : TypeCAxisWeakClassical p f) (h2b : SmallTypeCBaseS p f)
    (h2c : TypeCAxisTwo p f) (h3 : TypeCFrameSide p f) : SmallTypeCSetup p f :=
  smallTypeCSetup_of_baseS hexotic h1 h2a h2b h2c h3 typeCP1Step

theorem typeCEdgeTriangle_of_conj
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
      TypeCBranch p f G K z → ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G),
        K₁ ∈ CoreAssembly.conjClass K → K₂ ∈ CoreAssembly.conjClass K →
          IsClassicalMember p f K₁ z₁ → IsClassicalMember p f K₂ z₂ → Commutes K₁ K₂ →
            z₁ ≠ z₂ → ∃ g : G, g * z * g⁻¹ = z₁ * z₂) :
    TypeCEdgeTriangle p f := by
  intro G _ _ _ K z hbr K₁ K₂ z₁ z₂ h₁ h₂ c₁ c₂ hc hne
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h0
    · simpa using hbr.five
    · exact h0
  obtain ⟨g, hg⟩ := h G K z hbr K₁ K₂ z₁ z₂ h₁ h₂ c₁ c₂ hc hne
  have h12 : z₁ * z₂ = z₂ * z₁ := hc z₁ c₁.mem z₂ c₂.mem
  have h₃ : conjSub g K ∈ CoreAssembly.conjClass K := ⟨g, rfl⟩
  have c₃ : IsClassicalMember p f (conjSub g K) (z₁ * z₂) := hg ▸ hbr.cls.conj g
  have d₁ : z₁ ≠ z₁ * z₂ := fun e => c₂.ne_one (by simpa using e.symm)
  have d₂ : z₂ ≠ z₁ * z₂ := fun e => c₁.ne_one (by simpa using e.symm)
  refine ⟨conjSub g K, z₁ * z₂, h₃, c₃, ?_, ?_, Ne.symm d₁, Ne.symm d₂⟩
  · refine commutes_of_not_a2Configuration hbr.odd hf hbr.cls hbr.noA2 h₁ h₃ c₁ c₃ d₁ ?_
    calc z₁ * (z₁ * z₂) = z₁ * (z₂ * z₁) := by rw [h12]
      _ = (z₁ * z₂) * z₁ := (mul_assoc _ _ _).symm
  · refine commutes_of_not_a2Configuration hbr.odd hf hbr.cls hbr.noA2 h₂ h₃ c₂ c₃ d₂ ?_
    calc z₂ * (z₁ * z₂) = (z₂ * z₁) * z₂ := (mul_assoc _ _ _).symm
      _ = (z₁ * z₂) * z₂ := by rw [h12]

end CFSG.ClassicalInvolution.Generic.TypeCSetup

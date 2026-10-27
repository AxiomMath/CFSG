module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem inf_oddIn_eq_bot_of_syl {M T : Subgroup G} (hT : IsSylowTwoIn T M) :
    T ⊓ oddIn M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_of_le_two_group_of_le_odd (P := T) (O := oddIn M)
    (GrS4.isPGroup_of_isSylowTwoIn hT) ?_ inf_le_left inf_le_right
  rw [oddIn, card_map_of_injective (subtype_injective _)]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem eq_of_rho_eq {M T : Subgroup G} (hT : IsSylowTwoIn T M) {ρ : ↥M →* WrE}
    (hker : ∀ m : ↥M, ρ m = 1 ↔ (m : G) ∈ oddIn M) {m₁ m₂ : ↥M} (h₁ : (m₁ : G) ∈ T)
    (h₂ : (m₂ : G) ∈ T) (h : ρ m₁ = ρ m₂) : m₁ = m₂ := by
  have h1 : ρ (m₁⁻¹ * m₂) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ oddIn M := (hker _).mp h1
  have h3 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ T := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (inv_mem h₁) h₂
  have h4 : ((m₁⁻¹ * m₂ : ↥M) : G) ∈ T ⊓ oddIn M := mem_inf.mpr ⟨h3, h2⟩
  rw [inf_oddIn_eq_bot_of_syl hT, mem_bot] at h4
  have h5 : m₁⁻¹ * m₂ = 1 := Subtype.ext h4
  exact inv_mul_eq_one.mp h5

theorem mem_imgT_iff {M T : Subgroup G} {ρ : ↥M →* WrE} {z : WrE} :
    z ∈ imgT T M ρ ↔ ∃ m : ↥M, (m : G) ∈ T ∧ ρ m = z := by
  unfold imgT
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mp hm, e⟩,
    fun ⟨m, hm, e⟩ => ⟨m, mem_subgroupOf.mpr hm, e⟩⟩

end CFSG.ComponentClassification.GrSLit.L34Tw

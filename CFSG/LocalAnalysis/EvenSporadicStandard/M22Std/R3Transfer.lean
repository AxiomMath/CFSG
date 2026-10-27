module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathEnd

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.ABGLocalTools CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_fusion_conj [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) {S S0 : Subgroup G} (hS : IsPGroup 2 S) (hzS : z ∈ S)
    (hT : IsSylowOf 2 (S ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hS0 : S0 ≤ S) (hidx : S0.relIndex S = 2) (hz0 : z ∉ S0)
    (hfus : ∀ x ∈ S, x * x = 1 → x ∉ S0 → IsConj z x → ∃ s ∈ S, x = s⁻¹ * z * s) :
    ∃ g : G, g⁻¹ * z * g ∈ S0 := by
  by_contra hX
  push Not at hX
  have hfus' : ∀ g : G, g⁻¹ * z * g ∈ S → ∃ s ∈ S, g⁻¹ * z * g = s⁻¹ * z * s := by
    intro g hg
    have hx2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz2]; group
    refine hfus _ hg hx2 (hX g) (isConj_iff.2 ⟨g⁻¹, ?_⟩)
    group
  have hSidx := sylow_of_fusion hS hzS hT hfus'
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hS hSidx hS0 hidx hzS hz0 hz2'
  exact hX g hg

end CFSG.EvenSporadicStandard.M22Std

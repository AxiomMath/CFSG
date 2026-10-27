module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7T21C
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Final

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem a7_kPerp_eq_or_dConnected_of_thmE (hE : A7ThmE) (hs : Std2A7 Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) :
    KPerp Ω K = twinSet Ω K ∨ (DConnected Ω ∧ ∀ J ∈ omegaOfSet Ω (twinSet Ω K), ∀ t : G,
      IsUniqueInvolution J t → alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) := by
  by_cases h : KPerp Ω K = twinSet Ω K
  · exact Or.inl h
  · right
    have hpre : Pre2A7 Ω K := hs.toPre2A7
    have hΩ : HypOmegaGen Ω := hpre.hyp
    obtain ⟨J₀, hJ₀, -⟩ := exists_mem_omegaOfSet_twinSet hΩ hpre.classical hpre.mem hz h
    obtain ⟨t₀, ht₀⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ₀.1
    exact ⟨Hat2A7S8.T21.dConnected_of_alpha_bot hE hs hz hK' hne hJ₀ ht₀
      (Hat2A7S8.T21.alphaOf_eq_bot_of_thmE hE hs hz hK' hne hJ₀ ht₀),
      fun J hJ t ht => Hat2A7S8.T21.alphaOf_eq_bot_of_thmE hE hs hz hK' hne hJ ht⟩

theorem a7C21_2_of_thmE (hE : A7ThmE) : A7C21_2 := by
  intro G _ _ _ Ω K K' z hs
  rcases a7_kPerp_eq_or_dConnected_of_thmE hE hs.stand hs.hz hs.hK' hs.hne with h | ⟨hconn, -⟩
  · exact h
  · exact absurd hconn hs.disconnected

end Final

end CFSG.ClassicalInvolution.Hat2A7S

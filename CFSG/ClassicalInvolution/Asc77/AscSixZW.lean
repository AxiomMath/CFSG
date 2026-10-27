module

public import CFSG.ClassicalInvolution.Asc77.AscSix610
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem E187C.e18_zW_of {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K R W : Subgroup G} {S : Sylow 2 G} (hc : ConjInvariant Ω) (hK : K ∈ Ω)
    (hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G))
    (hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hzK0 : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (hquatR : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → IsQuatSub Q)
    (heq : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → IsPGroup 2 A → 4 ≤ Nat.card A → A ≤ K →
      A ≤ J → K = J)
    (heta : ∀ {S : Subgroup G} {η : Set (Subgroup G)} {K U : Subgroup G}, η ∈ etaSet Ω S →
      K ∈ Ω → U ∈ UinS Ω S → U ≤ K → ∃ V ∈ η, V ≤ K)
    (h4U : ∀ {U : Subgroup G}, U ∈ USet Ω → 4 ≤ Nat.card U)
    (h2U : ∀ {U : Subgroup G}, U ∈ USet Ω → IsPGroup 2 U) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W := by
  obtain ⟨hRR, hRK, hRS⟩ := hR
  obtain ⟨z, hz⟩ := hzK0 hK
  refine ⟨z, hz, ?_⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hRR
  have hquat := hquatR hRR
  have hJK : K = J := heq hK hJ hRJ.2.1 (by have := hquat.eight_le; omega) hRK hRJ.1
  have hRK' : IsSylow2In R K := hJK ▸ hRJ
  obtain ⟨U₀, hU₀R, hcyc, hcard⟩ := hquat.exists_cyclic_index_two
  have hU₀ : U₀ ∈ USet Ω := mem_USet_of_natCard hK hRK' hU₀R hcyc hcard
  obtain ⟨hWW, hWS, -⟩ := hW
  obtain ⟨η, hη, hWη⟩ := hWW
  obtain ⟨S₁, hS₁, -⟩ := hη
  have hAW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂_of_le V hV le_rfl
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hAW V hV).trans hWS
  have hηS' : η ∈ etaSet Ω (S : Subgroup G) := mem_etaSet_of_le hc hS₁ hηS
  obtain ⟨V, hVη, hVK⟩ := heta hηS' hK ⟨hU₀, hU₀R.trans hRS⟩ (hU₀R.trans hRK)
  have hVU : V ∈ USet Ω := (hS₁.1 hVη).1
  have h4 := h4U hVU
  have hzV : z ∈ V := mem_of_isUniqueInvolution_of_isPGroup hz hVK (h2U hVU) (by omega)
  exact hAW V hVη hzV

set_option linter.unusedSectionVars false in
theorem e18_zW : E18_zW p f := by
  intro G _ _ Ω K S R W H c
  exact E187C.e18_zW_of c.stand.hyp.conjInvariant c.stand.mem c.stand.hR c.stand.hW
    (fun hK => c.stand.hyp.exists_uniqueInvolution c.stand.odd c.stand.five hK)
    (fun hQ => c.stand.hyp.isQuatSub_of_mem_RSet c.stand.odd hQ)
    (fun hK hJ hA h4 hAK hAJ => c.stand.hyp.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (fun h hK hU hUK => exists_mem_of_mem_etaSet c.stand.odd c.stand.hyp h hK hU hUK)
    (fun hU => by
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := c.stand.hyp.exists_data_of_mem_USet c.stand.odd hU
      exact h4)
    (fun hU => c.stand.hyp.isPGroup_of_mem_USet c.stand.odd hU)

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.ClassicalInvolution.Asc77.AscE187Conj

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E187E4C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ A : Subgroup G, IsPGroup 2 A → R ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
            (Subgroup.centralizer (A : Set G)) → Subgroup.centralizer (A : Set G) ≤ H

variable {p f}

section Finite

variable [Finite G] {Ω : Set (Subgroup G)}

theorem WSet.exists_normalized_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (S' : Sylow 2 G) :
    ∃ W' ∈ WSet Ω, W' ≤ (S' : Subgroup G) ∧ ∀ s ∈ (S' : Subgroup G), conjSub s W' = W' := by
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S'
  refine ⟨⨆ U ∈ η, U, ⟨η, ⟨S', hη, hinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2, ?_⟩
  intro s hs
  rw [conjSub_iSup₂]
  apply le_antisymm
  · exact iSup₂_le fun U hU => le_iSup₂_of_le _ (hinv s hs U hU) le_rfl
  · refine iSup₂_le fun U hU => ?_
    have hU' : conjSub s⁻¹ U ∈ η := hinv s⁻¹ ((S' : Subgroup G).inv_mem hs) U hU
    have : U = conjSub s (conjSub s⁻¹ U) := (conjSub_conjSub_inv s U).symm
    rw [this]
    exact le_iSup₂_of_le (conjSub s⁻¹ U) hU' le_rfl

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.of_sylow (c : MinCex p f Ω K S R W H) {S' : Sylow 2 G} {W' : Subgroup G}
    (hRS' : R ≤ (S' : Subgroup G)) {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S' : R' ≤ (S' : Subgroup G))
    (hW' : W' ∈ WSet Ω) (hW'S' : W' ≤ (S' : Subgroup G))
    (hW'n : ∀ s ∈ (S' : Subgroup G), conjSub s W' = W') : MinCex p f Ω K S' R W' H where
  stand :=
    { odd := c.stand.odd
      five := c.stand.five
      hyp := c.stand.hyp
      below := c.stand.below
      mem := c.stand.mem
      aEmpty := c.stand.aEmpty
      twin := ⟨K', hK', hne, R', hR', hR'K', hR'S'⟩
      hR := ⟨c.stand.hR.1, c.stand.hR.2.1, hRS'⟩
      hW := ⟨hW', hW'S', hW'n⟩ }
  hyp := ⟨c.hyp.trans, c.hyp.cent⟩
  proper := c.proper
  minimal := c.minimal

theorem MinCex.centralizer_le_H (h4 : E187E4C p f) (c : MinCex p f Ω K S R W H)
    {K' R' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {A : Subgroup G}
    (hA : IsPGroup 2 A) (hRA : R ⊔ R' ≤ Subgroup.centralizer (A : Set G))
    (hX : Subgroup.centralizer (A : Set G) ≠ ⊤) : Subgroup.centralizer (A : Set G) ≤ H := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  obtain ⟨S', hRS', hR'S', hSyl⟩ :=
    E187C.exists_sylow_inf_centralizer c.stand.hR.2.2 hR'S hRA
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hp hq hΩ S'
  have c' := c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n
  exact h4 G Ω K S' R W' H c' K' hK' hne R' hR' hR'K' hR'S' A hA hRA hX hSyl

end Finite

end CFSG.ClassicalInvolution.Asc77

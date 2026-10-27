module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIEvenClassicalBlock
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddUnitary
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddOrthogonal

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OutcomeLocal

theorem commuting_block_classical_overgroup_residual_odd_orthogonal {G : Type} [Group G]
    [Finite G] {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G))
    (hrep : CFSG.Milestones.ClassicalRep (L ⧸ center L)) :
    ∃ (t : StatedLieTag) (n p f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      p.Prime ∧ Odd p ∧ 1 ≤ f ∧ StatedClassicalModel (L ⧸ center L) t n p f := by
  obtain ⟨t, n, p, f, hT⟩ := hrep
  have hmem := CFSG.Milestones.statedClassicalModel_tag_mem _ t n p f hT
  obtain ⟨hp, hf, -⟩ := hT.1
  by_cases hp2 : p = 2
  ·
    subst hp2
    exfalso
    have heven' := fun t ht => commuting_block_even_classical_overgroup_exclusion hq heven hJ hΔ
      hL hML hLH t ht n f
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact heven' _ (Or.inl rfl) hT
    · exact heven' _ (Or.inr (Or.inl rfl)) hT
    · exact heven' _ (Or.inr (Or.inr (Or.inl rfl))) hT
    · obtain ⟨⟨-, -, -, h2⟩, -⟩ := hT
      exact h2 rfl
    · exact heven' _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hT
    · exact heven' _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hT
  ·
    have hodd : Odd p := hp.odd_of_ne_two hp2
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      exfalso
      obtain ⟨⟨-, -, hn, -⟩, k, _, _, hk, ⟨e⟩⟩ := hT
      have : CharP k p := finite_field_prime_power_characteristic hp hf hk
      exact commuting_block_odd_projective_linear_overgroup_exclusion hq heven hV hJ hΔ hL hML
        hLH n k hn (by rw [ringChar.eq k p]; exact hp2)
        ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm⟩
    · exact absurd hT
        (commuting_block_odd_unitary_overgroup_exclusion hq heven hV hJ hΔ hL hML hLH n p f hp2)
    · exact absurd hT
        (commuting_block_odd_symplectic_overgroup_exclusion hq heven hV hJ hΔ hL hML hLH n p f hp2)
    · exact ⟨_, n, p, f, Or.inl rfl, hp, hodd, hf, hT⟩
    · exact ⟨_, n, p, f, Or.inr (Or.inl rfl), hp, hodd, hf, hT⟩
    · exact ⟨_, n, p, f, Or.inr (Or.inr rfl), hp, hodd, hf, hT⟩

theorem commuting_block_escaping_overgroup_not_classical {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hV : ∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4)
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial)
    {L : Subgroup G} (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ CFSG.Milestones.ClassicalRep (L ⧸ center L) := by
  intro hrep
  obtain ⟨t, n, p, f, ht, -, hodd, -, hT⟩ :=
    commuting_block_classical_overgroup_residual_odd_orthogonal hq heven hV hJ hΔ hL hML hLH hrep
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  exact commuting_block_odd_orthogonal_overgroup_exclusion hq heven hV hJ hΔ hL hML hLH t ht n p f
    hp2 hT

end CFSG.LocalAnalysis.ComponentInitial

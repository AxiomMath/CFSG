module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G]

theorem ne_four_one_of_psl {Q : Type} [Group Q] {n m : ℕ}
    (h : StatedClassicalModel Q .PSL n 2 m) (h8 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 8))) :
    (n, m) ≠ (4, 1) := by
  intro hnm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnm
  exact h8 (CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
    (Or.inl ⟨by decide, h⟩))

theorem nonempty_classicalModel {A : Subgroup G}
    (h : RankTwoClassicalEvenType (rankTwoQuot A)) : Nonempty (ClassicalModel A) := by
  obtain ⟨hL | hU | hS | ⟨n, m, hn, hO | hO⟩, h8, -⟩ := h
  · obtain ⟨n, m, hn, hL⟩ := hL
    obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hL
    exact ⟨.linear n m hn hm (ne_four_one_of_psl hL h8) K hK e⟩
  · obtain ⟨n, m, hn, ⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := hU
    exact ⟨.unitary n m hn hm K hK e⟩
  · obtain ⟨n, m, -, ⟨-, hm, hn, hnm⟩, K, _, _, hK, ⟨e⟩⟩ := hS
    exact ⟨.symplectic n m hn hm hnm K hK e⟩
  · obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := hO
    exact ⟨.orthPlus n m hn hm K hK e⟩
  · obtain ⟨⟨-, hm, -⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hO
    exact ⟨.orthMinus n m hn hm K hK b c hbc e⟩

variable [Finite G]

theorem hyp31_of (hII : ClassicalHypII) {A : Subgroup G} (hH : RankTwoHyp G A)
    (hO : standardComponentOddCore G = ⊥) (hT : RankTwoClassicalEvenType (rankTwoQuot A)) :
    AS76b.Hyp31 A :=
  ⟨hH.standard, hII _ hH.standard.1.1 hT, hO, lt_of_lt_of_le one_lt_two hH.rank, hH.not_normal⟩

end CFSG.ComponentClassification.RankTwoClassical

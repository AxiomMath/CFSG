module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceGlue

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding

theorem BlockIbParab.of_hyp {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (h : BlockThreeIbHyp M S L D x) (h2 : NineThreeTwo M S L) :
    BlockIbParab (barM M L) (blockPL M S L) := by
  obtain ⟨-, hA, hL, -⟩ := h
  exact ⟨hL.component, ToralReduce.odd_card_center_barM hL.toIsTwoPrimeComponent, h2.2.1,
    barM_normalizer_inf_ne_of_asc81bHyp hA hL⟩

theorem BlockIbData.of_hyp {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (h : BlockThreeIbHyp M S L D x) : BlockIbData (barM M L) (blockPL M S L) D x := by
  obtain ⟨-, -, -, -, -, cop, rank, cyc, Dperf, Dle, Dcyc, Dcarry, hx, hx3, hxC, free⟩ := h
  exact ⟨cop, rank, cyc, Dperf, Dle, Dcyc, Dcarry, hx, hx3, hxC, free⟩

theorem kFactBlockCentRankIbThree_of_families (hA : BlockIbRankFam (IsLieOf IdxA))
    (h2A : BlockIbRankFam (IsLieOf IdxTwistedA)) (hB : BlockIbRankFam (IsLieOf IdxB))
    (hD : BlockIbRankFam (IsLieOf IdxD)) (h2D : BlockIbRankFam (IsLieOf IdxTwistedD))
    (hG2 : BlockIbRankFam (IsLieOf IdxG2)) (hS : BlockIbRankFam IsSmallTwoOrG2)
    (hRest : BlockIbRankRest) : KFactBlockCentRankIbThree := by
  intro G _ _ M S L D x h E hEL hEP hED hEab hE9 t ht htE htF
  by_cases h2 : NineThreeTwo M S L
  · have hP := BlockIbParab.of_hyp h h2
    have hData := BlockIbData.of_hyp h
    rcases isClassicalTwoOrG2_family_cases h2.1 with hf | hf | hf | hf | hf | hf | hf
    · exact hA _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact h2A _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact hB _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact hD _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact h2D _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact hG2 _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
    · exact hS _ _ _ D x hP hf hData E hEL hEP hED hEab hE9 t ht htE htF
  · exact hRest G M S L D x h h2 E hEL hEP hED hEab hE9 t ht htE htF

theorem kFactBlockCentAbThreeIb_of_families (hA : BlockIbAbFam (IsLieOf IdxA))
    (h2A : BlockIbAbFam (IsLieOf IdxTwistedA)) (hB : BlockIbAbFam (IsLieOf IdxB))
    (hD : BlockIbAbFam (IsLieOf IdxD)) (h2D : BlockIbAbFam (IsLieOf IdxTwistedD))
    (hG2 : BlockIbAbFam (IsLieOf IdxG2)) (hS : BlockIbAbFam IsSmallTwoOrG2)
    (hRest : BlockIbAbRest) : KFactBlockCentAbThreeIb := by
  intro G _ _ M S L D x h U hUL hUP hUD hU3
  by_cases h2 : NineThreeTwo M S L
  · have hP := BlockIbParab.of_hyp h h2
    have hData := BlockIbData.of_hyp h
    rcases isClassicalTwoOrG2_family_cases h2.1 with hf | hf | hf | hf | hf | hf | hf
    · exact hA _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact h2A _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact hB _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact hD _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact h2D _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact hG2 _ _ _ D x hP hf hData U hUL hUP hUD hU3
    · exact hS _ _ _ D x hP hf hData U hUL hUP hUD hU3
  · exact hRest G M S L D x h h2 U hUL hUP hUD hU3

end CFSG.HardMathSupport.Curtis.UnitaryLevi

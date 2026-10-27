module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.TypeTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3KFact
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Reduction


theorem kFactBlockE9Transitive_of (h93 : Asc81bNineThree) (hK3 : KFactNineThreeThreeBig)
    (hPL : KFactBlockPLElem) : KFactBlockE9Transitive := by
  intro G _ _ M S L hK hA hQS hL hnX hns hsolv hM3 hL3 hK2 hCK E _ hE9 hEK hEL hEC
  have hconc : NineThreeConclusion M S L := h93 G M S L hK hA hL
  set Lb := barM M L
  set Kb := barM M (Subgroup.normalizer (S : Set G))
  set PL := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  set J := (PL.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb))
  have hPLeq : PL = Kb ⊓ Lb := CFSG.AGLEmbeddingD2.McLaughlin.barM_normalizer_inf_eq hQS
  have hPLL : PL ≤ Lb := hPLeq.le.trans inf_le_right
  have hPLK : PL ≤ Kb := hPLeq.le.trans inf_le_left
  have hEJ : (projHom hEL).range ≤ J := range_le_block hQS hEL hEK hCK
  have hcardE : Nat.card (projHom hEL).range = 9 := (card_range_projHom hEL hEC).trans hE9
  have h9J : 9 ∣ Nat.card J := hcardE ▸ Subgroup.card_dvd_of_le hEJ
  have hJP : Nat.card J ∣ Nat.card PL := card_map_subgroupOf_dvd hPLL
  have h9P : 9 ∣ Nat.card PL := h9J.trans hJP
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnX
  ·
    have hel := hPL G M S L hK hA hQS hL hnX hns (Or.inr (Or.inl h2)) hsolv hM3
    have h27 : ¬ 27 ∣ Nat.card J := fun h =>
      not_twentySeven_dvd_card hPLK hel hK2 (h.trans hJP)
    have hsyl := not_three_dvd_index_of_card hEJ hcardE h27
    have hnot : ¬ IsSylowTwoOf (pCoreOf 2 PL) Lb := by
      rw [← h2.2.2]
      exact fun h => hns (isSylowTwoOf_inf_of_barM hL.le hQS hA.twoRadical.isPGroup h)
    refine not_transitive_of_typeTwo hL.component.2.2 h2.1 h2.2.1 hnot hsolv hEL hEC hE9 hEJ
      hsyl (fun x hx => hx.1.2) (fun x hx => ?_)
    have h := mem_normalizer_inf (Subgroup.le_normalizer hx.1.1) hx.1.2
    rw [← hPLeq] at h
    exact h
  ·
    exact (hK3 G M S L hK hA hL hnX hns h3 hL3 hsolv).elim
  ·
    obtain ⟨-, -, -, -, ⟨e⟩⟩ := h4
    have h24 : Nat.card J = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    rw [h24] at h9J
    norm_num at h9J
  ·
    exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := h5
    have hrb : Open.pRank 3 (⊤ : Subgroup ↥Lb) = Open.pRank 3 L := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
        (by norm_num) M L hL.le]
    have hrk :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
    have hle := pRank_three_alternating_le (N := 7)
    omega
  ·
    obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact (not_nine_dvd_of_perm (le_four_of_blockPLThreeSolv_perm hsolv e) e h9P).elim
  ·
    obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact (not_nine_dvd_of_perm (le_four_of_blockPLThreeSolv_perm hsolv e) e h9P).elim
  · exact (not_nineThreeEight h8 hsolv).elim

end Reduction

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive

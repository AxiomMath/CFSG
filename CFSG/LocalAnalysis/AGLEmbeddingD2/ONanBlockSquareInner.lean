module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerParabolic
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerStep
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerTypes
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerSp
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique InnerStep InnerTypes

theorem kFactBlockAltFiveSquareInner_of_types (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hT : CitedBlockTransvectionPLType) (hA7 : CitedBlockAltSevenPL)
    (hP : KFactBlockAltFiveSquareParabolic) : KFactBlockAltFiveSquareInner := by
  intro G _ _ M S L U hK hA hL hX hS hB hUM hUN hUL φ hφ hφ1
  have hSL := h86 G M S hK hA _ hL.component
  have h3600 : Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∣
      Nat.card (blockPL M S L) := card_dvd_card_blockPL hSL hB hUM hUN hUL φ hφ hφ1
  have h25 : 25 ∣ Nat.card (blockPL M S L) := by
    have h : 25 ∣ Nat.card (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
      rw [Nat.card_prod, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact h.trans h3600
  have h5 : 5 ∣ Nat.card (blockPL M S L) := (by norm_num : 5 ∣ 25).trans h25
  rcases h93 G M S L hK hA hL with h1 | h2 | h3t | h4 | h5t | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hP G M S L U hK hA hL hX hS hB h2 hUM hUN hUL φ hφ hφ1
  · rcases citedBlockTransvectionPL_of_type hT G M S L hK hA hL hX hS h3t with
      ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      rw [pRank_eq_of_pCore_quotient e Nat.prime_three (by norm_num)]
      exact hk.trans (le_pRank_three_catSp k d hk hd)
    · exfalso
      have h25n : 25 ∣ Nat.card (Equiv.Perm (Fin n)) :=
        dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h25
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h25n
      have := ten_le_of_dvd_factorial h25n
      omega
  · exact absurd (h5.trans (card_blockPL_dvd_of_nineThreeFour h4)) (by norm_num)
  · exact absurd (h5.trans (hA7 G M S L hK hA hL hX hS h5t)) (by norm_num)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    have h25n : 25 ∣ Nat.card (Equiv.Perm (Fin n)) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h25
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h25n
    have hn10 := ten_le_of_dvd_factorial h25n
    rw [pRank_eq_of_pCore_quotient e Nat.prime_three (by norm_num)]
    exact (le_pRank_perm Nat.prime_three (k := 3) (by omega))
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    have h25n : 25 ∣ Nat.card (Equiv.Perm (Fin n)) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h25
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h25n
    have hn10 := ten_le_of_dvd_factorial h25n
    rw [pRank_eq_of_pCore_quotient e Nat.prime_three (by norm_num)]
    exact (le_pRank_perm Nat.prime_three (k := 3) (by omega))
  · obtain ⟨-, N, r, ⟨a, ha⟩, hr, h0, h2', h4', -, e, -⟩ := h8
    have hm6 : 6 ≤ N - 2 * r := by omega
    have h25n : 25 ∣ Nat.card (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h25
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fin] at h25n
    have h3 := three_le_div_add_div h25n hm6
    rw [pRank_eq_of_pCore_quotient e Nat.prime_three (by norm_num)]
    exact h3.trans ((add_le_add (le_pRank_perm Nat.prime_three (k := r / 3) (by omega))
      (le_pRank_perm Nat.prime_three (k := (N - 2 * r) / 3) (by omega))).trans
      (pRank_prod_ge Nat.prime_three.one_lt))

end CFSG.AGLEmbeddingD2

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerParabolic
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerStep
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockInnerTypes
import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanSpFiveRank
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVTypes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique InnerStep InnerTypes

theorem kFactBlockFiveHeisInner_of_types (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hT : CitedBlockTransvectionPLType) (hA7 : CitedBlockAltSevenPL)
    (hP : KFactBlockFiveHeisParabolic) : KFactBlockFiveHeisInner := by
  intro G _ _ M S L U hK hA hL hX hS hB hUM hUN hUL hU125 hUnc hUbot
  have hSL := h86 G M S hK hA _ hL.component
  have h125 : 125 ∣ Nat.card (blockPL M S L) := by
    have h := card_dvd_card_blockPL hSL hB hUM hUN hUL (MonoidHom.id U) Function.surjective_id
      (fun u hu => by rw [hUbot] at hu; exact Subgroup.mem_bot.mp hu)
    rw [hU125] at h
    exact h
  have h5 : 5 ∣ Nat.card (blockPL M S L) := (by norm_num : 5 ∣ 125).trans h125
  rcases h93 G M S L hK hA hL with h1 | h2 | h3t | h4 | h5t | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hP G M S L U hK hA hL hX hS hB h2 hUM hUN hUL hU125 hUnc hUbot
  · rcases citedBlockTransvectionPL_of_type hT G M S L hK hA hL hX hS h3t with
      ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      rw [pRank_eq_of_pCore_quotient e Nat.prime_five (by norm_num)]
      exact SpFive.three_le_pRank_five_catSp k d hk hd
        (dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h125)
    · exfalso
      have h125n : 125 ∣ Nat.card (Equiv.Perm (Fin n)) :=
        dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h125
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h125n
      have := fifteen_le_of_dvd_factorial h125n
      omega
  · exact absurd (h5.trans (card_blockPL_dvd_of_nineThreeFour h4)) (by norm_num)
  · exact absurd (h5.trans (hA7 G M S L hK hA hL hX hS h5t)) (by norm_num)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    have h125n : 125 ∣ Nat.card (Equiv.Perm (Fin n)) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h125
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h125n
    have hn15 := fifteen_le_of_dvd_factorial h125n
    rw [pRank_eq_of_pCore_quotient e Nat.prime_five (by norm_num)]
    exact le_pRank_perm Nat.prime_five (k := 3) (by omega)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    have h125n : 125 ∣ Nat.card (Equiv.Perm (Fin n)) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h125
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h125n
    have hn15 := fifteen_le_of_dvd_factorial h125n
    rw [pRank_eq_of_pCore_quotient e Nat.prime_five (by norm_num)]
    exact le_pRank_perm Nat.prime_five (k := 3) (by omega)
  · obtain ⟨-, N, r, -, hr, -, -, -, -, e, -⟩ := h8
    have h125n : 125 ∣ Nat.card (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r))) :=
      dvd_card_of_dvd_card_pCore_quotient e (by norm_num) h125
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fin] at h125n
    have h3 := three_le_div_five_add_div_five h125n
    rw [pRank_eq_of_pCore_quotient e Nat.prime_five (by norm_num)]
    exact h3.trans ((add_le_add (le_pRank_perm Nat.prime_five (k := r / 5) (by omega))
      (le_pRank_perm Nat.prime_five (k := (N - 2 * r) / 5) (by omega))).trans
      (pRank_prod_ge Nat.prime_five.one_lt))

end CFSG.AGLEmbeddingD2

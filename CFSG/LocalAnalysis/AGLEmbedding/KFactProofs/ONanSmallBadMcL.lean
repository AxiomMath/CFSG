module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import Certificates.Certificate9751

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.McL

open CFSG.AGLEmbeddingD2 CFSG.RankThree.Native CFSG.Sporadic.Schreier Certificates.MaxD2Heis
  CFSG.AGLEmbedding.KFactProofs.SmallIdent CFSG.AGLEmbedding.KFactProofs.RankOneCore

theorem mcl_five_noncomm_P :
    ∃ R : Subgroup (Equiv.Perm (Fin 275)), R ≤ mcl275P ∧ Nat.card R = 5 ^ 3 ∧
      ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P,
      ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P,
        a * b * a⁻¹ * b⁻¹ ∉ R := by
  have h := CFSG.AGLEmbedding.MaxD2.noncomm_of_checkHeis (S := [mcl275A, mcl275B])
    (D := mclFiveDataP) rfl mclFiveDataP_hS
    (by
      have h1 : [mcl275A, mcl275B].length = 2 := rfl
      have h2 : mclFiveDataP.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [mclP_closure_eq]; exact card_mclP) mcl_five_check_P Certificates.certificate9751
  rwa [mclP_closure_eq] at h

theorem not_normalizerQuotientComm_mclP :
    ¬ NormalizerQuotientComm 5 mcl275P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R, hRG, hRcard, a, ha, b, hb, hab⟩ := mcl_five_noncomm_P
  have hP : Nat.card mcl275P = 5 ^ 3 * 7185024 := by
    rw [mcl275P_eq, card_mclP]
    norm_num
  have hfac : (Nat.card mcl275P).factorization 5 = 3 := by
    rw [hP]
    exact factorization_pow_mul (by norm_num) (by norm_num) (by norm_num)
  have hcard' : Nat.card (R.subgroupOf mcl275P) = 5 ^ (Nat.card mcl275P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard, hfac]
  let T : Sylow 5 mcl275P := Sylow.ofCard (R.subgroupOf mcl275P) hcard'
  have hT : (T : Subgroup mcl275P) = R.subgroupOf mcl275P := rfl
  have hTne : (T : Subgroup mcl275P) ≠ ⊥ := by
    intro hbot
    rw [hT] at hbot
    have h1 : Nat.card (R.subgroupOf mcl275P) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard] at h1
    norm_num at h1
  have hN : ∀ g (hg : g ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 275))) ⊓ mcl275P),
      (⟨g, hg.2⟩ : mcl275P) ∈ Subgroup.normalizer ((T : Subgroup mcl275P) : Set mcl275P) := by
    intro g hg
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hRG]
    exact hg.1
  refine not_normalizerQuotientComm_of_witness T hTne (hN a ha) (hN b hb) fun hmem => hab ?_
  rw [hT, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem not_normalizerQuotientComm_isMcL
    {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (hK : CFSG.AGLEmbedding.IsSporadicGroup .McL L) : ¬ NormalizerQuotientComm 5 L := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  intro hc
  exact not_normalizerQuotientComm_mclP (NormalizerQuotientComm.of_mulEquiv e hc)

end CFSG.AGLEmbedding.KFactProofs.SmallBad.McL

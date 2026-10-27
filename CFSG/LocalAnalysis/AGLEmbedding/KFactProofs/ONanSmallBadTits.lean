module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCheck
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
public import Certificates.Certificate9750
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.Tits

open CFSG.AGLEmbeddingD2 CFSG.Sporadic.Schreier.Tits Certificates.MaxD2Perm
  CFSG.AGLEmbedding.KFactProofs.SmallIdent CFSG.AGLEmbedding.KFactProofs.RankOneCore

section Local


theorem tits_five_noncomm_d :
    ∃ R : Subgroup (Equiv.Perm (Fin 1755)), R ≤ titsD ∧ Nat.card R = 5 ^ 2 ∧
      ∃ a ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 1755))) ⊓ titsD,
      ∃ b ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 1755))) ⊓ titsD,
        a * b * a⁻¹ * b⁻¹ ∉ R := by
  have h := CFSG.AGLEmbedding.MaxD2.noncomm_of_check (S := [titsDGen 0, titsDGen 1])
    (D := titsDData) rfl titsD_hS
    (by
      have h1 : [titsDGen 0, titsDGen 1].length = 2 := rfl
      have h2 : titsDData.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [← titsD_eq_closure_list]; exact card_titsD) tits_five_local_check_d
    Certificates.certificate9750
  rwa [← titsD_eq_closure_list] at h

theorem not_normalizerQuotientComm_titsD : ¬ NormalizerQuotientComm 5 titsD := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨R, hRG, hRcard, a, ha, b, hb, hab⟩ := tits_five_noncomm_d
  have hcard' : Nat.card (R.subgroupOf titsD) = 5 ^ (Nat.card titsD).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard, card_titsD,
      factorization_five_eq_two (by norm_num) (by norm_num) (by norm_num)]
  let T : Sylow 5 titsD := Sylow.ofCard (R.subgroupOf titsD) hcard'
  have hT : (T : Subgroup titsD) = R.subgroupOf titsD := rfl
  have hTne : (T : Subgroup titsD) ≠ ⊥ := by
    intro hbot
    rw [hT] at hbot
    have h1 : Nat.card (R.subgroupOf titsD) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRG).toEquiv, hRcard] at h1
    norm_num at h1
  have hN : ∀ g (hg : g ∈ Subgroup.normalizer (R : Set (Equiv.Perm (Fin 1755))) ⊓ titsD),
      (⟨g, hg.2⟩ : titsD) ∈ Subgroup.normalizer ((T : Subgroup titsD) : Set titsD) := by
    intro g hg
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hRG]
    exact hg.1
  refine not_normalizerQuotientComm_of_witness T hTne (hN a ha) (hN b hb) fun hmem => hab ?_
  rw [hT, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

end Local

section Certified


theorem not_normalizerQuotientComm_isTits {L : Type} [Group L] [Finite L]
    (hK : CFSG.AGLEmbedding.IsTitsGroup L) : ¬ NormalizerQuotientComm 5 L := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  intro hc
  exact not_normalizerQuotientComm_titsD (NormalizerQuotientComm.of_mulEquiv e hc)

end Certified

end CFSG.AGLEmbedding.KFactProofs.SmallBad.Tits

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCIn
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent

theorem kFactL34InvolveIso_of_smallIdent
    (h : KFactSmallIdent) : KFactL34InvolveIso := by
  intro KC _ _ hs hnab hc T hT hΓ hAut L _ hL A f hf
  have hK := isSmallStrongP_of_autRank h hs hnab hc Nat.prime_three (by norm_num) T hT hΓ hAut
  have hdvd : 20160 ∣ Nat.card KC := by
    have h1 : Nat.card L ∣ Nat.card A := Subgroup.card_dvd_of_surjective (f := f) hf
    have h2 : Nat.card A ∣ Nat.card KC := Subgroup.card_subgroup_dvd_card A
    rw [← card_of_isLinThreeFour hL]
    exact h1.trans h2
  rcases hK with hL2 | hU | hA6 | ⟨-, hL34 | hM⟩ | ⟨h5, -⟩ | ⟨h11, -⟩
  · exfalso
    obtain ⟨d, hd, -⟩ := hL2
    exact card_ne_nine_of_isLinTwoIndex hd (by norm_num)
  · exfalso
    rw [card_of_isSmallUnitary_three hU] at hdvd
    omega
  · exfalso
    rw [card_of_isAltTwoP_three hA6] at hdvd
    omega
  · obtain ⟨e₁⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hL34
    obtain ⟨e₂⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hL
    exact ⟨e₁.trans e₂.symm⟩
  · exfalso
    rw [card_of_isM11 hM] at hdvd
    omega
  · omega
  · omega

end CFSG.AGLEmbedding

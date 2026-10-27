module

public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSmallAut
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.Adapters.LinearCatalogStated
public import CFSG.Quasithin.Background.FLcModel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small

open CFSG.Open CFSG.AGLEmbedding CFSG.HardMathSupport.Curtis.Proving CFSG.Quasithin.FLc
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

theorem small_data
    {X : Type} [Group X] (h : IsSmallTwoOrG2 X) :
    (∃ j : ℕ, Nat.card (MulAut X) = 2 ^ j * Nat.card X) ∧
      (OvergroupOrder96 X ∨ Nonempty (X ≃* SLt 4)) := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | hd
  · have hcardAut := Nat.card_congr (MulAut.congr e).toEquiv
    rcases hn with rfl | rfl | rfl
    · have hX : Nat.card X = Nat.factorial 5 / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have h1 : Nat.card (MulAut X) = Nat.factorial 5 :=
        hcardAut.trans (ParabComm.card_mulAut_alternatingGroup (Or.inl rfl))
      have h2 : Nat.factorial 5 = 2 ^ 1 * (Nat.factorial 5 / 2) := by decide
      exact ⟨⟨1, h1.trans (h2.trans (by rw [hX]))⟩,
        Or.inl (ordBound_isSmallFourTwo (Or.inl ⟨5, Or.inl rfl, ⟨e⟩⟩))⟩
    · have hX : Nat.card X = Nat.factorial 6 / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      refine ⟨?_, Or.inl (ordBound_isSmallFourTwo (Or.inl ⟨6, Or.inr rfl, ⟨e⟩⟩))⟩
      have h2 : Nat.factorial 6 / 2 = 360 := by decide
      rcases CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.card_mulAut_six with h | h
      · exact ⟨1, by rw [hcardAut, h, hX, h2]; norm_num⟩
      · exact ⟨2, by rw [hcardAut, h, hX, h2]; norm_num⟩
    · have hX : Nat.card X = Nat.factorial 8 / 2 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      have h1 : Nat.card (MulAut X) = Nat.factorial 8 :=
        hcardAut.trans (ParabComm.card_mulAut_alternatingGroup (Or.inr (by norm_num)))
      have h2 : Nat.factorial 8 = 2 ^ 1 * (Nat.factorial 8 / 2) := by decide
      exact ⟨⟨1, h1.trans (h2.trans (by rw [hX]))⟩,
        Or.inr ⟨e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
          (slEquivGLt 4).symm)⟩⟩
  · have h4 : IsSmallFourTwo X := Or.inr hd
    refine ⟨?_, Or.inl (ordBound_isSmallFourTwo h4)⟩
    obtain ⟨d, ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩, ⟨e⟩⟩ := hd
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
      have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      rw [hpq, hf] at hM
      obtain ⟨e₇⟩ := CFSG.GH74.KGroups.L27.equiv_of_lieModel (Or.inl ⟨by decide, hM⟩)
      have h1 : Nat.card (MulAut X) = 336 := CFSG.GH74.KGroups.L27.card_mulAut e₇
      have h2 : Nat.card X = 168 := by
        rw [Nat.card_congr e₇.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.L27.QP_ok,
          CFSG.GH74.KGroups.L27.QP_valid.2]
      exact ⟨1, by simp [h1, h2]⟩
    ·
      obtain ⟨dd, hv⟩ := d
      simp only at hd'
      subst hd'
      obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
      have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hpq, hf] at hM
      obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, hM⟩)
      have h1 : Nat.card (MulAut X) = 12096 := CFSG.GH74.KGroups.U33.card_mulAut eU
      have h2 : Nat.card X = 6048 := by
        rw [Nat.card_congr eU.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
          CFSG.GH74.KGroups.U33.QP_valid.2]
      exact ⟨1, by simp [h1, h2]⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small

module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48TwoBig
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Three

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ABGLocalTools

theorem stmtSp48MSide₂_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut)
    (hNine : KFactBlockThreeOrderNine) : StmtSp48MSide₂ := by
  intro G _ _ P M H R X U A h hO
  have h3 := h.surv.ph3
  obtain ⟨L, hL⟩ := h3.exists_weakSBlock h84 hD2
  have c : Sp48Ctx P M H R X U A L :=
    ⟨h, h84, h85, h86, h93, hD2, hB3, hb, hOut, hNine, hO, hL⟩
  obtain ⟨SL⟩ : Nonempty (Sylow 3 (blockParabolic M (pCoreOf 2 H) L)) := inferInstance
  by_cases horb : ∀ k ∈ H ⊓ M, barM M (L.map (MulAut.conj k).toMonoidHom) = barM M L
  · exact h.false_of_orbit_one h84 h85 h86 h93 hD2 hB3 hb hOut hNine hO hL horb
  push Not at horb
  obtain ⟨k₁, hk₁, hne⟩ := horb
  have hne' : blkOf M L k₁ ≠ barM M L := hne
  have h01 : blkOf M L 1 ≠ blkOf M L k₁ := by
    rw [blkOf_one]
    exact Ne.symm hne'
  rcases c.sylow_card SL with hs | hs
  · by_cases h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁
    · exact c.false_of_two_small SL hs hk₁ (Ne.symm hne') h2
    push Not at h2
    obtain ⟨k₂, hk₂, h20, h21⟩ := h2
    have h02 : blkOf M L 1 ≠ blkOf M L k₂ := by
      rw [blkOf_one]
      exact Ne.symm h20
    by_cases h3' : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁ ∨
        blkOf M L k = blkOf M L k₂
    · exact c.false_of_three_small SL hs hk₁ hk₂ h01 h02 (Ne.symm h21) h3'
    push Not at h3'
    obtain ⟨k₃, hk₃, h30, h31, h32⟩ := h3'
    have h03 : blkOf M L 1 ≠ blkOf M L k₃ := by
      rw [blkOf_one]
      exact Ne.symm h30
    exact c.false_of_four SL hs hk₁ hk₂ hk₃ h01 h02 h03 (Ne.symm h21) (Ne.symm h31)
      (Ne.symm h32)
  · by_cases h2 : ∀ k ∈ H ⊓ M, blkOf M L k = barM M L ∨ blkOf M L k = blkOf M L k₁
    · exact c.false_of_two_big SL hs hk₁ h01 h2
    push Not at h2
    obtain ⟨k₂, hk₂, h20, h21⟩ := h2
    have h02 : blkOf M L 1 ≠ blkOf M L k₂ := by
      rw [blkOf_one]
      exact Ne.symm h20
    exact c.false_of_three_big SL hs hk₁ hk₂ h01 h02 (Ne.symm h21)

end CFSG.AGLEmbedding

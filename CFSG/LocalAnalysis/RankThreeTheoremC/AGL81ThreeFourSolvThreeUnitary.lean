module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactNineFourSylowIrredProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding

@[expose] def ThreeFourSolvThreeUThreeThree : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 3 → q.exponent = 1 →
    d.1 = .twistedA 2 q → ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

theorem ThreeFourSolvThreeNoneAt.of_forall_lt_pRank {X : Type*} [Group X]
    (hX : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* X) →
      3 < CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    ThreeFourSolvThreeNoneAt X := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ _ hKX _ hrk
  exfalso
  have h1 := hX ↥K hKX
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ CFSG.pRank 3 ↥(⊤ : Subgroup Y) := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_coe_eq_openPRank,
      CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact CFSG.SectionRank.pRank_mono (by norm_num) le_top
  omega

theorem threeFourSolvThreeUnitary_of (h33 : ThreeFourSolvThreeUThreeThree) :
    ThreeFourSolvThreeUnitary := by
  intro q d hq3 hd
  rcases Nat.lt_or_ge q.exponent 2 with h2 | h2
  · have h1 : q.exponent = 1 := by
      have := q.exponent_pos
      omega
    exact h33 q d hq3 h1 hd
  · refine ThreeFourSolvThreeNoneAt.of_forall_lt_pRank fun K _ _ hK => ?_
    obtain ⟨e⟩ := hK
    have := CFSG.LocalAnalysis.RankThreeTheoremC.NineFourIrred.four_le_pRank_unitary
      (by decide : (3 : ℕ) ≠ 2) hq3 h2 hd e
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

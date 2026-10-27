module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTwD4

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti CFSG.TauCetiBridge
  CFSG.TauCetiBridge.Even

set_option linter.unusedSectionVars false



theorem two_le_pRank_three_exc_trialityD4 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have hm : 0 < TwistTag.D4.order := by decide
  have hF := card_fieldOf q hm
  obtain ⟨φ⟩ := chevalleyBridgesAll.trialityD4 q hv (fieldOf q TwistTag.D4.order) hF
    (frobOf q TwistTag.D4.order) (frobOf_apply q TwistTag.D4.order)
  have hk : Nat.card (fieldOf q TwistTag.D4.order) = q.card ^ 3 := hF
  have hq2 : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    calc 2 ≤ q.p := q.prime_p.two_le
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right q.prime_p.pos q.exponent_pos
  have := two_le_pRank_three_twistedD4 hq2 hk (frobOf_apply q TwistTag.D4.order)
    (e.trans φ.symm)
  omega


end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

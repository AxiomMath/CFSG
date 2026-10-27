module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTwD4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankReeF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankExc

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti CFSG.TauCetiBridge
  CFSG.TauCetiBridge.Even

set_option linter.unusedSectionVars false


theorem pRank_three_ne_one_trialityD4 {S : Type} [Group S] [Finite S] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
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

theorem pRank_three_ne_one_of_exceptional {S : Type} [Group S] [Finite S]
    (d : ValidLieTypeIndex)
    (hd : (∃ q, d.1 = .G2 q) ∨ (∃ q, d.1 = .F4 q) ∨ (∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .E7 q) ∨
      (∃ q, d.1 = .E8 q) ∨ (∃ q, d.1 = .twistedE6 q) ∨ (∃ q, d.1 = .trialityD4 q) ∨
      (∃ m, d.1 = .reeG2 m) ∨ (∃ m, d.1 = .suzuki m) ∨ (∃ m, d.1 = .reeF4 m) ∨ d.1 = .tits)
    (e : Nonempty (S ≃* (CFSGIndex.lie d).Group)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≠ 1 := by
  obtain ⟨e⟩ := e
  obtain ⟨i, hv⟩ := d
  rcases hd with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ |
    ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · exact pRank_three_ne_one_g2 q hv e
  · exact pRank_three_ne_one_f4 q hv e
  · exact pRank_three_ne_one_e6 q hv e
  · exact pRank_three_ne_one_e7 q hv e
  · exact pRank_three_ne_one_e8 q hv e
  · exact pRank_three_ne_one_twistedE6 q hv e
  · exact pRank_three_ne_one_trialityD4 q hv e
  · exact pRank_three_ne_one_reeG2 m hv e
  · exact pRank_three_ne_one_suzuki m hv e
  · exact pRank_three_ne_one_reeF4 m hv e
  · exact pRank_three_ne_one_tits hv e

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

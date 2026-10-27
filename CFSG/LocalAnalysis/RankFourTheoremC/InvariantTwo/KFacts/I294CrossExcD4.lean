module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section D4


theorem crossSylowAbelianAt_trialityD4 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    CrossSylowAbelianAt ⟨.trialityD4 q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdp' : q.p ≠ p := by simpa using hdp
  have hm : 0 < TwistTag.D4.order := by decide
  have hK : Nat.card (GaloisField q.p (q.exponent * TwistTag.D4.order)) =
      q.card ^ TwistTag.D4.order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'),
      TauCeti.PrimePower.card_def, pow_mul]
  let σ := iterateFrobenius (GaloisField q.p (q.exponent * TwistTag.D4.order)) q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  have hb : Nonempty (DerivedCentralQuotient (twistedFixedGroup .D4
      (GaloisField q.p (q.exponent * TwistTag.D4.order)) σ) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq _ hK σ hσ
    · exact CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hq _ hK σ hσ
  obtain ⟨φ⟩ := hb
  have hpK : ¬ p ∣ Nat.card (GaloisField q.p (q.exponent * TwistTag.D4.order)) := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv (e.trans φ.symm)
    (fun R => isMulCommutative_sylow_derivedCentralQuotient inf_le_left hp
      (CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 hp (by omega)) hpK R) P

end D4

end CFSG.LocalAnalysis.RankFourTheoremC

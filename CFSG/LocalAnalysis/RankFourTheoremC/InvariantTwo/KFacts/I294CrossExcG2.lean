module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2


theorem crossExc_not_dvd_card_weylGroup_G2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (WeylGroup Tag.G2) := by
  rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2,
    show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 from rfl]
  exact crossExc_not_dvd_two_pow_mul_three_pow hp hp5 2 1

theorem crossSylowAbelianAt_G2 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) : CrossSylowAbelianAt ⟨.G2 q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hdp' : q.p ≠ p := by simpa using hdp
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hb : Nonempty (AdjointQuotient .G2 (GaloisField q.p q.exponent) ≃*
      TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq _ hK
    · exact CFSG.TauCetiBridge.untwistedBridge_G2 q hv hq _ hK
  obtain ⟨φ⟩ := hb
  have hpK : ¬ p ∣ Nat.card (GaloisField q.p q.exponent) := by
    rw [hK, TauCeti.PrimePower.card_def]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv (e.trans φ.symm)
    (isMulCommutative_sylow_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      (fun S => isMulCommutative_sylow_adjointGroup hp
        (crossExc_not_dvd_card_weylGroup_G2 hp hp5) hpK S)) P

theorem crossSylowAbelianAt_reeG2 {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) :
    CrossSylowAbelianAt ⟨.reeG2 m, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : 3 ≠ p := by simpa using hdp
  obtain ⟨-, a, -, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp Nat.prime_three hdp'
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => isMulCommutative_sylow_derivedCentralQuotient inf_le_left hp
      (crossExc_not_dvd_card_weylGroup_G2 hp hp5) hpK R) P

end G2

end CFSG.LocalAnalysis.RankFourTheoremC

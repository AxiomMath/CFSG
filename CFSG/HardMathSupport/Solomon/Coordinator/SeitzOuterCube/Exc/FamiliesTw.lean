module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FamiliesUntw
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

section TwistedPairs


theorem excOuterPair_twE6 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.twistedE6 q).Valid) (p : ℕ) [Fact p.Prime] :
    ExcOuterPair ⟨.twistedE6 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _
    q.prime_p.ne_zero))
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) :=
    have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_twistedE6 q).symm)
  by_cases hp3 : p = 3
  · subst hp3
    exact (not_rankLE2_cat_twistedE6_three q hv hpq hrk).elim
  · have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
    have hK' : Nat.card K = q.card ^ 2 := by rw [hK, PrimePower.card_def]
    have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
    exact ⟨(fieldAutData_twE6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAllTwE6
        q.prime_p q.exponent_pos hK σ hσ hp hp5 hpq).of_mulEquiv e hp,
      (fixPlaneGen_twE6 hLow hK' σ hσ' hp (by omega) hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv
        e hp⟩

theorem fieldAutData_cat_trialityD4 {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    FieldAutData (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) p := by
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  by_cases h2 : q.p = 2
  · have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, h2]
    have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, h2]
    exact (SEITZ2.fieldAutData_trialityD4
      (CFSG.RankThree.PartOne.SEITZ8.subfieldPairD4_of_two
        CFSG.RankThree.PartOne.SEITZ8.subfieldPairD4Two_holds) hp hp5 q.exponent_pos hK'
      hσ').of_mulEquiv e hp
  · exact (CFSG.HardMathSupport.Seitz.TrialityOdd.fieldAutData_trialityD4_odd
      CFSG.HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof q.prime_p h2 hp hp5
      q.exponent_pos hK hσ).of_mulEquiv e hp

theorem excOuterPair_trialityD4_five (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) :
    ExcOuterPair ⟨.trialityD4 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) :=
    have : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_trialityD4 q).symm)
  have hK' : Nat.card K = q.card ^ 3 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, PrimePower.card_def]
  exact ⟨fieldAutData_cat_trialityD4 hv hp hp5,
    (fixPlaneGen_trialityD4 hLow hK' σ hσ' hp hp5 hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv
      e hp⟩

end TwistedPairs

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

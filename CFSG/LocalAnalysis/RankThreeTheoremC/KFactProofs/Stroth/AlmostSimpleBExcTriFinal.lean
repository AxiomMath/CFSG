module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.Quasithin.F134.LieD4 CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KFU
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

@[expose] def LieFamilyTrialityD4Three : TauCeti.LieTypeIndex → ℕ → Prop
  | .trialityD4 _, p => p = 3
  | _, _ => False

@[expose] def ChevTwoPClosureOddTrialityD4Three : Prop :=
  ChevTwoPClosureOddFamily LieFamilyTrialityD4Three

section Final


theorem chevTwoPClosureOddTrialityD4Split_of_three (hThree : ChevTwoPClosureOddTrialityD4Three) :
    ChevTwoPClosureOddTrialityD4Split := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | trialityD4 q =>
    have hq2 : q.p = 2 := hdi
    by_cases hp3 : p = 3
    · exact hThree p hp hp2 L hs hnab hrk hSE ⟨.trialityD4 q, hv⟩ hp3 hdi ⟨e⟩
    · have hord : orderOf ((q.card : ℕ) : ZMod p) = 1 := by
        rcases hF with h | h
        · exact absurd h hp3
        · exact h
      have hp5 := five_le_of_prime_ne hp hp2 hp3
      have hn := q.exponent_pos
      have hqcard : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq2]
      have hCEM0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).trialityD4 q hv hq2
      have hCEM : ChevalleyExceptionalModel L .trialityD4 2 q.exponent :=
        CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr e.symm hCEM0
      obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨eL⟩⟩ :=
        exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hCEM.2
      have hK : Nat.card K = (2 ^ q.exponent) ^ 3 := hKcard
      have hpq : p ∣ 2 ^ q.exponent - 1 := by
        rw [hqcard] at hord
        have h1 : 1 ≤ 2 ^ q.exponent := Nat.one_le_two_pow
        have := (dvd_pow_sub_one_iff_orderOf (e := 1) h1 hord).2 dvd_rfl
        simpa using this
      refine PClosureOdd.of_mulEquiv eL.symm ?_
      intro d hd1 hdp
      exact oddPCoreInClosure_triality_split hn hK σ hσ hp (by omega) hpq
        (orderOf_eq_prime hdp hd1)
  | A _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | B _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | C _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | D _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | E6 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | E7 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | E8 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | F4 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | G2 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | suzuki _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyTrialityD4Split])
  | tits => exact absurd hF (by simp [LieFamilyTrialityD4Split])

theorem chevTwoPClosureOddTrialityD4_of_three (hThree : ChevTwoPClosureOddTrialityD4Three) :
    ChevTwoPClosureOddTrialityD4 :=
  chevTwoPClosureOddTrialityD4_of_split (chevTwoPClosureOddTrialityD4Split_of_three hThree)

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

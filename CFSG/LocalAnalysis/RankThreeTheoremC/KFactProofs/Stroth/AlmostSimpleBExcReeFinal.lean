module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcReeSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.LargeReeOrder CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)


@[expose] def LieFamilyReeF4Three : TauCeti.LieTypeIndex → ℕ → Prop
  | .reeF4 _, p => p = 3
  | _, _ => False

@[expose] def ChevTwoPClosureOddReeF4Three : Prop :=
  ChevTwoPClosureOddFamily LieFamilyReeF4Three

section Final


theorem chevTwoPClosureOddReeF4Split_of_three (hThree : ChevTwoPClosureOddReeF4Three) :
    ChevTwoPClosureOddReeF4Split := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | reeF4 m =>
    by_cases hp3 : p = 3
    · exact hThree p hp hp2 L hs hnab hrk hSE ⟨.reeF4 m, hv⟩ hp3 hdi ⟨e⟩
    · have hord : orderOf (((2 ^ (2 * m + 1) : ℕ)) : ZMod p) = 1 := by
        rcases hF with h | h
        · exact absurd h hp3
        · exact h
      have hp5 := five_le_of_prime_ne hp hp2 hp3
      have hR0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).reeF4 m hv
      have hR : ReeTitsModel L .twistedF4 2 (2 * m + 1) :=
        CFSG.SectionRank.reeTitsModel_of_mulEquiv e hR0
      obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨eK⟩⟩ := reeF4_model_data hR
      have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hfa]
      have ham : a = m := by omega
      subst ham
      have hpq : p ∣ 2 ^ (2 * a + 1) - 1 := by
        have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
        have := (dvd_pow_sub_one_iff_orderOf (e := 1) h1 hord).2 dvd_rfl
        simpa using this
      refine PClosureOdd.of_mulEquiv eK.symm ?_
      intro d hd1 hdp
      exact oddPCoreInClosure_ree_split ha hK hp (by omega) hpq d (orderOf_eq_prime hdp hd1)
  | A _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | B _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | C _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | D _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | E6 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | E7 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | E8 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | F4 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | G2 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | suzuki _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyReeF4Split])
  | tits => exact absurd hF (by simp [LieFamilyReeF4Split])

theorem chevTwoPClosureOddReeF4_of_three (hThree : ChevTwoPClosureOddReeF4Three) :
    ChevTwoPClosureOddReeF4 :=
  chevTwoPClosureOddReeF4_of_split (chevTwoPClosureOddReeF4Split_of_three hThree)

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

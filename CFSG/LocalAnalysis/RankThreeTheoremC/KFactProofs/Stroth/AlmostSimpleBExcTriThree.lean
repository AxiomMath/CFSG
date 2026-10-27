module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriEven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.Timmesfeld.ExceptionalOrders
  CFSG.Quasithin.F134.LieD4 CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KFU
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

section Final


theorem oddPCoreInClosure_triality_three_even {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hfeven : Even f) (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hx : orderOf x = 3) :
    OddPCoreInClosure 3
      ↥(Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :=
  oddPCoreInClosure_triality_three_even_aux hf hfeven hK σ hσ hx _ fun _ =>
    Subgroup.mem_centralizer_singleton_iff

theorem chevTwoPClosureOddTrialityD4Three_holds : ChevTwoPClosureOddTrialityD4Three := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | trialityD4 q =>
    have hp3 : p = 3 := hF
    subst hp3
    have hq2 : q.p = 2 := hdi
    have hn := q.exponent_pos
    have hCEM0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).trialityD4 q hv hq2
    have hCEM : ChevalleyExceptionalModel L .trialityD4 2 q.exponent :=
      CFSG.RankThree.PartOne.chevalleyExceptionalModel_congr e.symm hCEM0
    obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨eL⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn hCEM.2
    have hK : Nat.card K = (2 ^ q.exponent) ^ 3 := hKcard
    haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two
      (k := q.exponent * 3) (by omega) (by rw [hK, pow_mul])
    refine PClosureOdd.of_mulEquiv eL.symm ?_
    intro d hd1 hdp
    have hx : orderOf d = 3 := orderOf_eq_prime hdp hd1
    rcases Nat.even_or_odd q.exponent with hev | hodd
    · exact oddPCoreInClosure_triality_three_even hn hev hK σ hσ hx
    · exact oddPCoreInClosure_triality_three_odd σ hn hodd hK hσ hx
  | A _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | B _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | C _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | D _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | E6 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | E7 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | E8 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | F4 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | G2 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | suzuki _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyTrialityD4Three])
  | tits => exact absurd hF (by simp [LieFamilyTrialityD4Three])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

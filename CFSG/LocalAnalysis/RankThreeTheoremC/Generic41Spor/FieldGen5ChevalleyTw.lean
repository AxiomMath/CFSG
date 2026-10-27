module

public import CFSG.LieType.SeitzGeneration.ExcSeitzWide

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration TauCeti

section ChevalleyTwisted


theorem fieldAutData_five_chevalley_twisted {L : Type} [Group L] [Finite L]
    {t : CFSG.Open.StatedLieTag} {ℓ f : ℕ}
    (ht : t = .twistedE6 ∨ t = .trialityD4)
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel L t ℓ f) (hℓ : ℓ ≠ 5) :
    CFSG.RankThree.PartOne.CTP.FieldAutData L 5 := by
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hM
  let q : PrimePower := ⟨ℓ, f, hp, hf⟩
  have hq : q.card = ℓ ^ f := PrimePower.card_def q
  rcases ht with rfl | rfl
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := LieTypeIndex.valid_twistedE6 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    obtain ⟨K', _, σ', hK', hσ', ⟨e'⟩⟩ := exists_catEquiv_twistedE6 q hv
    have : Finite K' := Nat.finite_of_card_ne_zero (by
      rw [hK']
      exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
    exact (fieldAutData_twE6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAllTwE6
      q.prime_p q.exponent_pos hK' σ' hσ' Nat.prime_five le_rfl hℓ.symm).of_mulEquiv
      ((e.trans b).trans e') Nat.prime_five
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := LieTypeIndex.valid_trialityD4 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
      (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    obtain ⟨K', _, _, σ', hK', hσ', -, ⟨e'⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    refine FieldAutData.of_mulEquiv ((e.trans b).trans e') Nat.prime_five ?_
    by_cases h2 : q.p = 2
    · have hK2 : Nat.card K' = (2 ^ q.exponent) ^ 3 := by rw [hK', h2]
      have hσ2 : ∀ c, σ' c = c ^ 2 ^ q.exponent := fun c => by rw [hσ' c, h2]
      exact SEITZ2.fieldAutData_trialityD4
        (SEITZ8.subfieldPairD4_of_two SEITZ8.subfieldPairD4Two_holds) Nat.prime_five le_rfl
        q.exponent_pos hK2 hσ2
    · exact CFSG.HardMathSupport.Seitz.TrialityOdd.fieldAutData_trialityD4_odd
        CFSG.HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof q.prime_p h2
        Nat.prime_five le_rfl q.exponent_pos hK' hσ'

end ChevalleyTwisted

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

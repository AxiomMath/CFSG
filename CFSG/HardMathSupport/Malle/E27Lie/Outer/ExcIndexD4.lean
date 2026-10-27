module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityOddFinal
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Fixed27

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section


@[expose] def TrialityThreeLower : Prop :=
  ∀ {f : ℕ}, 1 ≤ f → ∀ (K : Type) [Group K] [Finite K],
    CFSG.Blueprint.TwistedChevalleyModel K .D4 (3 ^ f) → ∀ α : MulAut K, α ^ 3 = 1 →
      α ∉ inner K → 27 ∣ Nat.card (fixedSubgroup α)

theorem twistedModel_of_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    {K : Type} [Group K] (e : K ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    CFSG.Blueprint.TwistedChevalleyModel K .D4 (q.p ^ q.exponent) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p (q.exponent * 3)) = q.card ^ 3 := by
    rw [GaloisField.card q.p (q.exponent * 3) (by have := q.exponent_pos; omega),
      TauCeti.PrimePower.card_def, pow_mul]
  have hσ : ∀ c : GaloisField q.p (q.exponent * 3),
      iterateFrobenius (GaloisField q.p (q.exponent * 3)) q.p q.exponent c = c ^ q.card :=
    fun c => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).trialityD4 q hv
    (GaloisField q.p (q.exponent * 3)) hcard
    (iterateFrobenius (GaloisField q.p (q.exponent * 3)) q.p q.exponent) hσ
  refine ⟨GaloisField q.p (q.exponent * 3), inferInstance, inferInstance, ?_,
    iterateFrobenius (GaloisField q.p (q.exponent * 3)) q.p q.exponent, ?_, ⟨e.trans br.symm⟩⟩
  · rw [hcard, TauCeti.PrimePower.card_def]; rfl
  · intro c; rw [hσ, TauCeti.PrimePower.card_def]

theorem e27LieOuterAutAt_trialityD4
    (h2 : CFSG.HardMathSupport.Lang.E27Lie.MinusToralLower) (h3 : TrialityThreeLower) :
    E27LieOuterAutAt (fun i => ∃ q, i = .trialityD4 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := twistedModel_of_trialityD4 q hv e
  have hpr := q.prime_p
  have hf := q.exponent_pos
  refine false_of_dvd_twentySeven u hQ ?_
  by_cases hp2 : q.p = 2
  · have hm' : CFSG.Blueprint.TwistedChevalleyModel K .D4 (2 ^ q.exponent) := hp2 ▸ hm
    exact CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_fixedSubgroup_trialityD4_two_model hf K
      hm' u hu3 fun ⟨k, hk⟩ => hout k hk.symm
  by_cases hp3 : q.p = 3
  · have hm' : CFSG.Blueprint.TwistedChevalleyModel K .D4 (3 ^ q.exponent) := hp3 ▸ hm
    exact h3 hf K hm' u hu3 fun ⟨k, hk⟩ => hout k hk.symm
  have hp5 : 5 ≤ q.p := by
    have := hpr.two_le
    have : q.p ≠ 4 := fun h4 => by rw [h4] at hpr; exact absurd hpr (by norm_num)
    omega
  by_cases hq : (q.p ^ q.exponent) % 3 = 1
  · exact CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_fixedSubgroup_trialityD4_q1_model hpr
      hp5 hf hq K hm u hu3 fun ⟨k, hk⟩ => hout k hk.symm
  · exact CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_fixedSubgroup_trialityD4_q2_model h2
      hpr hp5 hf K hm u hu3 fun ⟨k, hk⟩ => hout k hk.symm

end

end CFSG.HardMathSupport.Malle.E27Lie

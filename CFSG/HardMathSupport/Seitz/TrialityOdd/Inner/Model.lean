module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Model


theorem exists_trialityD4_model_of_isoLie {q : TauCeti.PrimePower} {K : Type} [Group K]
    (hiso : IsoLie K (.trialityD4 q)) :
    ∃ (X : Type) (_ : Field X) (_ : Finite X) (σ : X ≃+* X), Nat.card X = q.card ^ 3 ∧
      (∀ c, σ c = c ^ q.card) ∧ σ ^ TwistTag.D4.order = 1 ∧
      Nonempty (K ≃* graphFixedRootGroup TwistTag.D4 X σ.toRingHom) := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [← hqc] at hX hσ
  refine ⟨X, inferInstance, inferInstance, σ, hX, hσ, ?_, ⟨e0.trans e⟩⟩
  have : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X = q.card ^ 3 := by rw [← Nat.card_eq_fintype_card, hX]
  ext c
  change σ (σ (σ c)) = c
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show q.card * (q.card * q.card) = q.card ^ 3 by ring,
    ← hcard, FiniteField.pow_card]

end Model

theorem charP_of_trialityD4_model {q : TauCeti.PrimePower} (X : Type) [Field X]
    (hX : Nat.card X = q.card ^ 3) : CharP X q.p := by
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
    (k := q.exponent * 3) (Nat.mul_pos q.exponent_pos (by norm_num))
    (by rw [hX, hqc, ← pow_mul])

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

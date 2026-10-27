module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsOrthSpin
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts QuadraticMap
  CFSG.ClassicalGroups.Orthogonal

section Spin

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem false_of_isClassicalMember3_of_spin [Finite (spinGroup Q)] {X : Type} [Group X] [Finite X]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) (ψ : spinGroup Q →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q))
    {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) : False :=
  false_of_isClassicalMember3_of_orthogonal hodd h5 hQ (spinAction Q)
    (hrange.le.trans (elementaryGroup_le_orthogonalGroup Q)) hrange.ge (ker_spinAction_le_center Q)
    ψ hψ hker h

end Spin

section Tags

private theorem odd_card_galoisField_of_ne_two {r e : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (he : 1 ≤ e) : Odd (Nat.card (GaloisField r e)) := by
  rw [GaloisField.card r e (by omega)]
  exact (Fact.out (p := r.Prime)).odd_of_ne_two hr2 |>.pow

theorem classicalMemberParameters3At_POmegaOdd : ClassicalMemberParameters3At .POmegaOdd := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have hodd : Odd (Nat.card (GaloisField r e)) := odd_card_galoisField_of_ne_two hr2 he
  have h5' : 5 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    exact h5
  have h2 : (2 : GaloisField r e) ≠ 0 := two_ne_zero_galoisField e hr2
  have hfin : Finite (Generic.modelUniv .POmegaOdd n r e hr).K :=
    finite_modelUniv hr2 hr trivial hadm
  have hM : Generic.modelUniv .POmegaOdd n r e hr =
      ⟨spinGroup (quadOdd n (GaloisField r e)), oddDatum n (GaloisField r e)⟩ := rfl
  suffices hmain : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadOdd n (GaloisField r e)), oddDatum n (GaloisField r e)⟩ →
      ∀ ψ : M.K →* X, Function.Surjective ψ → ψ.ker ≤ Subgroup.center M.K → Finite M.K → False
    from hmain _ hM ψ hψ hker hfin
  intro M hM' ψ hψ hker hfin
  subst hM'
  exact false_of_isClassicalMember3_of_spin hodd h5' (nondegenerate_polarBilin_quadOdd _ _ h2)
    (range_spinAction_quadOdd h2 hn3) ψ hψ hker h

theorem classicalMemberParameters3At_POmegaPlus : ClassicalMemberParameters3At .POmegaPlus := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have hodd : Odd (Nat.card (GaloisField r e)) := odd_card_galoisField_of_ne_two hr2 he
  have h5' : 5 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    exact h5
  have hfin : Finite (Generic.modelUniv .POmegaPlus n r e hr).K :=
    finite_modelUniv hr2 hr trivial hadm
  have hM : Generic.modelUniv .POmegaPlus n r e hr =
      ⟨spinGroup (quadPlus n (GaloisField r e)), plusDatum n (GaloisField r e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus n r e hr =
        ModelFacts.modelUniv .POmegaPlus n r e hr).trans
      (modelUniv_POmegaPlus (n := n) (p := r) (f := e) hn3)
  suffices hmain : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus n (GaloisField r e)), plusDatum n (GaloisField r e) hn3⟩ →
      ∀ ψ : M.K →* X, Function.Surjective ψ → ψ.ker ≤ Subgroup.center M.K → Finite M.K → False
    from hmain _ hM ψ hψ hker hfin
  intro M hM' ψ hψ hker hfin
  subst hM'
  exact false_of_isClassicalMember3_of_spin hodd h5' (nondegenerate_polarBilin_quadPlus _ _)
    (range_spinAction_quadPlus hn3) ψ hψ hker h

theorem classicalMemberParameters3At_POmegaMinus : ClassicalMemberParameters3At .POmegaMinus := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  have he : 1 ≤ e := hadm.2.1
  have hn4 : 4 ≤ n := hadm.2.2
  have h5 : 5 ≤ r ^ e := five_le_pow_of_odd_prime_of_ne_three hr hr2 he hne
  have hodd : Odd (Nat.card (GaloisField r e)) := odd_card_galoisField_of_ne_two hr2 he
  have h5' : 5 ≤ Nat.card (GaloisField r e) := by
    rw [GaloisField.card r e (by omega)]
    exact h5
  have hfin : Finite (Generic.modelUniv .POmegaMinus n r e hr).K :=
    finite_modelUniv hr2 hr trivial hadm
  have hM : Generic.modelUniv .POmegaMinus n r e hr =
      ⟨spinGroup (quadMinus n (GaloisField r e) (minusCoeffs r e).1 (minusCoeffs r e).2),
        Twisted.minusDatum n (minusCoeffs_irr r e)⟩ := rfl
  suffices hmain : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadMinus n (GaloisField r e) (minusCoeffs r e).1 (minusCoeffs r e).2),
        Twisted.minusDatum n (minusCoeffs_irr r e)⟩ →
      ∀ ψ : M.K →* X, Function.Surjective ψ → ψ.ker ≤ Subgroup.center M.K → Finite M.K → False
    from hmain _ hM ψ hψ hker hfin
  intro M hM' ψ hψ hker hfin
  subst hM'
  exact false_of_isClassicalMember3_of_spin hodd h5'
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr r e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr r e)) ψ hψ hker h

end Tags

end CFSG.ClassicalInvolution.Q3

module

public import CFSG.ClassicalInvolution.Q3.Q3YSTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem neg_one_ne_one_gf3 : (-1 : GaloisField 3 1) ≠ 1 := by
  intro h
  apply Q3W.two_ne_zero_gf3
  linear_combination -h


@[expose] def ModelFourGroup3On (S : StatedLieTag → Prop) : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), S t → IsFundTag t → StatedLieAdmissible t n 3 1 →
    ¬ (t = .PSp ∧ n = 2) → Even (Nat.card (modelUniv t n 3 1 Nat.prime_three).K) →
    ∃ F : Subgroup (modelUniv t n 3 1 Nat.prime_three).K, IsElemAbelian 2 F ∧ Nat.card F = 4 ∧
      F ⊓ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K = ⊥

@[expose] def Sp4KleinQuat3 : Prop :=
  ∃ y y' : (modelUniv .PSp 2 3 1 Nat.prime_three).K, KleinQuat _ y y'

theorem ModelFourGroup3On.mono {S S' : StatedLieTag → Prop} (h : ModelFourGroup3On S)
    (hle : ∀ t, S' t → S t) : ModelFourGroup3On S' :=
  fun t n ht => h t n (hle t ht)

theorem ModelFourGroup3On.union {S S' : StatedLieTag → Prop} (h : ModelFourGroup3On S)
    (h' : ModelFourGroup3On S') : ModelFourGroup3On fun t => S t ∨ S' t :=
  fun t n ht => ht.elim (h t n) (h' t n)

theorem modelFourGroup3On_of_tags (hPSL : ModelFourGroup3On fun t => t = .PSL)
    (hPSU : ModelFourGroup3On fun t => t = .PSU) (hPSp : ModelFourGroup3On fun t => t = .PSp)
    (hOdd : ModelFourGroup3On fun t => t = .POmegaOdd)
    (hPlus : ModelFourGroup3On fun t => t = .POmegaPlus)
    (hMinus : ModelFourGroup3On fun t => t = .POmegaMinus)
    (hExc : ModelFourGroup3On fun t =>
      t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) :
    ModelFourGroup3On fun _ => True := by
  intro t n _ hfund hadm hne heven
  cases t
  case PSL => exact hPSL _ n rfl hfund hadm hne heven
  case PSU => exact hPSU _ n rfl hfund hadm hne heven
  case PSp => exact hPSp _ n rfl hfund hadm hne heven
  case POmegaOdd => exact hOdd _ n rfl hfund hadm hne heven
  case POmegaPlus => exact hPlus _ n rfl hfund hadm hne heven
  case POmegaMinus => exact hMinus _ n rfl hfund hadm hne heven
  case G2 => exact hExc _ n (Or.inl rfl) hfund hadm hne heven
  case F4 => exact hExc _ n (Or.inr (Or.inl rfl)) hfund hadm hne heven
  case E6 => exact hExc _ n (Or.inr (Or.inr (Or.inl rfl))) hfund hadm hne heven
  case E7 => exact hExc _ n (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hfund hadm hne heven
  case E8 => exact hExc _ n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hfund hadm hne heven
  case twistedE6 =>
    exact hExc _ n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hfund hadm hne heven
  case trialityD4 =>
    exact hExc _ n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hfund hadm hne heven
  all_goals exact absurd hfund (by simp [IsFundTag])

end CFSG.ClassicalInvolution.Q3.Q3YS

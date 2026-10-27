module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

@[expose] def IsTwoPow (q : TauCeti.PrimePower) (k : ℕ) : Prop :=
  q.p = 2 ∧ q.exponent = k

@[expose] def IsL2EightIndex : TauCeti.LieTypeIndex → Prop
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | _ => False

theorem IsL2EightIndex.exists {d : TauCeti.LieTypeIndex} (h : IsL2EightIndex d) :
    ∃ q, d = .A 1 q ∧ IsTwoPow q 3 := by
  cases d with
  | A r q => exact ⟨q, by rw [h.1], h.2⟩
  | _ => simp only [IsL2EightIndex] at h

@[expose] def Bal207Index (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .B r q => p = 3 ∧ ((IsTwoPow q 1 ∧ 3 ≤ r) ∨ (IsTwoPow q 3 ∧ 2 ≤ r))
  | .twistedA r q => p = 3 ∧
      (((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ ¬ 3 ∣ r + 1) ∨ (IsTwoPow q 1 ∧ r = 5))
  | .D r q => p = 3 ∧
      (((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Even r ∧ 6 ≤ r) ∨ (IsTwoPow q 1 ∧ r = 4))
  | .twistedD r q => p = 3 ∧ (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ Odd r ∧ 5 ≤ r
  | .trialityD4 q => p = 3 ∧ IsTwoPow q 1
  | .G2 q => p = 3 ∧ IsTwoPow q 3
  | .F4 q => p = 3 ∧ IsTwoPow q 1
  | .tits => p = 3 ∨ p = 5
  | .suzuki m => p = 5 ∧ m = 2
  | .reeF4 m => p = 5 ∧ m = 2
  | _ => False

@[expose] def Gen2318Index : TauCeti.LieTypeIndex → Prop
  | .A r q => IsTwoPow q 2 ∧ ∃ n, 2 ≤ n ∧ r + 1 = 3 ^ n
  | .twistedA r q => (IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ ∃ n, 3 ≤ n ∧ r + 1 = 3 * n
  | .F4 q => IsTwoPow q 2
  | .E6 q => IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3
  | .E8 q => IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3
  | .E7 q => IsTwoPow q 1 ∨ IsTwoPow q 3
  | _ => False

@[expose] def IsTwistedE6FourIndex : TauCeti.LieTypeIndex → Prop
  | .twistedE6 q => IsTwoPow q 2
  | _ => False

@[expose] def Bal209TwoIndex : TauCeti.LieTypeIndex → Prop
  | .twistedE6 q => IsTwoPow q 1
  | _ => False

@[expose] def IsF4EightIndex : TauCeti.LieTypeIndex → Prop
  | .F4 q => IsTwoPow q 3
  | _ => False

@[expose] def IsD4FourIndex : TauCeti.LieTypeIndex → Prop
  | .D r q => r = 4 ∧ IsTwoPow q 2
  | _ => False

@[expose] def FourIndex : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => IsTwoPow q 3 ∧ (r = 2 ∨ r = 5)
  | .twistedE6 q => IsTwoPow q 3
  | .D r q => r = 4 ∧ IsTwoPow q 3
  | _ => False

@[expose] def IsSixIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsF4EightIndex d ∨ IsD4FourIndex d ∨ FourIndex d

@[expose] def ExcIndex (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  Bal207Index p d ∨
    (p = 3 ∧ (IsL2EightIndex d ∨ Gen2318Index d ∨ Bal209TwoIndex d ∨ IsTwistedE6FourIndex d ∨
      IsSixIndex d))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

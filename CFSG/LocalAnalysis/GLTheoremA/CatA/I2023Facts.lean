module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open

@[expose] def isTD4Any : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 _ => True | _ => False

@[expose] def isTD4Of (q : TauCeti.PrimePower) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 q' => q'.card = q.card | _ => False

@[expose] def innerAutS (S : Type) [Group S] : Subgroup (MulAut S) :=
  (MulAut.conj : S →* MulAut S).range

@[expose] def I2023FactOutCyclic : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S isTD4Any →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E →
      Nat.card E ≤ 3 * Nat.card ↥(E ⊓ innerAutS S)

@[expose] def I2023FactC1 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower), q.p = 2 →
    catalogIs S (isTD4Of q) →
    ∀ φ : MulAut S, φ ^ 3 = 1 → φ ∉ innerAutS S →
      ∃ g : S, (MulAut.conj g * φ) ^ 3 = 1 ∧
        (Nat.card {x : S // (MulAut.conj g * φ) x = x}).factorization 2 = 6 * q.exponent ∧
        ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
          ∀ e ∈ E, (MulAut.conj g * φ) e = e

@[expose] def I2023FactD2LocalOdd : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower), q.p = 2 → Odd q.exponent →
    catalogIs S (isTD4Of q) →
    ∀ (E T : Subgroup (MulAut S)), IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set (MulAut S)) → Nat.card E ≤ 9

@[expose] def I2023FactD4BorelEven : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower), q.p = 2 → Even q.exponent →
    catalogIs S (isTD4Of q) →
    ∀ φ : MulAut S, φ ^ 3 = 1 → φ ∉ innerAutS S →
      (Nat.card {x : S // φ x = x}).factorization 2 = 6 * q.exponent →
      ∀ r : ℕ, r ≤ 2 →
        ∃ E : Subgroup S, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r ∧
          (∀ e ∈ E, φ e = e) ∧
          ∃ U : Subgroup S, IsPGroup 2 U ∧ 8 < Nat.card U ∧
            (∀ u ∈ U, φ u ∈ U) ∧ (∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧
            ∃ u ∈ U, φ u ≠ u

end CFSG.LocalAnalysis.GLTheoremA.I2023

end

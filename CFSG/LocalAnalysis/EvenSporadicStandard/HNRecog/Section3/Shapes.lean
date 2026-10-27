module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

abbrev Z (n : ℕ) : Type := Multiplicative (ZMod n)

abbrev Sym (n : ℕ) : Type := Equiv.Perm (Fin n)

@[expose] def IsShapeZ2TimesSym (n : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z 2 × Sym n)

@[expose] def IsShapeSym (n : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Sym n)

@[expose] def IsShapeD8TimesS3 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* DihedralGroup 4 × Sym 3)

@[expose] def IsShapeZ2WrS3 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z 2 × Sym 4)

@[expose] def IsShapeTwoTwoTimesD8 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × DihedralGroup 4)

@[expose] def IsShapeTwoTwoTimesS4 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × Sym 4)

@[expose] def IsShapeZ2TimesD8 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z 2 × DihedralGroup 4)

@[expose] def IsShapeTwoTwoTimesS3 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × Sym 3)

@[expose] def IsShapeZ2TimesD10 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z 2 × DihedralGroup 5)

@[expose] def IsShapeU35 (X : Type*) [Group X] : Prop :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  Nonempty (X ≃* ↥(CFSG.Open.PSU3 5 1))

@[expose] def IsShapeFiveCubeByTwoTwo (X : Type*) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsPGroup 5 N ∧ Nat.card N = 5 ^ 3 ∧
    Nonempty (X ⧸ N ≃* Elem2 2)

@[expose] def IsShapeZ2TimesA5 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z 2 × alternatingGroup (Fin 5))

@[expose] def IsShapeTwoTwoTimesA5 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 × alternatingGroup (Fin 5))

@[expose] def IsShapeTwoTwoWrTwo (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Elem2 2 ≀ᵣ Z 2)

@[expose] def IsShapeZpTimesA5 (p : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z p × alternatingGroup (Fin 5))

@[expose] def IsShapeZpTimesZp (p : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z p × Z p)

@[expose] def IsShapeZpWrTwo (p : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Z p ≀ᵣ Z 2)

@[expose] def IsShapeA5 (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 5))

@[expose] def IsShapeTwoOneSixByFive (X : Type*) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), Nat.card N = 2 ^ 7 ∧ Nat.card (X ⧸ N) = 5

@[expose] def IsShapeZ2Z4StarExtra (N : Type*) [Group N] : Prop :=
  IsPGroup 2 N ∧ Nat.card N = 2 ^ 7 ∧ Nonempty (Subgroup.center N ≃* Z 2 × Z 4) ∧
    ∃ Q : Subgroup N, IsPlusExtraspecial 2 Q ∧ Subgroup.center N ⊔ Q = ⊤ ∧
      Nat.card (Subgroup.center N ⊓ Q : Subgroup N) = 2

end CFSG.EvenSporadicStandard.HNRecog.Section3

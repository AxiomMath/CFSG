module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def IsFM9 (q : ℕ) : Prop :=
  q = 9 ∨ (q.Prime ∧ ((∃ k : ℕ, q = 2 ^ 2 ^ k + 1) ∨ ∃ n : ℕ, q + 1 = 2 ^ n))

@[expose] def HasSL2Model (K : Type) [Group K] (P : ℕ → Prop) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), P (Nat.card F) ∧ Nonempty (K ≃* StatedSL 2 F)

@[expose] def HasL2Model (K : Type) [Group K] (P : ℕ → Prop) : Prop :=
  ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ P (p ^ f) ∧ LieModel K .PSL 2 p f

@[expose] def IsDoubleCoverOfAlt (K : Type) [Group K] (n : ℕ) : Prop :=
  IsQuasisimple K ∧ Nat.card (center K) = 2 ∧
    Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))

@[expose] def IsL34Quotient (K : Type) [Group K] : Prop :=
  LieModel (K ⧸ center K) .PSL 3 2 2

@[expose] def InChev2 (S : Type) [Group S] : Prop :=
  EvenLieType S ∨ Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ LieModel S .PSU 3 3 1

@[expose] def SimpleInC2 (S : Type) [Group S] : Prop :=
  IsSimpleGroup S ∧
    (InChev2 S ∨ HasL2Model S IsFM9 ∨
      LieModel S .PSL 3 3 1 ∨ LieModel S .PSL 4 3 1 ∨ LieModel S .PSU 4 3 1 ∨
      LieModel S .G2 0 3 1 ∨
      NativeSporadic.IsSporadic S .M11 ∨ NativeSporadic.IsSporadic S .M12 ∨
      NativeSporadic.IsSporadic S .M22 ∨ NativeSporadic.IsSporadic S .M23 ∨
      NativeSporadic.IsSporadic S .M24 ∨ NativeSporadic.IsSporadic S .J2 ∨
      NativeSporadic.IsSporadic S .J3 ∨ NativeSporadic.IsSporadic S .J4 ∨
      NativeSporadic.IsSporadic S .HS ∨ NativeSporadic.IsSporadic S .Suz ∨
      NativeSporadic.IsSporadic S .Ru ∨ NativeSporadic.IsSporadic S .Co1 ∨
      NativeSporadic.IsSporadic S .Co2 ∨ NativeSporadic.IsSporadic S .Fi22 ∨
      NativeSporadic.IsSporadic S .Fi23 ∨ NativeSporadic.IsSporadic S .Fi24Prime ∨
      NativeSporadic.IsSporadic S .Th ∨ NativeSporadic.IsSporadic S .B ∨
      NativeSporadic.IsSporadic S .M)

@[expose] def ExcludedFromC2 (K : Type) [Group K] : Prop :=
  HasSL2Model K IsFM9 ∨ IsDoubleCoverOfAlt K 8 ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧ Nonempty (K ≃* StatedSL 4 F)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 9 ∧
      Nonempty (K ≃* StatedSU 4 3 F)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧ Nonempty (K ≃* StatedSp 2 F)) ∨
    (IsL34Quotient K ∧ Monoid.exponent ↥(center K) = 4)

@[expose] def InC2 (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧ center K = pCore 2 K ∧ SimpleInC2 (K ⧸ center K) ∧ ¬ ExcludedFromC2 K

@[expose] def InT2 (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧
    (HasL2Model K (fun q => Odd q ∧ ¬ IsFM9 q) ∨ HasSL2Model K Odd ∨
      Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      (∃ n : ℕ, 7 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt K n) ∨
      (IsL34Quotient K ∧ Monoid.exponent ↥(center K) = 4))

@[expose] def InB2 (K : Type) [Group K] : Prop :=
  InT2 K ∧ center K ≠ ⊥

@[expose] def InCalK2 (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧ center K = pCore 2 K ∧ IsKGroupNative K

@[expose] def InG2 (K : Type) [Group K] : Prop :=
  InCalK2 K ∧ ¬ InC2 K ∧ ¬ InT2 K

@[expose] def InU2 (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧
    (HasL2Model K Odd ∨ Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      (IsL34Quotient K ∧ IsElementaryAbelian 2 ↥(center K) ∧ Nat.card (center K) ≤ 4))

@[expose] def InTarget2 (K : Type) [Group K] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((5 < p ^ f ∧ LieModel K .PSL 2 p f) ∨ LieModel K .PSL 3 p f ∨ LieModel K .PSU 3 p f ∨
      (3 < p ^ f ∧ LieModel K .PSp 2 p f) ∨
      (3 < p ^ f ∧ p ^ f % 8 ≠ 1 ∧ LieModel K .PSL 4 p f) ∨
      (3 < p ^ f ∧ p ^ f % 8 ≠ 7 ∧ LieModel K .PSU 4 p f) ∨
      (3 < p ^ f ∧ LieModel K .G2 0 p f) ∨ LieModel K .trialityD4 0 p f)) ∨
    (∃ f : ℕ, LieModel K .twistedG2 0 3 f) ∨
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
    NativeSporadic.IsSporadic K .M11 ∨ NativeSporadic.IsSporadic K .M12 ∨
    NativeSporadic.IsSporadic K .McL ∨ NativeSporadic.IsSporadic K .Ly ∨
    NativeSporadic.IsSporadic K .ONan

@[expose] def InTarget2Star (K : Type) [Group K] : Prop :=
  InTarget2 K ∨ LieModel K .PSL 2 2 2 ∨ LieModel K .PSU 3 2 2 ∨ NativeSporadic.IsSporadic K .J1

end CFSG.GH74.GLS

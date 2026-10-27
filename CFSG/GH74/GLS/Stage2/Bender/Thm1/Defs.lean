module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Notation

variable {G : Type} [Group G]

@[expose] def piOf (X : Subgroup G) : Set ℕ := {r | r.Prime ∧ r ∣ Nat.card ↥X}

@[expose] def Inverts (z : G) (X : Subgroup G) : Prop := ∀ x ∈ X, z * x * z⁻¹ = x⁻¹

@[expose] def NF (z : G) (M X : Subgroup G) : Prop :=
  X ≤ Fm M ∧ X ≠ ⊥ ∧ z ∈ normalizer (X : Set G) ∧ normalizer (X : Set G) ≤ M

@[expose] def Ep (p : ℕ) (M : Subgroup G) : Subgroup G := pPrimeCoreOf p (Fm M)

@[expose] def TwoPrimes (X : Subgroup G) : Prop := 2 ≤ (piOf X).ncard

end Notation

@[expose] def IsPrimePowerGrp (X : Type) [Group X] : Prop := ∃ p : ℕ, p.Prime ∧ IsPGroup p X

section Choice

variable {G : Type} [Group G]

structure Hyp6A (z : G) : Prop where
  fitting : ∀ N ∈ maximalOverCentralizer z, Fs N = Fm N ∧ Fm N = pPrimeCoreOf 2 (Fm N)
  two_primes : ∃ M ∈ maximalOverCentralizer z, TwoPrimes (Fm M)

@[expose] def Adm (z : G) (M : Subgroup G) (p : ℕ) : Prop :=
  M ∈ maximalOverCentralizer z ∧ TwoPrimes (Fm M) ∧ p.Prime ∧ ¬ Op p M ≤ Cen z

structure Choice6 (z : G) (M : Subgroup G) (p : ℕ) : Prop where
  adm : Adm z M p
  inv : (∃ (M' : Subgroup G) (p' : ℕ), Adm z M' p' ∧ Inverts z (Op p' M')) → Inverts z (Op p M)

end Choice

structure Ctx6 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) (M : Subgroup G) (p : ℕ) :
    Prop where
  ctx : Stage2Ctx G z k S
  hyp : Hyp6A z
  choice : Choice6 z M p

section Families

variable {G : Type} [Group G]

@[expose] def QP (z : G) (p : ℕ) (P Q : Subgroup G) : Prop :=
  Q ≤ P ∧ Subgroup.Characteristic (Q.subgroupOf P) ∧
    (∀ x ∈ Q, x ^ p = 1) ∧ ⁅⁅Q, Q⁆, Q⁆ = ⊥ ∧ ⁅Q, P⁆ ≤ zOf Q ∧ ¬ Q ≤ Cen z

structure MinBad (z : G) (M : Subgroup G) (p : ℕ) (Q X : Subgroup G) : Prop where
  Q_mem : QP z p (Op p M) Q
  X_le : X ≤ Q
  X_ne : X ≠ ⊥
  X_inv : z ∈ normalizer (X : Set G)
  X_not : ¬ NF z M X
  minimal : ∀ Y : Subgroup G, Y ≤ Q → Y ≠ ⊥ → z ∈ normalizer (Y : Set G) → ¬ NF z M Y →
    Nat.card ↥X ≤ Nat.card ↥Y
  prefer : (∃ Y : Subgroup G, Y ≤ Q ∧ Y ≠ ⊥ ∧ z ∈ normalizer (Y : Set G) ∧ ¬ NF z M Y ∧
    Nat.card ↥Y = Nat.card ↥X ∧ ¬ Y ≤ Cen z) → ¬ X ≤ Cen z

end Families

end CFSG.GH74.GLS.Stage2.Bender.Thm1

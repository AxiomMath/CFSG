module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup

@[expose] def derivedCentralizer {Y : Type*} [Group Y] (u : Y) : Subgroup Y :=
  (_root_.commutator (centralizer ({u} : Set Y))).map (centralizer ({u} : Set Y)).subtype

structure RuFacts (Y : Type) [Group Y] : Prop where
  card_eq : Nat.card Y = 145926144000
  card_centralizer : ∀ v : Y, orderOf v = 2 →
    Nat.card (centralizer ({v} : Set Y)) = 245760 ∨
      Nat.card (centralizer ({v} : Set Y)) = 116480
  isConj_A : ∀ v w : Y, orderOf v = 2 → orderOf w = 2 →
    Nat.card (centralizer ({v} : Set Y)) = 245760 →
    Nat.card (centralizer ({w} : Set Y)) = 245760 → IsConj v w
  isConj_B : ∀ v w : Y, orderOf v = 2 → orderOf w = 2 →
    Nat.card (centralizer ({v} : Set Y)) = 116480 →
    Nat.card (centralizer ({w} : Set Y)) = 116480 → IsConj v w
  sq_A : ∀ v : Y, orderOf v = 2 → Nat.card (centralizer ({v} : Set Y)) = 245760 →
    ∃ y : Y, y ^ 2 = v
  pair : ∃ u a : Y, orderOf u = 2 ∧ Nat.card (centralizer ({u} : Set Y)) = 116480 ∧
    orderOf a = 2 ∧ Nat.card (centralizer ({a} : Set Y)) = 245760 ∧ a * u = u * a ∧
    a ∈ derivedCentralizer u ∧
    Nat.card ↥(centralizer ({a} : Set Y) ⊓ centralizer ({u} : Set Y)) = 256
  no_256 : ∀ p q : Y, orderOf p = 2 → orderOf q = 2 → p ≠ q → p * q = q * p →
    Nat.card (centralizer ({p} : Set Y)) = 245760 →
    Nat.card (centralizer ({q} : Set Y)) = 245760 →
    Nat.card ↥(centralizer ({p} : Set Y) ⊓ centralizer ({q} : Set Y)) ≠ 256

end CFSG.EvenSporadicStandard.RuStd

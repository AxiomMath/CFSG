module

public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

structure Hyp (a : V12) (D : Submodule (ZMod 2) V12) (L : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    Prop where
  ne_zero : a ≠ 0
  q_eq : q0 a = 0
  sing : ∀ x ∈ D, q0 x = 0
  finrank_eq : finrank (ZMod 2) D = 6
  mem : a ∈ D
  le : L ≤ gammaU
  card : Nat.card L = 32
  fix : ∀ l ∈ L, l a = a
  perp : ∀ l ∈ L, ∀ x, f0 x a = 0 → l x - x ∈ D
  comm : ∀ l ∈ L, ∀ d ∈ D, l d - d = 0 ∨ l d - d = a
  faithful : ∀ l ∈ L, (∀ d ∈ D, l d = d) → l = 1

structure StepATFacts : Prop where
  t1 : ∀ rep ∈ dReps, rep ≠ d0 →
    ∀ L : Subgroup (V12 ≃ₗ[ZMod 2] V12), ¬ Hyp (vecOf a0) (spanOf rep) L
  t2 : ∀ L : Subgroup (V12 ≃ₗ[ZMod 2] V12), Hyp (vecOf a0) (spanOf d0) L →
    ∃ c < 32, ∀ l : V12 ≃ₗ[ZMod 2] V12, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, l x = linOfRows r x
  t3 : ∀ c < 32, ∀ r ∈ compOf c, r.size = 12 ∧ ∀ x ∈ r, x < 4096

end CFSG.GF2Type.Smith1979.GammaU.StepA

module

public import CFSG.GF2Type.Smith1979.GammaU.Group
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module CFSG.GF2Type.Smith1979.GammaU

structure E0Facts (E : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (OB OA : V12 → Prop) (a0 w0 : V12) :
    Prop where
  cases : ∀ v : V12, v ≠ 0 → q0 v = 0 → OB v ∨ OA v
  B_sing : ∀ v : V12, OB v → v ≠ 0 ∧ q0 v = 0
  B_inv : ∀ e ∈ E, ∀ v : V12, OB v → OB (e v)
  A_inv : ∀ e ∈ E, ∀ v : V12, OA v → OA (e v)
  B_trans : ∀ v : V12, OB v → ∃ e ∈ E, e v = w0
  A_trans : ∀ v : V12, OA v → ∃ e ∈ E, e v = a0
  w0_mem : OB w0
  a0_mem : OA a0
  stab_w0 : ∀ P : Subgroup (V12 ≃ₗ[ZMod 2] V12),
    P ≤ E ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) w0 →
    (∀ s ∈ E ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) w0, ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → P = ⊥
  sub6 : ∀ U : Submodule (ZMod 2) V12, finrank (ZMod 2) U = 6 → a0 ∈ U →
    (∀ s ∈ E ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) a0, ∀ u ∈ U, s u ∈ U) →
    ∃ w ∈ U, OB w
  orbit : ∀ v : V12, OA v → f0 v w0 = 0 →
    64 ≤ Set.ncard {u : V12 | ∃ s ∈ E ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) w0, s v = u}

end CFSG.GF2Type.Smith1979.IdxFour

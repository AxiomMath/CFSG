module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.GF2Type.Smith1979.GammaU.CensusDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.RankThree.OrthogonalInvolutions

@[expose] def ModelOuter (t : V12 ≃ₗ[ZMod 2] V12) : Prop := fixSpace t ≤ commSpace t

@[expose] def ModelInner (Vt : Submodule (ZMod 2) V12) (t : V12 ≃ₗ[ZMod 2] V12) : Prop :=
  thetaU * t = t * thetaU ∧ finrank (ZMod 2) (fixSpace t) ≤ 8 ∧ (∀ r ∈ commSpace t, q0 r = 0) ∧
    (∀ w ∈ fixSpace t, (∀ p ∈ Vt ⊓ fixSpace t, f0 w p = 0) →
      ∃ p ∈ Vt ⊓ fixSpace t, ∃ r ∈ commSpace t, w = p + r) ∧
    (∀ v ∈ fixSpace t, q0 v = 0 → ∃ i : ℕ, ∃ u ∈ Vt ⊓ fixSpace t, ∃ r ∈ commSpace t,
      v = (thetaU ^ i) u + r)

structure ModelFacts (M K2 L : Subgroup (V12 ≃ₗ[ZMod 2] V12)) (x0 : V12 ≃ₗ[ZMod 2] V12)
    (a0 : V12) (Vt : Submodule (ZMod 2) V12) : Prop where
  M_le : M ≤ gammaU
  K2_le : K2 ≤ M
  K2_index : K2.relIndex M = 2
  x_mem : x0 ∈ M
  x_not_mem : x0 ∉ K2
  x_sq : x0 * x0 = 1
  x_comm : x0 * thetaU = thetaU * x0
  x_dim : finrank (ZMod 2) (commSpace x0) = 2
  x_sing : ∀ w ∈ commSpace x0, q0 w = 0
  x_cent : ¬ 2 ^ 9 ∣ Nat.card (M ⊓ Subgroup.centralizer ({x0} : Set (V12 ≃ₗ[ZMod 2] V12)) :
    Subgroup (V12 ≃ₗ[ZMod 2] V12))
  lemma5 : ∀ w ∈ commSpace x0, w ≠ 0 → ∀ P : Subgroup (V12 ≃ₗ[ZMod 2] V12),
    P ≤ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) w →
    (∀ s ∈ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) w, ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → Nat.card P ≠ 2 ^ 5
  stab_two : ∀ v : V12, v ≠ 0 → q0 v = 0 →
    2 ^ 8 ∣ Nat.card (M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) v :
      Subgroup (V12 ≃ₗ[ZMod 2] V12))
  base : ∀ v : V12, v ≠ 0 → q0 v = 0 → ∀ P : Subgroup (V12 ≃ₗ[ZMod 2] V12),
    P ≤ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) v →
    (∀ s ∈ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) v, ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → Nat.card P = 2 ^ 5 → ∃ m ∈ M, m v = a0
  lbar_unique : ∀ P : Subgroup (V12 ≃ₗ[ZMod 2] V12),
    P ≤ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) a0 →
    (∀ s ∈ M ⊓ MulAction.stabilizer (V12 ≃ₗ[ZMod 2] V12) a0, ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → Nat.card P = 2 ^ 5 → P = L
  vt_le : Vt ≤ Submodule.span (ZMod 2) {y | ∃ l ∈ L, ∃ x : V12, f0 x a0 = 0 ∧ l x - x = y}
  vt_rank : finrank (ZMod 2) Vt = 6
  inv_conj : ∀ t ∈ K2, t ≠ 1 → t * t = 1 → ∃ m ∈ M, m * t * m⁻¹ ∈ L
  lbar : ∀ t ∈ L, t ≠ 1 → ModelOuter t ∨ ModelInner Vt t

end CFSG.GF2Type.Smith1979.IdxFour

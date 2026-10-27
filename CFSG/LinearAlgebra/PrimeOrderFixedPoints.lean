module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.OrderOfElement
import CFSG.LinearAlgebra.SL2MinimalFaithful
import Mathlib.Tactic.Polynomial.Basic

public section

open Module

namespace CFSG.LinearAlgebra

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

@[instance_reducible] private noncomputable def representationMulDistribMulAction
    (ρ : Representation (ZMod 2) G W) :
    MulDistribMulAction G (Multiplicative W) where
  smul g x := Multiplicative.ofAdd (ρ g x.toAdd)
  one_smul x := by
    change Multiplicative.ofAdd (ρ 1 x.toAdd) = x
    rw [map_one, Module.End.one_apply, ofAdd_toAdd]
  mul_smul g h x := by
    change Multiplicative.ofAdd (ρ (g * h) x.toAdd) =
      Multiplicative.ofAdd (ρ g (ρ h x.toAdd))
    rw [map_mul, Module.End.mul_apply]
  smul_one g := by
    change Multiplicative.ofAdd (ρ g (0 : W)) = 1
    rw [map_zero, ofAdd_zero]
  smul_mul g x y := by
    change Multiplicative.ofAdd (ρ g (x.toAdd + y.toAdd)) =
      Multiplicative.ofAdd (ρ g x.toAdd) * Multiplicative.ofAdd (ρ g y.toAdd)
    rw [map_add, ofAdd_add]

private noncomputable def representationToMulAut (ρ : Representation (ZMod 2) G W) :
    G →* MulAut (Multiplicative W) :=
  letI := representationMulDistribMulAction ρ
  MulDistribMulAction.toMulAut G (Multiplicative W)

private theorem representationToMulAut_apply (ρ : Representation (ZMod 2) G W) (g : G) (w : W) :
    representationToMulAut ρ g (Multiplicative.ofAdd w) = Multiplicative.ofAdd (ρ g w) := by
  letI := representationMulDistribMulAction ρ
  rfl

private theorem representationToMulAut_ne_one {ρ : Representation (ZMod 2) G W} {g : G}
    (h : ρ g ≠ 1) : representationToMulAut ρ g ≠ 1 := by
  intro hh
  apply h
  ext w
  have := congrArg (fun f : MulAut (Multiplicative W) => f (Multiplicative.ofAdd w)) hh
  simpa [representationToMulAut_apply, MulAut.one_apply] using this

theorem exists_prime_dvd_two_pow_sub_one_of_ne_one
    (ρ : Representation (ZMod 2) G W) {g : G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hord : orderOf g = r) (hρ : ρ g ≠ 1) :
    ∃ b : ℕ, 0 < b ∧ 2 ^ b ≤ Nat.card W ∧ r ∣ 2 ^ b - 1 := by
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite (R := ZMod 2)
  set d := Module.finrank (ZMod 2) W with hd
  have hW : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcard : Nat.card (Multiplicative W) = 2 ^ d :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans hW
  obtain ⟨e, he, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow (p := 2) (d := d)
    (ℓ := r) Nat.prime_two hr (representationToMulAut ρ) hord
    (representationToMulAut_ne_one hρ) hcard
  refine ⟨d - e, by omega, ?_, ?_⟩
  · calc 2 ^ (d - e) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      _ = Nat.card W := hW.symm
  · have hsplit : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
      have hpow : 2 ^ d = 2 ^ e * 2 ^ (d - e) := by
        rw [← pow_add, Nat.add_sub_cancel' he.le]
      calc 2 ^ d - 2 ^ e = 2 ^ e * 2 ^ (d - e) - 2 ^ e * 1 := by rw [hpow, mul_one]
        _ = 2 ^ e * (2 ^ (d - e) - 1) := (Nat.mul_sub_left_distrib ..).symm
    rw [hsplit] at hdvd
    rcases hr.dvd_mul.mp hdvd with h | h
    · exfalso
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    · exact h

end CFSG.LinearAlgebra

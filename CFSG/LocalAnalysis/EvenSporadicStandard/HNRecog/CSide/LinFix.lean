module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module

private lemma cSide_linFix_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) :
    v + v = 0 := by
  rw [add_eq_zero_iff_eq_neg]
  rw [← neg_one_smul (ZMod 2) v, CharTwo.neg_eq (1 : ZMod 2), one_smul]

private lemma cSide_linFix_neg_eq_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : V) : -v = v := by
  rw [← neg_one_smul (ZMod 2) v, CharTwo.neg_eq (1 : ZMod 2), one_smul]

private lemma cSide_linFix_card_fixed_eq_card_ker {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (b : V ≃ₗ[ZMod 2] V) :
    Nat.card {v : V // b v = v} =
      Nat.card (LinearMap.ker ((b : V →ₗ[ZMod 2] V) + 1)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro v
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
  constructor
  · intro h
    have h' : (b : V →ₗ[ZMod 2] V) v = v := by simpa using h
    rw [h', cSide_linFix_add_self]
  · intro h
    rw [add_eq_zero_iff_eq_neg] at h
    have h' : (b : V →ₗ[ZMod 2] V) v = v := by
      rw [h]
      exact cSide_linFix_neg_eq_self v
    simpa using h'

private lemma cSide_linFix_card_ker_eq_two_pow_finrank {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (f : V →ₗ[ZMod 2] V) :
    Nat.card (LinearMap.ker f) = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f)
  rwa [Nat.card_zmod] at h

theorem cSide_four_le_finrank_range {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 8) (b : V ≃ₗ[ZMod 2] V)
    (hfix : Nat.card {v : V // b v = v} ≤ 16) :
    4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)) := by
  set f : V →ₗ[ZMod 2] V := (b : V →ₗ[ZMod 2] V) + 1
  have hcard : Nat.card {v : V // b v = v} = 2 ^ finrank (ZMod 2) (LinearMap.ker f) := by
    rw [cSide_linFix_card_fixed_eq_card_ker b, cSide_linFix_card_ker_eq_two_pow_finrank f]
  have hle : 2 ^ finrank (ZMod 2) (LinearMap.ker f) ≤ 2 ^ 4 := by
    rw [← hcard]
    exact le_trans hfix (by norm_num)
  have hker : finrank (ZMod 2) (LinearMap.ker f) ≤ 4 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hV] at hrn
  omega

theorem cSide_card_fix_of_free {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : finrank (ZMod 2) V = 8) (b : V ≃ₗ[ZMod 2] V) (hb : b * b = 1)
    (hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1))) :
    Nat.card {v : V // b v = v} = 2 ^ 4 := by
  set f : V →ₗ[ZMod 2] V := (b : V →ₗ[ZMod 2] V) + 1
  have hcomp : f.comp f = 0 := by
    ext v
    have hbEnd : (b : V →ₗ[ZMod 2] V) * (b : V →ₗ[ZMod 2] V) = 1 := by
      ext w
      simpa using congrArg (fun e : V ≃ₗ[ZMod 2] V => e w) hb
    have hbb : (b : V →ₗ[ZMod 2] V) ((b : V →ₗ[ZMod 2] V) v) = v := by
      have h := LinearMap.congr_fun hbEnd v
      rwa [Module.End.mul_apply, Module.End.one_apply] at h
    rw [LinearMap.comp_apply]
    change ((b : V →ₗ[ZMod 2] V) + 1) (((b : V →ₗ[ZMod 2] V) + 1) v) = 0
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.add_apply, Module.End.one_apply]
    rw [map_add, hbb]
    rw [add_assoc, ← add_assoc ((b : V →ₗ[ZMod 2] V) v) ((b : V →ₗ[ZMod 2] V) v) v,
      cSide_linFix_add_self ((b : V →ₗ[ZMod 2] V) v), zero_add, cSide_linFix_add_self v]
  have hle : LinearMap.range f ≤ LinearMap.ker f :=
    LinearMap.range_le_ker_iff.mpr hcomp
  have hmono : finrank (ZMod 2) (LinearMap.range f) ≤ finrank (ZMod 2) (LinearMap.ker f) :=
    Submodule.finrank_mono hle
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hV] at hrn
  have hker : finrank (ZMod 2) (LinearMap.ker f) = 4 := by omega
  rw [cSide_linFix_card_fixed_eq_card_ker b, cSide_linFix_card_ker_eq_two_pow_finrank f, hker]

theorem cSide_exists_fixed_of_pGroup {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Nontrivial V] {H : Type*} [Group H] (hH : IsPGroup 2 H) (ρ : H →* (V ≃ₗ[ZMod 2] V)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h : H, ρ h v = v := by
  have hcardV : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
  have hdvd : 2 ∣ Nat.card V := by
    rw [hcardV]
    refine dvd_pow_self 2 (fun h0 => ?_)
    have h1 : Nat.card V = 1 := by rw [hcardV, h0, pow_zero]
    have hlt : 1 < Nat.card V := Finite.one_lt_card (α := V)
    omega
  let act : MulAction H V :=
    { smul := fun h v => ρ h v
      one_smul := fun v => by
        change ρ 1 v = v
        rw [map_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
      mul_smul := fun h₁ h₂ v => by
        change ρ (h₁ * h₂) v = ρ h₁ (ρ h₂ v)
        rw [map_mul, LinearEquiv.mul_apply] }
  letI : MulAction H V := act
  have hfixed : (0 : V) ∈ MulAction.fixedPoints H V := fun h => map_zero (ρ h)
  obtain ⟨b, hb, hb0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd hfixed
  exact ⟨b, hb0.symm, fun h => hb h⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Free

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem eq_one_of_pow_five_of_finrank_le_three (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1)
    (hd : finrank (ZMod 2) V ≤ 3) : γ = 1 := by
  have h4 : 4 ∣ finrank (ZMod 2) (LinearMap.range (γ - 1)) :=
    Fpf.four_dvd_finrank_range γ h
  have hle : finrank (ZMod 2) (LinearMap.range (γ - 1)) ≤ finrank (ZMod 2) V :=
    Submodule.finrank_le _
  have hlt : finrank (ZMod 2) (LinearMap.range (γ - 1)) < 4 :=
    lt_of_le_of_lt (le_trans hle hd) (by norm_num)
  have hzero : finrank (ZMod 2) (LinearMap.range (γ - 1)) = 0 :=
    Nat.eq_zero_of_dvd_of_lt h4 hlt
  have hbot : LinearMap.range (γ - 1) = ⊥ :=
    (Submodule.finrank_eq_zero (R := ZMod 2)).mp hzero
  have hsub : γ - 1 = 0 := LinearMap.range_eq_bot.mp hbot
  exact sub_eq_zero.mp hsub

theorem exists_eq_add_of_four_le_finrank_range (b : V →ₗ[ZMod 2] V) (hb : b * b = 1)
    (h8 : finrank (ZMod 2) V = 8)
    (h4 : 4 ≤ finrank (ZMod 2) (LinearMap.range (b + 1))) (x : V) (hx : b x = x) :
    ∃ y : V, x = y + b y := by
  have hchar : ∀ v : V, v + v = 0 := fun v => by
    have h := two_smul (ZMod 2) v
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  have hcharE : ∀ f : Module.End (ZMod 2) V, f + f = 0 := fun f => by
    have h := two_smul (ZMod 2) f
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
    exact h.symm
  have hsqEnd : (b + 1) * (b + 1) = 0 := by
    rw [mul_add, mul_one, add_mul, one_mul, hb]
    rw [add_assoc, ← add_assoc b b 1, hcharE b, zero_add, hcharE 1]
  have hsq : ∀ v : V, (b + 1) ((b + 1) v) = 0 := fun v => by
    rw [← Module.End.mul_apply, hsqEnd, LinearMap.zero_apply]
  have hrange_le_ker : LinearMap.range (b + 1) ≤ LinearMap.ker (b + 1) := by
    rintro w ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact hsq v
  have hrn := LinearMap.finrank_range_add_finrank_ker (b + 1)
  rw [h8] at hrn
  have hker_le : finrank (ZMod 2) (LinearMap.ker (b + 1)) ≤ 4 := by omega
  have hrange_le : finrank (ZMod 2) (LinearMap.range (b + 1))
      ≤ finrank (ZMod 2) (LinearMap.ker (b + 1)) := Submodule.finrank_mono hrange_le_ker
  have heq_finrank : finrank (ZMod 2) (LinearMap.range (b + 1))
      = finrank (ZMod 2) (LinearMap.ker (b + 1)) := by omega
  have heq : LinearMap.range (b + 1) = LinearMap.ker (b + 1) :=
    Submodule.eq_of_le_of_finrank_eq hrange_le_ker heq_finrank
  have hxker : x ∈ LinearMap.ker (b + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, hx, Module.End.one_apply]
    exact hchar x
  have hxrange : x ∈ LinearMap.range (b + 1) := by
    rw [heq]
    exact hxker
  rw [LinearMap.mem_range] at hxrange
  obtain ⟨y, hy⟩ := hxrange
  refine ⟨y, ?_⟩
  rw [← hy, LinearMap.add_apply, Module.End.one_apply, add_comm]

end CFSG.EvenSporadicStandard.HNRecog.Free

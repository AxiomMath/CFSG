module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

open Finset

variable {p : ℕ} [Fact p.Prime] {G P U : Type*} [Group G] [Group P] [AddCommGroup U]
  [Module (ZMod p) U]

@[expose] def fixedSubmodule (σ : P →* (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U where
  carrier := {u | ∀ x, σ x u = u}
  add_mem' := fun {a b} ha hb x => by simp [ha x, hb x]
  zero_mem' := fun x => by simp
  smul_mem' := fun c u hu x => by simp [hu x]

@[expose] def fixedKernel (ρ : G →* (U ≃ₗ[ZMod p] U)) (σ : P →* (U ≃ₗ[ZMod p] U)) : Subgroup G where
  carrier := {g | ∀ u ∈ fixedSubmodule σ, ρ g u = u}
  mul_mem' := fun {a b} ha hb u hu => by
    have := hb u hu
    simp [this, ha u hu]
  one_mem' := fun u _ => by simp
  inv_mem' := fun {a} ha u hu => by
    have h1 := ha u hu
    have h2 : ((ρ a)⁻¹ * ρ a) u = u := by simp
    rw [LinearEquiv.mul_apply, h1] at h2
    simpa only [map_inv] using h2

theorem mem_fixedKernel {ρ : G →* (U ≃ₗ[ZMod p] U)} {σ : P →* (U ≃ₗ[ZMod p] U)} {g : G} :
    g ∈ fixedKernel ρ σ ↔ ∀ u ∈ fixedSubmodule σ, ρ g u = u := Iff.rfl

variable [Finite U]

theorem exists_fixed_of_invariant (hP : IsPGroup p P) (σ : P →* (U ≃ₗ[ZMod p] U))
    (N : Submodule (ZMod p) U) (hN : ∀ x u, u ∈ N → σ x u ∈ N) (hne : N ≠ ⊥) :
    ∃ u ∈ N, u ≠ 0 ∧ ∀ x, σ x u = u := by
  letI : MulAction P N :=
    { smul := fun x u => ⟨σ x u, hN x u u.2⟩
      one_smul := fun u => by ext; simp [HSMul.hSMul, SMul.smul]
      mul_smul := fun x y u => by ext; simp [HSMul.hSMul, SMul.smul] }
  have hsmul : ∀ (x : P) (u : N), ((x • u : N) : U) = σ x u := fun _ _ => rfl
  haveI : Module.Finite (ZMod p) N := inferInstance
  have hcard : Nat.card N = p ^ Module.finrank (ZMod p) N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hpos : 0 < Module.finrank (ZMod p) N := Module.finrank_pos_iff.mpr
    (Submodule.nontrivial_iff_ne_bot.mpr hne)
  have hdvd : p ∣ Nat.card N := hcard ▸ dvd_pow_self p hpos.ne'
  have h0 : (0 : N) ∈ MulAction.fixedPoints P N := fun x => by
    ext
    simp [hsmul]
  obtain ⟨b, hb, hb0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd h0
  refine ⟨b, b.2, fun h => hb0 ?_, fun x => ?_⟩
  · exact Subtype.ext h.symm
  · have := hb x
    exact congrArg Subtype.val this

variable {ρ : G →* (U ≃ₗ[ZMod p] U)} {σ : P →* (U ≃ₗ[ZMod p] U)}

theorem eq_of_coprime_of_mem_fixedKernel (hP : IsPGroup p P)
    (hcomm : ∀ g x u, ρ g (σ x u) = σ x (ρ g u)) {k : G} (hk : k ∈ fixedKernel ρ σ)
    (hcop : Nat.Coprime (orderOf (ρ k)) p) (u : U) : ρ k u = u := by
  have pow_comm (g : G) (x : P) (i : ℕ) (v : U) :
      ((ρ g) ^ i) (σ x v) = σ x (((ρ g) ^ i) v) := by
    induction i generalizing v with
    | zero => simp
    | succ i ih => rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hcomm, ih]
  set n := orderOf (ρ k) with hn
  let s : Module.End (ZMod p) U :=
    ∑ i ∈ range n, (((ρ k) ^ i : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
  have hs : ∀ v, s v = ∑ i ∈ range n, ((ρ k) ^ i) v := fun v => by
    simp [s, LinearMap.sum_apply]
  have hsk : ∀ v, s (ρ k v) = s v := fun v => by
    rw [hs, hs]
    have h1 : ∀ i, ((ρ k) ^ i) (ρ k v) = ((ρ k) ^ (i + 1)) v := fun i => by
      rw [pow_succ, LinearEquiv.mul_apply]
    simp only [h1]
    have e1 := Finset.sum_range_succ (fun i => ((ρ k) ^ i) v) n
    have e2 := Finset.sum_range_succ' (fun i => ((ρ k) ^ i) v) n
    have h3 : ((ρ k) ^ n) v = ((ρ k) ^ 0) v := by simp [hn, pow_orderOf_eq_one]
    have e3 := e2.symm.trans e1
    rw [h3] at e3
    exact add_right_cancel e3
  let N : Submodule (ZMod p) U := LinearMap.ker s
  have hN : ∀ x v, v ∈ N → σ x v ∈ N := fun x v hv => by
    simp only [N, LinearMap.mem_ker] at hv ⊢
    rw [hs] at hv ⊢
    simp only [pow_comm, ← map_sum]
    rw [hv]
    simp
  have hbot : N = ⊥ := by
    by_contra hne
    obtain ⟨v, hvN, hv0, hvfix⟩ := exists_fixed_of_invariant hP σ N hN hne
    have hvk : ρ k v = v := (mem_fixedKernel.mp hk) v hvfix
    have hpow : ∀ i : ℕ, ((ρ k) ^ i) v = v := fun i => by
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, LinearEquiv.mul_apply, hvk, ih]
    have hsv : s v = (n : ZMod p) • v := by
      rw [hs]
      simp [hpow, ← Nat.cast_smul_eq_nsmul (ZMod p)]
    have hnz : (n : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hd)
    have : s v = 0 := hvN
    rw [hsv] at this
    exact hv0 ((smul_eq_zero.mp this).resolve_left hnz)
  have : ρ k u - u ∈ N := by
    simp only [N, LinearMap.mem_ker, map_sub, hsk, sub_self]
  rw [hbot] at this
  exact sub_eq_zero.mp (Submodule.mem_bot _ |>.mp this)

end CFSG.GroupTheory.AutomorphismAction.CommutingPGroup

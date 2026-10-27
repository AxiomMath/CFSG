module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4QuadOdd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12
open scoped commutatorElement

structure Hyp89 (p : ℕ) {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  faithful : Function.Injective ρ
  norm : a ∈ normalizer (K : Set Γ)
  quasi : IsQuasisimple ↥K
  quad : (((ρ a : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0
  acts : ⁅K, zpowers a⁆ ≠ ⊥

namespace Hyp89

variable {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ}

theorem pow_prime (hf : Hyp89 p ρ K a) : a ^ p = 1 := by
  have := Fact.mk hf.prime
  apply hf.faithful
  rw [map_pow, map_one]
  exact quadratic_pow_prime_eq_one (F := ZMod p) (V := V) hf.quad

theorem centralizes_odd [Finite Γ] [Module.Finite (ZMod p) V] (hf : Hyp89 p ρ K a) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) {Q : Subgroup Γ} (hQ : IsPGroup r ↥Q)
    (ha : a ∈ normalizer (Q : Set Γ)) : Q ≤ centralizer ({a} : Set Γ) := by
  have := Fact.mk hf.prime
  have := Fact.mk hr
  exact quadratic_le_centralizer_odd (F := ZMod p) (V := V) hf.odd hr2 hrp ρ hf.faithful hf.quad
    hQ ha

theorem centralizes_abelian [Finite Γ] [Module.Finite (ZMod p) V] (hf : Hyp89 p ρ K a)
    {Q : Subgroup Γ} (hQ : IsPGroup 2 ↥Q) (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (ha : a ∈ normalizer (Q : Set Γ)) : Q ≤ centralizer ({a} : Set Γ) := by
  have := Fact.mk hf.prime
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.2
    (quadratic_centralizes_abelian (F := ZMod p) (V := V) hf.odd (Ne.symm hf.odd) ρ hf.faithful
      hf.quad hQ hab ha x hx).symm

end Hyp89

theorem Mod55.toHyp89 {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} {a : Γ} {P : Subgroup Γ}
    (hf : Mod55 p ρ K a P) : Hyp89 p ρ K a :=
  ⟨hf.prime, hf.odd, hf.faithful,
    by rw [Subgroup.normalizer_eq_top_iff.mpr hf.normal]; exact Subgroup.mem_top a,
    hf.quasi, hf.quad, hf.acts⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

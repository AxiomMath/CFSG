module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4QuadOdd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12

namespace Mod55

variable {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] [Module.Finite (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ}
  {K : Subgroup Γ} {a : Γ} {P : Subgroup Γ}

omit [Finite Γ] [Module.Finite (ZMod p) V] in
theorem pow_prime (hf : Mod55 p ρ K a P) : a ^ p = 1 := by
  have := Fact.mk hf.prime
  apply hf.faithful
  rw [map_pow, map_one]
  exact quadratic_pow_prime_eq_one (F := ZMod p) (V := V) hf.quad

theorem centralizes_odd (hf : Mod55 p ρ K a P) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) {Q : Subgroup Γ} (hQ : IsPGroup r ↥Q) (ha : a ∈ normalizer (Q : Set Γ)) :
    Q ≤ centralizer ({a} : Set Γ) := by
  have := Fact.mk hf.prime
  have := Fact.mk hr
  exact quadratic_le_centralizer_odd (F := ZMod p) (V := V) hf.odd hr2 hrp ρ hf.faithful hf.quad
    hQ ha

end Mod55

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

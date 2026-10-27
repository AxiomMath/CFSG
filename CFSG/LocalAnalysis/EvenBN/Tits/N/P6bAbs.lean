module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

private theorem p6b_coe_pow {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] (x : Q ≃ₗ[ZMod 2] Q)
    (U : Submodule (ZMod 2) Q) (f : Function.End U) (hf : ∀ u : U, (f u : Q) = x u) (m : ℕ) (u : U) :
    (((f ^ m) u : U) : Q) = (x ^ m) u := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', LinearEquiv.mul_apply, ← ih u, ← hf]
    rfl

private theorem p6b_card_modEq {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (x : Q ≃ₗ[ZMod 2] Q) (p n : ℕ) [Fact p.Prime] (hx : x ^ p ^ n = 1) (U : Submodule (ZMod 2) Q)
    (hU : ∀ u ∈ U, x u ∈ U) (K : Submodule (ZMod 2) Q) (hK : ∀ v : Q, v ∈ K ↔ v ∈ U ∧ x v = v) :
    Nat.card U ≡ Nat.card K [MOD p] := by
  classical
  haveI : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨x u, hU u u.2⟩
  have hf : f ^ p ^ n = 1 := by
    refine funext fun u => Subtype.ext ?_
    rw [p6b_coe_pow x U f (fun u => rfl), hx]
    rfl
  have key := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := n) hf
  have hcard : Nat.card (Function.fixedPoints f) = Nat.card K := by
    refine Nat.card_congr
      { toFun := fun u => ⟨u.1.1, (hK u.1.1).2 ⟨u.1.2, congrArg Subtype.val u.2⟩⟩
        invFun := fun k => ⟨⟨k.1, ((hK k.1).1 k.2).1⟩, Subtype.ext ((hK k.1).1 k.2).2⟩
        left_inv := fun u => rfl
        right_inv := fun k => rfl }
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard] at key
  exact key

theorem card_invariant_cases {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (hQ : Nat.card Q = 2 ^ 8) (x : Q ≃ₗ[ZMod 2] Q) (hx5 : x ^ 5 = 1)
    (hfix : ∀ v : Q, x v = v → v = 0) (U : Submodule (ZMod 2) Q) (hU : ∀ u ∈ U, x u ∈ U) :
    Nat.card U = 1 ∨ Nat.card U = 2 ^ 4 ∨ Nat.card U = 2 ^ 8 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hbot : Nat.card (⊥ : Submodule (ZMod 2) Q) = 1 := by simp
  have h5 : Nat.card U ≡ 1 [MOD 5] := by
    rw [← hbot]
    refine p6b_card_modEq x 5 1 (by simpa using hx5) U hU ⊥ fun v => ?_
    rw [Submodule.mem_bot]
    refine ⟨?_, fun h => hfix v h.2⟩
    rintro rfl
    exact ⟨U.zero_mem, map_zero x⟩
  have hdvd : Nat.card U ∣ 2 ^ 8 := by
    rw [← hQ]
    exact AddSubgroup.card_addSubgroup_dvd_card U.toAddSubgroup
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hkU] at h5 ⊢
  interval_cases k <;> first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; rfl)
    | exact absurd h5 (by decide)

theorem trivial_of_commuting_involution {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]
    (hQ : Nat.card Q = 2 ^ 8) (x t : Q ≃ₗ[ZMod 2] Q) (hx5 : x ^ 5 = 1)
    (hfix : ∀ v : Q, x v = v → v = 0) (ht2 : t ^ 2 = 1) (htx : t * x = x * t)
    (U : Submodule (ZMod 2) Q) (hUx : ∀ u ∈ U, x u ∈ U) (hUt : ∀ u ∈ U, t u ∈ U)
    (h16 : Nat.card U = 2 ^ 4) : ∀ u ∈ U, t u = u := by
  let K : Submodule (ZMod 2) Q :=
    { carrier := {v | v ∈ U ∧ t v = v}
      add_mem' := by
        rintro a b ⟨ha, hta⟩ ⟨hb, htb⟩
        exact ⟨U.add_mem ha hb, by rw [map_add, hta, htb]⟩
      zero_mem' := ⟨U.zero_mem, map_zero t⟩
      smul_mem' := by
        rintro c a ⟨ha, hta⟩
        exact ⟨U.smul_mem c ha, by rw [map_smul, hta]⟩ }
  have hK : ∀ v : Q, v ∈ K ↔ v ∈ U ∧ t v = v := fun v => Iff.rfl
  have hKx : ∀ v ∈ K, x v ∈ K := by
    rintro v ⟨hv, htv⟩
    refine ⟨hUx v hv, ?_⟩
    have h := congrArg (fun g : Q ≃ₗ[ZMod 2] Q => g v) htx
    simp only [LinearEquiv.mul_apply] at h
    rw [h, htv]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : Nat.card U ≡ Nat.card K [MOD 2] :=
    p6b_card_modEq t 2 1 (by simpa using ht2) U hUt K hK
  have hKU : K ≤ U := fun v hv => hv.1
  have hle : Nat.card K ≤ Nat.card U :=
    Nat.card_le_card_of_injective (Submodule.inclusion hKU) (Submodule.inclusion_injective hKU)
  have hK16 : Nat.card K = 2 ^ 4 := by
    rcases card_invariant_cases hQ x hx5 hfix K hKx with h | h | h
    · rw [h, h16] at h2
      exact absurd h2 (by decide)
    · exact h
    · rw [h, h16] at hle
      exact absurd hle (by decide)
  have hKeq : K.toAddSubgroup = U.toAddSubgroup :=
    AddSubgroup.eq_of_le_of_card_ge hKU (by show Nat.card U ≤ Nat.card K; rw [hK16, h16])
  intro u hu
  have hu' : u ∈ K.toAddSubgroup := hKeq ▸ hu
  exact hu'.2

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

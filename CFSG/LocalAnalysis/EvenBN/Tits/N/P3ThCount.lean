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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

section Count

variable {V : Type*} [Group V] [Finite V]

theorem card_modEq_fixed {p : ℕ} [Fact p.Prime] (G : Subgroup (MulAut V)) (hG : IsPGroup p G)
    (U : Subgroup V) (hU : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) :
    Nat.card U ≡ Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} [MOD p] := by
  letI : SMul G U := ⟨fun g u => ⟨g.1 u.1, hU g.1 g.2 u.1 u.2⟩⟩
  letI : MulAction G U :=
    { one_smul := fun u => Subtype.ext (by change ((1 : G) : MulAut V) u.1 = u.1; simp)
      mul_smul := fun g h u => Subtype.ext (by
        change ((g * h : G) : MulAut V) u.1 = g.1 (h.1 u.1)
        simp) }
  have h := hG.card_modEq_card_fixedPoints (α := U)
  have e : Nat.card (MulAction.fixedPoints G U) = Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    constructor
    · intro hu g hg
      have := hu ⟨g, hg⟩
      exact congrArg Subtype.val this
    · intro hu g
      exact Subtype.ext (hu g.1 g.2)
  rw [e] at h
  exact h

theorem exists_ne_one_fixed {p : ℕ} [Fact p.Prime] (G : Subgroup (MulAut V)) (hG : IsPGroup p G)
    (U : Subgroup V) (hU : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U) (hp : p ∣ Nat.card U) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ g ∈ G, g u = u := by
  have h := card_modEq_fixed G hG U hU
  have hF : p ∣ Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} := by
    have := (Nat.modEq_zero_iff_dvd.2 hp).symm.trans h
    exact Nat.modEq_zero_iff_dvd.1 this.symm
  haveI : Nonempty {u : U // ∀ g ∈ G, g u.1 = u.1} := ⟨⟨⟨1, one_mem U⟩, fun g hg => by simp⟩⟩
  have hpos : 0 < Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} := Nat.card_pos
  have hge : p ≤ Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} := Nat.le_of_dvd hpos hF
  have hp2 := (Fact.out : p.Prime).two_le
  by_contra hcon
  push_neg at hcon
  have hsub : Subsingleton {u : U // ∀ g ∈ G, g u.1 = u.1} := by
    refine ⟨fun a b => ?_⟩
    have ha : a.1.1 = 1 := by
      by_contra hne
      obtain ⟨g, hg, hne'⟩ := hcon a.1.1 a.1.2 hne
      exact hne' (a.2 g hg)
    have hb : b.1.1 = 1 := by
      by_contra hne
      obtain ⟨g, hg, hne'⟩ := hcon b.1.1 b.1.2 hne
      exact hne' (b.2 g hg)
    exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
  have hcard1 : Nat.card {u : U // ∀ g ∈ G, g u.1 = u.1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨hsub, ⟨⟨⟨1, one_mem U⟩, fun g hg => by simp⟩⟩⟩
  omega

theorem mem_iff_of_forall_mem (g : MulAut V) (U : Subgroup V) (hU : ∀ u ∈ U, g u ∈ U) (u : V) :
    u ∈ U ↔ g u ∈ U := by
  refine ⟨hU u, fun hu => ?_⟩
  let f : U → U := fun w => ⟨g w.1, hU w.1 w.2⟩
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext (g.injective (congrArg Subtype.val h))
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨g u, hu⟩
  have : g w.1 = g u := congrArg Subtype.val hw
  rw [← g.injective this]
  exact w.2

@[expose] def stabSubgroup (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ u, u ∈ U ↔ g u ∈ U}
  mul_mem' := by
    intro g h hg hh u
    rw [hh u, hg (h u), MulAut.mul_apply]
  one_mem' := by
    intro u
    simp
  inv_mem' := by
    intro g hg u
    rw [hg (g⁻¹ u)]
    simp

@[expose] def fixSub (g : MulAut V) : Subgroup V :=
  MonoidHom.eqLocus (g : V →* V) (MonoidHom.id V)

theorem card_fixed_subtype_eq (g : MulAut V) (U : Subgroup V) :
    Nat.card {u : U // g u.1 = u.1} = Nat.card ↥(U ⊓ fixSub g) :=
  Nat.card_congr
    { toFun := fun u => ⟨u.1.1, u.1.2, u.2⟩
      invFun := fun v => ⟨⟨v.1, v.2.1⟩, v.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_modEq_x (x : MulAut V) (hx5 : x ^ 5 = 1) (U : Subgroup V)
    (hU : ∀ u ∈ U, x u ∈ U) : Nat.card U ≡ Nat.card ↥(U ⊓ fixSub x) [MOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hG : IsPGroup 5 (zpowers x) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    obtain ⟨g, n, rfl⟩ := g
    show (x ^ n) ^ (5 ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx5, one_zpow]
  have hxs : x ∈ stabSubgroup U := fun u => mem_iff_of_forall_mem x U hU u
  have hinv : ∀ g ∈ zpowers x, ∀ u ∈ U, g u ∈ U := fun g hg u hu =>
    ((zpowers_le.2 hxs hg) u).1 hu
  have h := card_modEq_fixed (p := 5) (zpowers x) hG U hinv
  have e : Nat.card {u : U // ∀ g ∈ zpowers x, g u.1 = u.1} = Nat.card {u : U // x u.1 = u.1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
    constructor
    · intro hu
      exact hu x (mem_zpowers x)
    · intro hu g hg
      obtain ⟨n, rfl⟩ := hg
      show (x ^ n) u.1 = u.1
      have hfix : ∀ m : ℕ, (x ^ m) u.1 = u.1 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, MulAut.mul_apply, hu, ih]
      have hx1 : x⁻¹ u.1 = u.1 := by
        have := congrArg (fun w => x⁻¹ w) hu
        simpa using this.symm
      have hfix' : ∀ m : ℕ, (x⁻¹ ^ m) u.1 = u.1 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, MulAut.mul_apply, hx1, ih]
      cases n with
      | ofNat m =>
        rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact hfix m
      | negSucc m =>
        rw [zpow_negSucc, ← inv_pow]
        exact hfix' (m + 1)
  rw [e, card_fixed_subtype_eq] at h
  exact h

theorem card_mod_five_of_fpf (x : MulAut V) (hx5 : x ^ 5 = 1) (U : Subgroup V)
    (hU : ∀ u ∈ U, x u ∈ U) (hfpf : ∀ u ∈ U, x u = u → u = 1) : Nat.card U % 5 = 1 := by
  have h := card_modEq_x x hx5 U hU
  have hF : U ⊓ fixSub x = ⊥ := by
    refine eq_bot_iff.2 fun u hu => ?_
    exact (mem_bot.2 (hfpf u hu.1 hu.2))
  rw [hF, Subgroup.card_bot] at h
  exact h

theorem card_inf_ker_mul_card_map (f : V →* V) (U : Subgroup V) :
    Nat.card ↥(f.ker ⊓ U : Subgroup V) * Nat.card ↥(U.map f) = Nat.card U := by
  have h := Subgroup.card_ker_mul_card_range (f.comp U.subtype)
  have hk : (f.comp U.subtype).ker = f.ker.subgroupOf U := rfl
  have hr : (f.comp U.subtype).range = U.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hk, hr] at h
  have hc : Nat.card (f.ker.subgroupOf U) = Nat.card ↥(f.ker ⊓ U : Subgroup V) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : f.ker ⊓ U ≤ U)).toEquiv
  rw [hc] at h
  exact h

theorem two_pow_mod_five_one {k : ℕ} (hk : k ≤ 10) (h : 2 ^ k % 5 = 1) :
    k = 0 ∨ k = 4 ∨ k = 8 := by
  interval_cases k <;> simp_all

end Count

end CFSG.LocalAnalysis.EvenBN.Tits.N

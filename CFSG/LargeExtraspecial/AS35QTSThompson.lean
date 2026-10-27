module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open Subgroup

variable {G : Type*} [Group G]

@[expose] noncomputable def thompsonCount (z w y : G) : ℕ :=
  {p : G × G | IsConj z p.1 ∧ IsConj w p.2 ∧ y ∈ zpowers (p.1 * p.2)}.ncard

theorem ncard_conj_mul_card_centralizer [Finite G] (z : G) :
    {y | IsConj z y}.ncard * Nat.card (centralizer ({z} : Set G)) = Nat.card G := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) z)
  rw [Nat.card_prod] at h
  have horb : MulAction.orbit (ConjAct G) z = {y | IsConj z y} := by
    ext y
    rw [ConjAct.mem_orbit_conjAct]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [horb, Nat.card_coe_set_eq, ← Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr ConjAct.ofConjAct.toEquiv] at h
  exact h

theorem isConj_of_odd {x v : G} (hx : x * x = 1) (hv : v * v = 1) (hodd : Odd (orderOf (x * v))) :
    IsConj x v := by
  obtain ⟨k, hk⟩ := hodd
  set r := x * v with hrdef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hrdef, mul_inv_rev, hxinv, hvinv, ← mul_assoc x x v, hx, one_mul]
  have hxr' : x * r⁻¹ * x⁻¹ = r := by
    have := congrArg (·⁻¹) hxr
    simpa [mul_assoc] using this
  have h1 : ∀ j : ℕ, r ^ j * x * (r ^ j)⁻¹ = r ^ (2 * j) * x := by
    intro j
    have h2 : x * (r ^ j)⁻¹ * x⁻¹ = r ^ j := by rw [← inv_pow, ← conj_pow, hxr']
    calc r ^ j * x * (r ^ j)⁻¹ = r ^ j * (x * (r ^ j)⁻¹ * x⁻¹) * x := by group
      _ = r ^ j * r ^ j * x := by rw [h2]
      _ = r ^ (2 * j) * x := by rw [← pow_add, two_mul]
  have hr : r ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one r
  have hv' : v = r⁻¹ * x := by
    calc v = x⁻¹ * r := by rw [hrdef]; group
      _ = (x * r * x⁻¹) * x := by rw [mul_assoc (x * r) x⁻¹ x, inv_mul_cancel, mul_one, hxinv]
      _ = r⁻¹ * x := by rw [hxr]
  refine isConj_iff.mpr ⟨r ^ k, ?_⟩
  rw [h1, hv']
  calc r ^ (2 * k) * x = r ^ (2 * k + 1) * r⁻¹ * x := by rw [pow_succ]; group
    _ = r⁻¹ * x := by rw [hr, one_mul]

theorem eq_pow_half [Finite G] {c y : G} (hy : y ∈ zpowers c) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    Even (orderOf c) ∧ y = c ^ (orderOf c / 2) := by
  have hfin : IsOfFinOrder c := isOfFinOrder_of_finite c
  obtain ⟨k, hk, rfl⟩ : ∃ k < orderOf c, c ^ k = y := by
    obtain ⟨m, rfl⟩ := hy
    refine ⟨(m % (orderOf c : ℤ)).toNat, ?_, ?_⟩
    · have h0 : (0 : ℤ) < orderOf c := by exact_mod_cast hfin.orderOf_pos
      have := Int.emod_lt_of_pos m h0
      have h1 := Int.emod_nonneg m h0.ne'
      omega
    · have h0 : (0 : ℤ) < orderOf c := by exact_mod_cast hfin.orderOf_pos
      have h1 := Int.emod_nonneg m h0.ne'
      change c ^ (m % (orderOf c : ℤ)).toNat = c ^ m
      rw [← zpow_natCast, Int.toNat_of_nonneg h1, zpow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hy1 (pow_zero c)
  have hdvd : orderOf c ∣ 2 * k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [two_mul, pow_add, hyy]
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : m = 1 := by
    rcases m with _ | _ | m
    · omega
    · rfl
    · nlinarith
  subst hm1
  refine ⟨⟨k, by omega⟩, ?_⟩
  congr 1
  omega

theorem card_eq_thompson [Finite G] {z w : G} (hzz : z * z = 1) (hz1 : z ≠ 1) (hww : w * w = 1)
    (hw1 : w ≠ 1) (hinv : ∀ y : G, y * y = 1 → y ≠ 1 → IsConj z y ∨ IsConj w y)
    (hzw : ¬ IsConj z w) :
    Nat.card G = thompsonCount z w z * Nat.card (centralizer ({w} : Set G)) +
      thompsonCount z w w * Nat.card (centralizer ({z} : Set G)) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set Df := Finset.univ.filter fun x : G => IsConj z x
  set Wf := Finset.univ.filter fun x : G => IsConj w x
  set Pf := Df ×ˢ Wf
  set Nf : G → Finset (G × G) := fun y => Pf.filter fun p => y ∈ zpowers (p.1 * p.2)
  set F : G × G → G := fun p => (p.1 * p.2) ^ (orderOf (p.1 * p.2) / 2)
  have hinvz : ∀ x, IsConj z x → x * x = 1 ∧ x ≠ 1 := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    refine ⟨by rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hzz]; group,
      fun h => hz1 ?_⟩
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hinvw : ∀ x, IsConj w x → x * x = 1 ∧ x ≠ 1 := by
    intro x hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    refine ⟨by rw [show g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ by group, hww]; group,
      fun h => hw1 ?_⟩
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hF : ∀ p ∈ Pf, F p * F p = 1 ∧ F p ≠ 1 ∧ F p ∈ zpowers (p.1 * p.2) ∧
      ∀ y, y ∈ zpowers (p.1 * p.2) → y * y = 1 → y ≠ 1 → y = F p := by
    intro p hp
    simp only [Pf, Df, Wf, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    have heven : Even (orderOf (p.1 * p.2)) := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      exact hzw (hp.1.trans ((isConj_of_odd (hinvz _ hp.1).1 (hinvw _ hp.2).1 hodd).trans
        hp.2.symm))
    obtain ⟨j, hj⟩ := heven
    have hpos : 0 < orderOf (p.1 * p.2) := (isOfFinOrder_of_finite _).orderOf_pos
    have hhalf : orderOf (p.1 * p.2) / 2 = j := by omega
    refine ⟨?_, ?_, ⟨(orderOf (p.1 * p.2) / 2 : ℕ), zpow_natCast _ _⟩, ?_⟩
    · simp only [F]
      rw [← pow_add, hhalf, ← hj, pow_orderOf_eq_one]
    · simp only [F]
      rw [hhalf]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    · intro y hy hyy hy1
      exact (eq_pow_half hy hyy hy1).2
  have hFmem : ∀ p ∈ Pf, F p ∈ Df ∪ Wf := by
    intro p hp
    obtain ⟨h1, h2, -, -⟩ := hF p hp
    rcases hinv _ h1 h2 with h | h
    · exact Finset.mem_union_left _ (by simpa [Df] using h)
    · exact Finset.mem_union_right _ (by simpa [Wf] using h)
  have hfib : ∀ y ∈ Df ∪ Wf, Pf.filter (fun p => F p = y) = Nf y := by
    intro y hy
    have hyi : y * y = 1 ∧ y ≠ 1 := by
      rcases Finset.mem_union.mp hy with h | h
      · exact hinvz y (by simpa [Df] using h)
      · exact hinvw y (by simpa [Wf] using h)
    ext p
    simp only [Nf, Finset.mem_filter]
    constructor
    · rintro ⟨hp, rfl⟩
      exact ⟨hp, (hF p hp).2.2.1⟩
    · rintro ⟨hp, hyp⟩
      exact ⟨hp, ((hF p hp).2.2.2 y hyp hyi.1 hyi.2).symm⟩
  have hsum : Pf.card = ∑ y ∈ Df ∪ Wf, (Nf y).card := by
    rw [Finset.card_eq_sum_card_fiberwise hFmem]
    exact Finset.sum_congr rfl fun y hy => by rw [hfib y hy]
  have hconjN : ∀ g y : G, (Nf (g * y * g⁻¹)).card = (Nf y).card := by
    intro g y
    refine Finset.card_bij' (fun p _ => (g⁻¹ * p.1 * g, g⁻¹ * p.2 * g))
      (fun p _ => (g * p.1 * g⁻¹, g * p.2 * g⁻¹)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Nf, Pf, Df, Wf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp ⊢
      refine ⟨⟨hp.1.1.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩),
        hp.1.2.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)⟩, ?_⟩
      obtain ⟨k, hk⟩ := hp.2
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      rw [show g⁻¹ * p.1 * g * (g⁻¹ * p.2 * g) = g⁻¹ * (p.1 * p.2) * g⁻¹⁻¹ by group, conj_zpow,
        hk]
      group
    · intro p hp
      simp only [Nf, Pf, Df, Wf, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hp ⊢
      refine ⟨⟨hp.1.1.trans (isConj_iff.mpr ⟨g, rfl⟩), hp.1.2.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩,
        ?_⟩
      obtain ⟨k, hk⟩ := hp.2
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      rw [show g * p.1 * g⁻¹ * (g * p.2 * g⁻¹) = g * (p.1 * p.2) * g⁻¹ by group, conj_zpow, hk]
    · intro p _
      simp only
      ext <;> simp only <;> group
    · intro p _
      simp only
      ext <;> simp only <;> group
  have hsumD : ∑ y ∈ Df, (Nf y).card = Df.card * (Nf z).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨g, rfl⟩ := isConj_iff.mp (by simpa [Df] using hy)
    exact hconjN g z
  have hsumW : ∑ y ∈ Wf, (Nf y).card = Wf.card * (Nf w).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨g, rfl⟩ := isConj_iff.mp (by simpa [Wf] using hy)
    exact hconjN g w
  have hdisj : Disjoint Df Wf := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Df, Wf, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hzw (hx.trans hx'.symm)
  have hmain : Df.card * Wf.card = Df.card * (Nf z).card + Wf.card * (Nf w).card := by
    rw [← Finset.card_product, ← hsumD, ← hsumW, ← Finset.sum_union hdisj]
    exact hsum
  have hD : {x | IsConj z x}.ncard = Df.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [Df]
  have hW : {x | IsConj w x}.ncard = Wf.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [Wf]
  have hN : ∀ y, thompsonCount z w y = (Nf y).card := by
    intro y
    rw [thompsonCount, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp [Nf, Pf, Df, Wf, and_assoc]
  have hcz := ncard_conj_mul_card_centralizer z
  have hcw := ncard_conj_mul_card_centralizer w
  rw [hD] at hcz
  rw [hW] at hcw
  rw [hN, hN]
  have hG : 0 < Nat.card G := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hG
  calc Nat.card G * Nat.card G =
      (Df.card * Nat.card (centralizer ({z} : Set G))) *
        (Wf.card * Nat.card (centralizer ({w} : Set G))) := by rw [hcz, hcw]
    _ = (Df.card * Wf.card) * (Nat.card (centralizer ({z} : Set G)) *
        Nat.card (centralizer ({w} : Set G))) := by ring
    _ = (Df.card * (Nf z).card + Wf.card * (Nf w).card) *
        (Nat.card (centralizer ({z} : Set G)) * Nat.card (centralizer ({w} : Set G))) := by
        rw [hmain]
    _ = (Df.card * Nat.card (centralizer ({z} : Set G))) *
          ((Nf z).card * Nat.card (centralizer ({w} : Set G))) +
        (Wf.card * Nat.card (centralizer ({w} : Set G))) *
          ((Nf w).card * Nat.card (centralizer ({z} : Set G))) := by ring
    _ = Nat.card G * ((Nf z).card * Nat.card (centralizer ({w} : Set G)) +
        (Nf w).card * Nat.card (centralizer ({z} : Set G))) := by
        rw [hcz, hcw]
        ring

end CFSG.LargeExtraspecial.AS35QTS

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.GH74.Uniqueness.Section15Last

open Subgroup

variable {X : Type} [Group X]

structure FinalHyp (M V R₀ Mo D K : Subgroup X) (u : X) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  Mo_le : Mo ≤ R₀
  R₀_le : R₀ ≤ V
  V_le : V ≤ M
  D_le : D ≤ M
  K_le : K ≤ D
  V_norm : ∀ g ∈ M, ∀ x ∈ V, g * x * g⁻¹ ∈ V
  R₀_norm : ∀ g ∈ M, ∀ x ∈ R₀, g * x * g⁻¹ ∈ R₀
  Mo_norm : ∀ g ∈ M, ∀ x ∈ Mo, g * x * g⁻¹ ∈ Mo
  K_norm : ∀ d ∈ D, ∀ k ∈ K, d * k * d⁻¹ ∈ K
  card_Mo : Nat.card Mo = 2 ^ n
  card_R₀ : Nat.card R₀ = 2 ^ (2 * n)
  card_V : Nat.card V = 2 ^ (2 * n + 1)
  card_K : Nat.card K = 2 ^ n - 1
  card_M : Nat.card M = 2 ^ (3 * n) * Nat.card D
  Mo_sq : ∀ x ∈ Mo, x * x = 1
  R₀_comm : ∀ a ∈ R₀, ∀ b ∈ R₀, a * b = b * a
  R₀_sq : ∀ x ∈ R₀, x * x ∈ Mo
  R₀_sq_ne : ∀ x ∈ R₀, x ∉ Mo → x * x ≠ 1
  u_mem : u ∈ V
  u_not_mem : u ∉ R₀
  u_sq : u * u = 1
  u_inv : ∀ x ∈ R₀, u * x * u⁻¹ = x⁻¹
  V_conj : ∀ x ∈ V, x ∉ R₀ → ∃ g ∈ M, g * u * g⁻¹ = x
  K_comm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a
  K_trans : ∀ a ∈ Mo, a ≠ 1 → ∀ b ∈ Mo, b ≠ 1 → ∃ k ∈ K, k * a * k⁻¹ = b
  K_fpf : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ Mo, k * x = x * k → x = 1
  D_u : ∀ d ∈ D, d * u = u * d
  D_V : ∀ d ∈ D, d ∈ V → d = 1 ∨ d = u
  C_Mo : ∀ g ∈ M, (∀ x ∈ Mo, g * x = x * g) → g ∈ V
  V_max : ∀ N : Subgroup X, N ≤ M → (∀ g ∈ M, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → IsPGroup 2 N → N ≤ V
  oddGen : closure {y : X | y ∈ M ∧ Odd (orderOf y)} = M

theorem inv_mul_mem_of_index_two {G : Type*} [Group G] {H : Subgroup G} (hH : H.index = 2)
    {a b : G} (ha : a ∉ H) (hb : b ∉ H) : a⁻¹ * b ∈ H :=
  (Subgroup.mul_mem_iff_of_index_two hH).mpr (iff_of_false (fun h' => ha (inv_mem_iff.mp h')) hb)

namespace FinalHyp

variable {M V R₀ Mo D K : Subgroup X} {u : X} {n : ℕ}

theorem Mo_le_M (h : FinalHyp M V R₀ Mo D K u n) : Mo ≤ M :=
  h.Mo_le.trans (h.R₀_le.trans h.V_le)

theorem R₀_le_M (h : FinalHyp M V R₀ Mo D K u n) : R₀ ≤ M := h.R₀_le.trans h.V_le

theorem u_inv_eq (h : FinalHyp M V R₀ Mo D K u n) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right h.u_sq

theorem u_mem_M (h : FinalHyp M V R₀ Mo D K u n) : u ∈ M := h.V_le h.u_mem

theorem index_V (h : FinalHyp M V R₀ Mo D K u n) : (R₀.subgroupOf V).index = 2 := by
  have h1 := Subgroup.card_mul_index (R₀.subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R₀_le).toEquiv, h.card_R₀, h.card_V] at h1
  have hpos : 0 < 2 ^ (2 * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, pow_succ]

theorem u_mul_mem (h : FinalHyp M V R₀ Mo D K u n) {x : X} (hx : x ∈ V) (hx' : x ∉ R₀) :
    u * x ∈ R₀ := by
  have h1 := inv_mul_mem_of_index_two h.index_V (a := (⟨u, h.u_mem⟩ : V)) (b := ⟨x, hx⟩)
    (fun hu => h.u_not_mem hu) (fun hx'' => hx' hx'')
  have h2 : u⁻¹ * x ∈ R₀ := h1
  rwa [h.u_inv_eq] at h2

theorem conj_u_mem (h : FinalHyp M V R₀ Mo D K u n) {g : X} (hg : g ∈ M) :
    g * u * g⁻¹ ∈ V ∧ g * u * g⁻¹ ∉ R₀ := by
  refine ⟨h.V_norm g hg u h.u_mem, fun hR => h.u_not_mem ?_⟩
  have h1 := h.R₀_norm g⁻¹ (M.inv_mem hg) _ hR
  have h2 : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
  rwa [h2] at h1

theorem cc_mem (h : FinalHyp M V R₀ Mo D K u n) {g : X} (hg : g ∈ M) :
    u * (g * u * g⁻¹) ∈ R₀ :=
  h.u_mul_mem (h.conj_u_mem hg).1 (h.conj_u_mem hg).2

theorem Mo_comm (h : FinalHyp M V R₀ Mo D K u n) {a b : X} (ha : a ∈ Mo) (hb : b ∈ Mo) :
    a * b = b * a := by
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (h.Mo_sq _ (Mo.mul_mem ha hb))
  have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.Mo_sq a ha)
  have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h.Mo_sq b hb)
  rw [mul_inv_rev, h2, h3] at h1
  exact h1.symm

theorem u_comm_Mo (h : FinalHyp M V R₀ Mo D K u n) {y : X} (hy : y ∈ Mo) : u * y = y * u := by
  have h1 := h.u_inv y (h.Mo_le hy)
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.Mo_sq y hy)
  rw [h2, h.u_inv_eq] at h1
  calc u * y = (u * y * u) * u := by rw [mul_assoc, h.u_sq, mul_one]
    _ = y * u := by rw [h1]

theorem V_comm_Mo (h : FinalHyp M V R₀ Mo D K u n) {v : X} (hv : v ∈ V) {y : X} (hy : y ∈ Mo) :
    v * y = y * v := by
  by_cases hvR : v ∈ R₀
  · exact h.R₀_comm v hvR y (h.Mo_le hy)
  · have hr : u * v ∈ R₀ := h.u_mul_mem hv hvR
    have hv' : v = u * (u * v) := by rw [← mul_assoc, h.u_sq, one_mul]
    have hr' : (u * v) * y = y * (u * v) := h.R₀_comm _ hr y (h.Mo_le hy)
    calc v * y = u * ((u * v) * y) := by
          conv_lhs => rw [hv']
          rw [mul_assoc]
      _ = u * (y * (u * v)) := by rw [hr']
      _ = (u * y) * (u * v) := by rw [mul_assoc]
      _ = (y * u) * (u * v) := by rw [h.u_comm_Mo hy]
      _ = y * v := by rw [mul_assoc, ← mul_assoc u u v, h.u_sq, one_mul]

@[expose] def sqHom (h : FinalHyp M V R₀ Mo D K u n) : ↥R₀ →* ↥Mo where
  toFun r := ⟨(r : X) * r, h.R₀_sq r r.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change (a : X) * b * ((a : X) * b) = ((a : X) * a) * ((b : X) * b)
    calc (a : X) * b * ((a : X) * b) = (a : X) * ((b : X) * a) * b := by group
      _ = (a : X) * ((a : X) * b) * b := by rw [h.R₀_comm b b.2 a a.2]
      _ = ((a : X) * a) * ((b : X) * b) := by group)

theorem sqHom_surjective (h : FinalHyp M V R₀ Mo D K u n) : Function.Surjective h.sqHom := by
  have hker : h.sqHom.ker = Mo.subgroupOf R₀ := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hr
      by_contra hrM
      have hr' : (r : X) * r = 1 := congrArg Subtype.val hr
      exact h.R₀_sq_ne r r.2 hrM hr'
    · intro hr
      exact Subtype.ext (h.Mo_sq r hr)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup h.sqHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange h.sqHom).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Mo_le).toEquiv, h.card_R₀, h.card_Mo] at h1
  have hpos : 0 < 2 ^ n := by positivity
  have h2 : Nat.card h.sqHom.range = 2 ^ n := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← h1, two_mul, pow_add]
  have hfin : Finite ↥Mo := Nat.finite_of_card_ne_zero (by rw [h.card_Mo]; positivity)
  have h3 : h.sqHom.range = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [h2, h.card_Mo])
  exact MonoidHom.range_eq_top.mp h3

theorem exists_sq_eq (h : FinalHyp M V R₀ Mo D K u n) {y : X} (hy : y ∈ Mo) :
    ∃ r ∈ R₀, r * r = y := by
  obtain ⟨r, hr⟩ := h.sqHom_surjective ⟨y, hy⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

end FinalHyp

@[expose] def cc (u g : X) : X := u * (g * u * g⁻¹)

@[expose] def tt (u g : X) : X := cc u g * cc u g

theorem cc_one {u : X} (hu : u * u = 1) : cc u 1 = 1 := by
  simp [cc, hu]

theorem tt_one {u : X} (hu : u * u = 1) : tt u 1 = 1 := by
  simp [tt, cc_one hu]

theorem cc_mul {u : X} (hu : u * u = 1) (g h : X) :
    cc u (g * h) = cc u g * (g * cc u h * g⁻¹) := by
  unfold cc
  calc u * (g * h * u * (g * h)⁻¹)
      = u * (g * (u * u) * (h * u * h⁻¹) * g⁻¹) := by rw [hu]; group
    _ = u * (g * u * g⁻¹) * (g * (u * (h * u * h⁻¹)) * g⁻¹) := by group

namespace FinalHyp

variable {M V R₀ Mo D K : Subgroup X} {u : X} {n : ℕ}

theorem cc_mem_R₀ (h : FinalHyp M V R₀ Mo D K u n) {g : X} (hg : g ∈ M) : cc u g ∈ R₀ :=
  h.cc_mem hg

theorem tt_mem (h : FinalHyp M V R₀ Mo D K u n) {g : X} (hg : g ∈ M) : tt u g ∈ Mo :=
  h.R₀_sq _ (h.cc_mem_R₀ hg)

theorem tt_mul (h : FinalHyp M V R₀ Mo D K u n) {g k : X} (hg : g ∈ M) (hk : k ∈ M) :
    tt u (g * k) = tt u g * (g * tt u k * g⁻¹) := by
  have hc : cc u (g * k) = cc u g * (g * cc u k * g⁻¹) := cc_mul h.u_sq g k
  have ha : cc u g ∈ R₀ := h.cc_mem_R₀ hg
  have hb : g * cc u k * g⁻¹ ∈ R₀ := h.R₀_norm g hg _ (h.cc_mem_R₀ hk)
  have hab : cc u g * (g * cc u k * g⁻¹) = (g * cc u k * g⁻¹) * cc u g :=
    h.R₀_comm _ ha _ hb
  unfold tt
  rw [hc]
  calc cc u g * (g * cc u k * g⁻¹) * (cc u g * (g * cc u k * g⁻¹))
      = cc u g * ((g * cc u k * g⁻¹) * cc u g) * (g * cc u k * g⁻¹) := by group
    _ = cc u g * (cc u g * (g * cc u k * g⁻¹)) * (g * cc u k * g⁻¹) := by rw [hab]
    _ = (cc u g * cc u g) * (g * (cc u k * cc u k) * g⁻¹) := by group

theorem cc_eq_of_R₀ (h : FinalHyp M V R₀ Mo D K u n) {r : X} (hr : r ∈ R₀) :
    cc u r = (r * r)⁻¹ := by
  have h1 : u * r⁻¹ * u⁻¹ = r := by
    have := h.u_inv r⁻¹ (R₀.inv_mem hr)
    rwa [inv_inv] at this
  have h2 : r * u = u * r⁻¹ := (mul_inv_eq_iff_eq_mul.mp h1).symm
  unfold cc
  calc u * (r * u * r⁻¹) = u * (u * r⁻¹ * r⁻¹) := by rw [h2]
    _ = (u * u) * r⁻¹ * r⁻¹ := by group
    _ = r⁻¹ * r⁻¹ := by rw [h.u_sq, one_mul]
    _ = (r * r)⁻¹ := by group

theorem tt_R₀ (h : FinalHyp M V R₀ Mo D K u n) {r : X} (hr : r ∈ R₀) : tt u r = 1 := by
  unfold tt
  rw [h.cc_eq_of_R₀ hr, ← mul_inv_rev, h.Mo_sq _ (h.R₀_sq r hr), inv_one]

theorem tt_u (h : FinalHyp M V R₀ Mo D K u n) : tt u u = 1 := by
  simp [tt, cc, h.u_sq]

theorem tt_V (h : FinalHyp M V R₀ Mo D K u n) {v : X} (hv : v ∈ V) : tt u v = 1 := by
  by_cases hvR : v ∈ R₀
  · exact h.tt_R₀ hvR
  · have hr : u * v ∈ R₀ := h.u_mul_mem hv hvR
    have hv' : v = u * (u * v) := by rw [← mul_assoc, h.u_sq, one_mul]
    rw [hv', h.tt_mul h.u_mem_M (h.R₀_le_M hr), h.tt_u, h.tt_R₀ hr]
    simp

theorem cc_D (h : FinalHyp M V R₀ Mo D K u n) {d : X} (hd : d ∈ D) : cc u d = 1 := by
  have h1 : d * u * d⁻¹ = u := by rw [h.D_u d hd]; group
  unfold cc
  rw [h1, h.u_sq]

theorem tt_D (h : FinalHyp M V R₀ Mo D K u n) {d : X} (hd : d ∈ D) : tt u d = 1 := by
  unfold tt
  rw [h.cc_D hd, one_mul]

end FinalHyp

end CFSG.GH74.Uniqueness.Section15Last

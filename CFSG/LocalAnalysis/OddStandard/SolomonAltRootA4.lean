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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.OddStandard.SolomonAlt

open Equiv Equiv.Perm Subgroup Function

variable {α : Type*}

theorem apply_apply_of_mul_self {t : Perm α} (ht : t * t = 1) (a : α) : t (t a) = a := by
  simpa using congrArg (fun f : Perm α => f a) ht

theorem apply_comm_of_mem_centralizer {t σ : Perm α} (hσ : σ ∈ centralizer {t}) (a : α) :
    t (σ a) = σ (t a) :=
  (congrArg (fun f : Perm α => f a) (mem_centralizer_singleton_iff.1 hσ)).symm

section

variable [DecidableEq α]

theorem swap_mem_centralizer {t : Perm α} (ht : t * t = 1) (a : α) :
    swap a (t a) ∈ centralizer {t} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht x
  split_ifs <;> grind

theorem conj_swap_of_mem_centralizer {t σ : Perm α} (hσ : σ ∈ centralizer {t}) (a : α) :
    σ * swap a (t a) * σ⁻¹ = swap (σ a) (t (σ a)) := by
  rw [apply_comm_of_mem_centralizer hσ, ← swap_apply_apply]

def exchange (t : Perm α) (a b : α) : Perm α := swap a b * swap (t a) (t b)

theorem exchange_mem_centralizer {t : Perm α} (ht : t * t = 1) {a b : α} (ha : t a ≠ a)
    (hb : t b ≠ b) (hba : b ≠ a) (hbta : b ≠ t a) : exchange t a b ∈ centralizer {t} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  have h3 := apply_apply_of_mul_self ht x
  simp only [exchange, Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem exchange_apply_left {t : Perm α} (ht : t * t = 1) {a b : α} (ha : t a ≠ a)
    (hb : t b ≠ b) (hbta : b ≠ t a) : exchange t a b a = b := by
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  simp only [exchange, Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem exchange_apply_of_notMem {t : Perm α} {a b x : α}
    (hxa : x ≠ a) (hxta : x ≠ t a) (hxb : x ≠ b) (hxtb : x ≠ t b) : exchange t a b x = x := by
  simp only [exchange, Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem pair_mul_self {t : Perm α} (ht : t * t = 1) {p q : α} (hqp : q ≠ p) (hqtp : q ≠ t p)
    (hp : t p ≠ p) (hq : t q ≠ q) :
    (swap p (t p) * swap q (t q)) * (swap p (t p) * swap q (t q)) = 1 := by
  ext x
  have h1 := apply_apply_of_mul_self ht p
  have h2 := apply_apply_of_mul_self ht q
  have h3 := apply_apply_of_mul_self ht x
  simp only [Perm.mul_apply, Equiv.swap_apply_def, Perm.one_apply]
  split_ifs <;> grind

theorem pair_apply_left {t : Perm α} (ht : t * t = 1) {p q : α} (hqp : q ≠ p) (hqtp : q ≠ t p) :
    (swap p (t p) * swap q (t q)) p = t p := by
  have h1 := apply_apply_of_mul_self ht p
  have h2 := apply_apply_of_mul_self ht q
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem pair_apply_right {t : Perm α} (ht : t * t = 1) {p q : α} (hqp : q ≠ p) (hqtp : q ≠ t p) :
    (swap p (t p) * swap q (t q)) q = t q := by
  have h1 := apply_apply_of_mul_self ht p
  have h2 := apply_apply_of_mul_self ht q
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

theorem pair_apply_of_notMem {t : Perm α} (ht : t * t = 1) {p q x : α}
    (hxp : x ≠ p) (hxtp : x ≠ t p) (hxq : x ≠ q) (hxtq : x ≠ t q) :
    (swap p (t p) * swap q (t q)) x = x := by
  have h1 := apply_apply_of_mul_self ht p
  have h2 := apply_apply_of_mul_self ht q
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> grind

omit [DecidableEq α] in
theorem card_involutions_le_three {X : Subgroup (Perm α)} (e : X ≃* alternatingGroup (Fin 4))
    (s : Finset (Perm α)) (hs : ∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) : s.card ≤ 3 := by
  classical
  let T : Finset (alternatingGroup (Fin 4)) :=
    Finset.univ.filter (fun g => g ≠ 1 ∧ g * g = 1)
  have hT : T.card = 3 := by decide
  let s' : Finset X := s.subtype (· ∈ X)
  have hs' : s'.card = s.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun y hy => (hs y hy).1
  rw [← hs', ← hT]
  refine Finset.card_le_card_of_injOn e ?_ e.injective.injOn
  intro x hx
  obtain ⟨-, hx1, hx2⟩ := hs x (Finset.mem_subtype.1 hx)
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, T, Set.mem_ofPred_eq]
  refine ⟨fun h => hx1 ?_, ?_⟩
  · have := e.injective (h.trans (map_one e).symm)
    rw [this]
    rfl
  · rw [← map_mul]
    have : x * x = 1 := Subtype.ext hx2
    rw [this, map_one]

theorem false_of_pair_mem {t : Perm α} (ht : t * t = 1) {X : Subgroup (Perm α)}
    (hn : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    {a b c d : α} (ha : t a ≠ a) (hb : t b ≠ b) (hc : t c ≠ c) (hd : t d ≠ d)
    (hba : b ≠ a) (hbta : b ≠ t a)
    (hc1 : c ∉ ({a, t a, b, t b} : Finset α))
    (hd1 : d ∉ ({a, t a, b, t b, c, t c} : Finset α))
    (hy : swap a (t a) * swap b (t b) ∈ X) : False := by
  classical
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc1 hd1
  have key : ∀ σ ∈ centralizer {t}, ∀ p q : α,
      swap p (t p) * swap q (t q) ∈ X →
      swap (σ p) (t (σ p)) * swap (σ q) (t (σ q)) ∈ X := by
    intro σ hσ p q hpq
    have h := hn σ hσ _ hpq
    have e : σ * (swap p (t p) * swap q (t q)) * σ⁻¹ =
        (σ * swap p (t p) * σ⁻¹) * (σ * swap q (t q) * σ⁻¹) := by group
    rw [e, conj_swap_of_mem_centralizer hσ, conj_swap_of_mem_centralizer hσ] at h
    exact h
  have h1 := apply_apply_of_mul_self ht a
  have h2 := apply_apply_of_mul_self ht b
  have h3' := apply_apply_of_mul_self ht c
  have h4 := apply_apply_of_mul_self ht d
  have hy2 : swap a (t a) * swap c (t c) ∈ X := by
    have σmem := exchange_mem_centralizer ht hb hc (by grind) (by grind)
    have := key _ σmem a b hy
    rwa [exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind),
      exchange_apply_left ht hb hc (by grind)] at this
  have hy3 : swap a (t a) * swap d (t d) ∈ X := by
    have σmem := exchange_mem_centralizer ht hb hd (by grind) (by grind)
    have := key _ σmem a b hy
    rwa [exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind),
      exchange_apply_left ht hb hd (by grind)] at this
  have hy4 : swap b (t b) * swap c (t c) ∈ X := by
    have σmem := exchange_mem_centralizer ht ha hb hba hbta
    have := key _ σmem a c hy2
    rwa [exchange_apply_left ht ha hb hbta,
      exchange_apply_of_notMem (by grind) (by grind) (by grind) (by grind)] at this
  have hd12 : swap a (t a) * swap b (t b) ≠ swap a (t a) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f b) h
    rw [pair_apply_right ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact hb this
  have hd13 : swap a (t a) * swap b (t b) ≠ swap a (t a) * swap d (t d) := by
    intro h
    have := congrArg (fun f : Perm α => f b) h
    rw [pair_apply_right ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact hb this
  have hd14 : swap a (t a) * swap b (t b) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht hba hbta, pair_apply_of_notMem ht (by grind) (by grind) (by grind)
      (by grind)] at this
    exact ha this
  have hd23 : swap a (t a) * swap c (t c) ≠ swap a (t a) * swap d (t d) := by
    intro h
    have := congrArg (fun f : Perm α => f c) h
    rw [pair_apply_right ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact hc this
  have hd24 : swap a (t a) * swap c (t c) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact ha this
  have hd34 : swap a (t a) * swap d (t d) ≠ swap b (t b) * swap c (t c) := by
    intro h
    have := congrArg (fun f : Perm α => f a) h
    rw [pair_apply_left ht (by grind) (by grind), pair_apply_of_notMem ht (by grind) (by grind)
      (by grind) (by grind)] at this
    exact ha this
  have hcard : ({swap a (t a) * swap b (t b), swap a (t a) * swap c (t c),
      swap a (t a) * swap d (t d), swap b (t b) * swap c (t c)} : Finset (Perm α)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hd34]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd23, hd24⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd12, hd13, hd14⟩
  have hle := h3 {swap a (t a) * swap b (t b), swap a (t a) * swap c (t c),
      swap a (t a) * swap d (t d), swap b (t b) * swap c (t c)} (by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · refine ⟨hy, fun h => ha ?_, pair_mul_self ht hba hbta ha hb⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht hba hbta] using this
    · refine ⟨hy2, fun h => ha ?_, pair_mul_self ht (by grind) (by grind) ha hc⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht (by grind : c ≠ a) (by grind : c ≠ t a)] using this
    · refine ⟨hy3, fun h => ha ?_, pair_mul_self ht (by grind) (by grind) ha hd⟩
      have := congrArg (fun f : Perm α => f a) h
      simpa [pair_apply_left ht (by grind : d ≠ a) (by grind : d ≠ t a)] using this
    · refine ⟨hy4, fun h => hb ?_, pair_mul_self ht (by grind) (by grind) hb hc⟩
      have := congrArg (fun f : Perm α => f b) h
      simpa [pair_apply_left ht (by grind : c ≠ b) (by grind : c ≠ t b)] using this)
  omega

omit [DecidableEq α] in
theorem exists_two_more [Fintype α] [DecidableEq α] {t : Perm α} (h8 : 8 ≤ t.support.card)
    (a b : α) :
    ∃ c d : α, t c ≠ c ∧ t d ≠ d ∧ c ∉ ({a, t a, b, t b} : Finset α) ∧
      d ∉ ({a, t a, b, t b, c, t c} : Finset α) := by
  have h1 : ({a, t a, b, t b} : Finset α).card < t.support.card :=
    lt_of_le_of_lt Finset.card_le_four (by omega)
  obtain ⟨c, hc, hc1⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  have h2 : ({a, t a, b, t b, c, t c} : Finset α).card < t.support.card :=
    lt_of_le_of_lt Finset.card_le_six (by omega)
  obtain ⟨d, hd, hd1⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
  exact ⟨c, d, Perm.mem_support.1 hc, Perm.mem_support.1 hd, hc1, hd1⟩

variable [Fintype α]

theorem apply_eq_or_eq_apply {t : Perm α} (ht : t * t = 1) (h8 : 8 ≤ t.support.card)
    {X : Subgroup (Perm α)} (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    {x : Perm α} (hx : x ∈ X) {a : α} (ha : t a ≠ a) : x a = a ∨ x a = t a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hxa, hxta⟩ := hcon
  have hxC : x ∈ centralizer {t} := hX hx
  have hb : t (x a) ≠ x a := by
    rw [apply_comm_of_mem_centralizer hxC]
    intro h
    exact ha (x.injective h)
  have hcA : swap a (t a) ∈ centralizer {t} := swap_mem_centralizer ht a
  have hy : swap (x a) (t (x a)) * swap a (t a) ∈ X := by
    have h1 : x * (swap a (t a) * x⁻¹ * (swap a (t a))⁻¹) ∈ X := by
      refine X.mul_mem hx ?_
      exact hn _ hcA x⁻¹ (X.inv_mem hx)
    have e : x * (swap a (t a) * x⁻¹ * (swap a (t a))⁻¹) =
        (x * swap a (t a) * x⁻¹) * (swap a (t a))⁻¹ := by group
    rw [e, conj_swap_of_mem_centralizer hxC, swap_inv] at h1
    exact h1
  have h1 := apply_apply_of_mul_self ht (x a)
  have h2 := apply_comm_of_mem_centralizer hxC a
  obtain ⟨c, d, hc, hd, hc1, hd1⟩ := exists_two_more h8 (x a) a
  exact false_of_pair_mem ht hn h3 hb ha hc hd (Ne.symm hxa) (by grind) hc1 hd1 hy

def fixMoved (t : Perm α) : Subgroup (Perm α) where
  carrier := {σ | ∀ a, t a ≠ a → σ a = a}
  mul_mem' := by
    intro σ τ hσ hτ a ha
    simp [Perm.mul_apply, hτ a ha, hσ a ha]
  one_mem' := fun _ _ => rfl
  inv_mem' := by
    intro σ hσ a ha
    exact Perm.inv_eq_iff_eq.2 (hσ a ha).symm

omit [Fintype α] [DecidableEq α] in
theorem mem_fixMoved {t σ : Perm α} : σ ∈ fixMoved t ↔ ∀ a, t a ≠ a → σ a = a := Iff.rfl

@[expose] def restrictFixed (t : Perm α) : centralizer {t} →* Perm (Function.fixedPoints t) where
  toFun k := (k : Perm α).subtypePerm fun _ => by
    simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_ofPred_eq]
    rw [apply_comm_of_mem_centralizer k.2]
    exact (k : Perm α).injective.eq_iff
  map_one' := by ext; rfl
  map_mul' k l := (subtypePerm_mul _ _ _ _).symm

omit [Fintype α] in
theorem restrictFixed_surjective (t : Perm α) : Function.Surjective (restrictFixed t) := fun u =>
  ⟨⟨Perm.ofSubtype u, mem_centralizer_singleton_iff.2
    (disjoint_ofSubtype_of_memFixedPoints_self u).commute⟩, subtypePerm_ofSubtype u⟩

theorem apply_eq_of_pow_three {t : Perm α} (ht : t * t = 1) (h8 : 8 ≤ t.support.card)
    {X : Subgroup (Perm α)} (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    {x : Perm α} (hx : x ∈ X) (hx3 : x ^ 3 = 1) : x ∈ fixMoved t := by
  intro a ha
  rcases apply_eq_or_eq_apply ht h8 hX hn h3 hx ha with h | h
  · exact h
  · exfalso
    have hxC : x ∈ centralizer {t} := hX hx
    have h' : x (t a) = a := by
      rw [← apply_comm_of_mem_centralizer hxC, h, apply_apply_of_mul_self ht]
    have := congrArg (fun f : Perm α => f a) hx3
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, h, h', Perm.one_apply] at this
    exact ha (by simpa [h] using this)

theorem le_fixMoved_inf_alternating {t : Perm α} (ht : t * t = 1) (h8 : 8 ≤ t.support.card)
    {X : Subgroup (Perm α)} (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3)
    (e : X ≃* alternatingGroup (Fin 4)) : X ≤ fixMoved t ⊓ alternatingGroup α := by
  let φ : alternatingGroup (Fin 4) →* Perm α := X.subtype.comp e.symm.toMonoidHom
  have hφX : ∀ g, φ g ∈ X := fun g => (e.symm g).2
  have hφ3 : ∀ g : alternatingGroup (Fin 4), (g : Perm (Fin 4)).IsThreeCycle → φ g ^ 3 = 1 := by
    intro g hg
    have : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hg.orderOf]
      exact pow_orderOf_eq_one _
    rw [← map_pow, this, map_one]
  have hcl : Subgroup.closure
      {g : alternatingGroup (Fin 4) | (g : Perm (Fin 4)).IsThreeCycle} = ⊤ :=
    alternatingGroup.closure_isThreeCycles_eq_top
  have hfix : (fixMoved t).comap φ = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    intro g hg
    exact apply_eq_of_pow_three ht h8 hX hn h3 (hφX g) (hφ3 g hg)
  have halt : (alternatingGroup α).comap φ = ⊤ := by
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    intro g hg
    have h := hφ3 g hg
    have hs : sign (φ g) ^ 3 = 1 := by rw [← map_pow, h, map_one]
    show φ g ∈ alternatingGroup α
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign (φ g)) with h1 | h1
    · exact h1
    · rw [h1] at hs
      exact absurd hs (by decide)
  intro x hx
  have h1 := (Subgroup.eq_top_iff' _).1 hfix (e ⟨x, hx⟩)
  have h2 := (Subgroup.eq_top_iff' _).1 halt (e ⟨x, hx⟩)
  have hφx : φ (e ⟨x, hx⟩) = x := by simp [φ]
  refine ⟨?_, ?_⟩
  · simpa [hφx] using h1
  · simpa [hφx] using h2

theorem card_fixedPoints_and_eq {t : Perm α} (ht : t * t = 1) (h8 : 8 ≤ t.support.card)
    {X : Subgroup (Perm α)} (hX : X ≤ centralizer {t})
    (hn : ∀ c ∈ centralizer {t}, ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (e : X ≃* alternatingGroup (Fin 4)) :
    Nat.card (Function.fixedPoints t) = 4 ∧
      X = (alternatingGroup (Function.fixedPoints t)).map Perm.ofSubtype := by
  have h3 : ∀ s : Finset (Perm α), (∀ y ∈ s, y ∈ X ∧ y ≠ 1 ∧ y * y = 1) → s.card ≤ 3 :=
    fun s hs => card_involutions_le_three e s hs
  have hle := le_fixMoved_inf_alternating ht h8 hX hn h3 e
  let ψ : X →* Perm (Function.fixedPoints t) := (restrictFixed t).comp (Subgroup.inclusion hX)
  have hψ : ∀ (x : X) (a : Function.fixedPoints t),
      ((ψ x a : Function.fixedPoints t) : α) = (x : Perm α) a := fun _ _ => rfl
  have hxfix : ∀ x : X, ∀ a, t a ≠ a → (x : Perm α) a = a := fun x a ha => (hle x.2).1 a ha
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext a
    by_cases ha : t a = a
    · have := congrArg (fun f : Perm (Function.fixedPoints t) => (f ⟨a, ha⟩ : α)) hx
      simpa [hψ] using this
    · simp [hxfix x a ha]
  have hxeq : ∀ x : X, (x : Perm α) = Perm.ofSubtype (ψ x) := by
    intro x
    ext a
    by_cases ha : t a = a
    · rw [Perm.ofSubtype_apply_of_mem _ (show a ∈ Function.fixedPoints t from ha)]
      rfl
    · rw [Perm.ofSubtype_apply_of_not_mem _ (show a ∉ Function.fixedPoints t from ha),
        hxfix x a ha]
  set Y : Subgroup (Perm (Function.fixedPoints t)) := ψ.range with hY
  have hXcard : Nat.card X = 12 := by
    rw [Nat.card_congr e.toEquiv]
    have : Fintype.card (alternatingGroup (Fin 4)) = 12 := by decide
    rw [Nat.card_eq_fintype_card, this]
  have hYcard : Nat.card Y = 12 := by
    have h1 : Nat.card Y = Nat.card X :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    rw [h1, hXcard]
  have hYalt : Y ≤ alternatingGroup (Function.fixedPoints t) := by
    rintro _ ⟨x, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 : sign (Perm.ofSubtype (ψ x)) = sign (ψ x) := Perm.sign_ofSubtype _
    rw [← h1, ← hxeq x]
    exact Equiv.Perm.mem_alternatingGroup.1 (hle x.2).2
  have hYn : Y.Normal := by
    refine ⟨fun y hy τ => ?_⟩
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨c, hc⟩ := restrictFixed_surjective t τ
    refine ⟨⟨c * x * c⁻¹, hn _ c.2 _ x.2⟩, ?_⟩
    have : Subgroup.inclusion hX ⟨c * x * c⁻¹, hn _ c.2 _ x.2⟩ =
        c * Subgroup.inclusion hX x * c⁻¹ := Subtype.ext rfl
    simp only [ψ, MonoidHom.comp_apply, this, map_mul, map_inv, hc]
  have hm4 : Nat.card (Function.fixedPoints t) = 4 := by
    have hperm : Nat.card (Perm (Function.fixedPoints t)) =
        (Nat.card (Function.fixedPoints t)).factorial := Nat.card_perm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    ·
      have h1 : Nat.card Y ≤ Nat.card (Perm (Function.fixedPoints t)) :=
        Subgroup.card_le_card_group Y
      have h2 : (Nat.card (Function.fixedPoints t)).factorial ≤ (3 : ℕ).factorial :=
        Nat.factorial_le (by omega)
      have h3' : (3 : ℕ).factorial = 6 := rfl
      omega
    ·
      have h5 : 5 ≤ Nat.card (Function.fixedPoints t) := by omega
      have : Nontrivial (Function.fixedPoints t) :=
        Finite.one_lt_card_iff_nontrivial.1 (by omega)
      have hcard2 := two_mul_nat_card_alternatingGroup (α := Function.fixedPoints t)
      have h6 : (5 : ℕ).factorial ≤ (Nat.card (Function.fixedPoints t)).factorial :=
        Nat.factorial_le h5
      have h7 : (5 : ℕ).factorial = 120 := rfl
      have hN : (Y.subgroupOf (alternatingGroup (Function.fixedPoints t))).Normal :=
        hYn.subgroupOf _
      rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top h5
        (N := Y.subgroupOf (alternatingGroup (Function.fixedPoints t))) with h | h
      · have : Y = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          have : (⟨y, hYalt hy⟩ : alternatingGroup (Function.fixedPoints t)) ∈
              Y.subgroupOf (alternatingGroup (Function.fixedPoints t)) := hy
          rw [h, Subgroup.mem_bot] at this
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val this
        rw [this, Subgroup.card_bot] at hYcard
        omega
      · have hle2 : alternatingGroup (Function.fixedPoints t) ≤ Y := by
          intro g hg
          have : (⟨g, hg⟩ : alternatingGroup (Function.fixedPoints t)) ∈
              Y.subgroupOf (alternatingGroup (Function.fixedPoints t)) := by
            rw [h]
            exact Subgroup.mem_top _
          exact this
        have := Subgroup.card_le_of_le hle2
        omega
  refine ⟨hm4, ?_⟩
  have hAcard : Nat.card (alternatingGroup (Function.fixedPoints t)) = 12 := by
    have : Nontrivial (Function.fixedPoints t) :=
      Finite.one_lt_card_iff_nontrivial.1 (by omega)
    have hcard2 := two_mul_nat_card_alternatingGroup (α := Function.fixedPoints t)
    rw [Nat.card_perm, hm4] at hcard2
    have : (4 : ℕ).factorial = 24 := rfl
    omega
  have hYA : Y = alternatingGroup (Function.fixedPoints t) :=
    Subgroup.eq_of_le_of_card_ge hYalt (by omega)
  have hXle : X ≤ (alternatingGroup (Function.fixedPoints t)).map Perm.ofSubtype := by
    intro x hx
    refine ⟨ψ ⟨x, hx⟩, ?_, (hxeq ⟨x, hx⟩).symm⟩
    rw [← hYA]
    exact ⟨_, rfl⟩
  have hmapcard : Nat.card ((alternatingGroup (Function.fixedPoints t)).map Perm.ofSubtype) =
      12 := by
    rw [Subgroup.card_map_of_injective Perm.ofSubtype_injective, hAcard]
  exact Subgroup.eq_of_le_of_card_ge hXle (by omega)

theorem root_alt_four_of_normal_centralizer {t : Perm α} (ht : t * t = 1)
    (h8 : 8 ≤ t.support.card) {X : Subgroup (Perm α)} (hX : X ≤ centralizer {t})
    (hXn : (X.subgroupOf (centralizer {t})).Normal)
    (he : Nonempty (X ≃* alternatingGroup (Fin 4))) :
    Nat.card (Function.fixedPoints t) = 4 ∧
      X = (alternatingGroup (Function.fixedPoints t)).map Perm.ofSubtype := by
  obtain ⟨e⟩ := he
  refine card_fixedPoints_and_eq ht h8 hX ?_ e
  intro c hc x hx
  have hxC : x ∈ centralizer {t} := hX hx
  have := hXn.conj_mem ⟨x, hxC⟩ hx ⟨c, hc⟩
  exact this

end

end CFSG.OddStandard.SolomonAlt

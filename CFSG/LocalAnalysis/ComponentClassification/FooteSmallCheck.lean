module

public import CFSG.Sporadic.Schreier.Enumeration
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
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ComponentClassification.FooteSmall

open CFSG.Sporadic.Schreier

section OfList

variable {G : Type*} [Group G] [DecidableEq G]

@[expose] def closedCheck (L : List G) : Bool :=
  L.contains 1 && L.all (fun a => L.all fun b => L.contains (a * b)) &&
    L.all fun a => L.contains a⁻¹

@[expose] def ofList (L : List G) (h : closedCheck L = true) : Subgroup G where
  carrier := {g | g ∈ L}
  mul_mem' := by
    intro a b ha hb
    simp only [closedCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at h
    exact h.1.2 a ha b hb
  one_mem' := by
    simp only [closedCheck, Bool.and_eq_true, List.contains_iff_mem] at h
    exact h.1.1
  inv_mem' := by
    intro a ha
    simp only [closedCheck, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at h
    exact h.2 a ha

theorem mem_ofList (L : List G) (h : closedCheck L = true) (g : G) : g ∈ ofList L h ↔ g ∈ L :=
  Iff.rfl

theorem card_ofList (L : List G) (h : closedCheck L = true) (hL : L.Nodup) :
    Nat.card (ofList L h) = L.length :=
  card_eq_length (fun g => g ∈ ofList L h) id Function.injective_id L hL fun b => by
    simp [mem_ofList]

end OfList

section Search

variable {n : ℕ}

@[expose] def key (k : ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  Nat.fold k (fun i _ acc => acc * n + if h : i < n then (g ⟨i, h⟩).val else 0) 0

@[expose] def visit (k : ℕ) (C : List (Equiv.Perm (Fin n)))
    (st : Array Bool × List (Equiv.Perm (Fin n))) (x : Equiv.Perm (Fin n)) :
    Array Bool × List (Equiv.Perm (Fin n)) :=
  C.foldl (fun st c =>
    match st with
    | (seen, found) =>
      let i := key k (x * c)
      if seen[i]! then (seen, found) else (seen.set! i true, tab (x * c) :: found)) st

@[expose] def search (k : ℕ) (C : List (Equiv.Perm (Fin n))) :
    ℕ → Array Bool → List (Equiv.Perm (Fin n)) → List (Equiv.Perm (Fin n)) →
      List (Equiv.Perm (Fin n))
  | 0, _, _, acc => acc
  | fuel + 1, seen, frontier, acc =>
    match frontier.foldl (visit k C) (seen, []) with
    | (_, []) => acc
    | (seen', found) => search k C fuel seen' found (found ++ acc)

@[expose] def genCheck (k : ℕ) (C targets : List (Equiv.Perm (Fin n))) : Bool :=
  let L := search k C 64
    ((Array.replicate (n ^ k) false).set! (key k (1 : Equiv.Perm (Fin n))) true) [1] [1]
  targets.all fun g => L.contains g

variable {k : ℕ} {C : List (Equiv.Perm (Fin n))} {X : Subgroup (Equiv.Perm (Fin n))}

theorem visit_sound (hC : ∀ c ∈ C, c ∈ X) {x : Equiv.Perm (Fin n)} (hx : x ∈ X) :
    ∀ st : Array Bool × List (Equiv.Perm (Fin n)), (∀ y ∈ st.2, y ∈ X) →
      ∀ y ∈ (visit k C st x).2, y ∈ X := by
  unfold visit
  induction C with
  | nil => intro st hst; simpa using hst
  | cons c D ih =>
    intro st hst
    rw [List.foldl_cons]
    refine ih (fun d hd => hC d (List.mem_cons_of_mem c hd)) _ ?_
    obtain ⟨seen, found⟩ := st
    simp only
    split
    · exact hst
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [tab_eq]
        exact X.mul_mem hx (hC c List.mem_cons_self)
      · exact hst y hy

theorem foldl_visit_sound (hC : ∀ c ∈ C, c ∈ X) :
    ∀ F : List (Equiv.Perm (Fin n)), (∀ x ∈ F, x ∈ X) →
      ∀ st : Array Bool × List (Equiv.Perm (Fin n)), (∀ y ∈ st.2, y ∈ X) →
        ∀ y ∈ (F.foldl (visit k C) st).2, y ∈ X := by
  intro F
  induction F with
  | nil => intro _ st hst; simpa using hst
  | cons x F ih =>
    intro hF st hst
    rw [List.foldl_cons]
    exact ih (fun z hz => hF z (List.mem_cons_of_mem x hz)) _
      (visit_sound hC (hF x List.mem_cons_self) st hst)

theorem search_sound (hC : ∀ c ∈ C, c ∈ X) :
    ∀ (fuel : ℕ) (seen : Array Bool) (frontier acc : List (Equiv.Perm (Fin n))),
      (∀ y ∈ frontier, y ∈ X) → (∀ y ∈ acc, y ∈ X) → ∀ y ∈ search k C fuel seen frontier acc,
        y ∈ X := by
  intro fuel
  induction fuel with
  | zero => intro _ _ acc _ hacc; simpa [search] using hacc
  | succ fuel ih =>
    intro seen frontier acc hfr hacc
    have hst := foldl_visit_sound (k := k) hC frontier hfr (seen, []) (by simp)
    rcases hres : frontier.foldl (visit k C) (seen, []) with ⟨seen', found⟩
    rw [hres] at hst
    cases found with
    | nil => simpa [search, hres] using hacc
    | cons y₀ found =>
      simp only [search, hres]
      refine ih seen' (y₀ :: found) ((y₀ :: found) ++ acc) hst ?_
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hst y hy
      · exact hacc y hy

theorem genCheck_sound {targets : List (Equiv.Perm (Fin n))} (h : genCheck k C targets = true)
    (hC : ∀ c ∈ C, c ∈ X) : ∀ g ∈ targets, g ∈ X := by
  intro g hg
  simp only [genCheck, List.all_eq_true, List.contains_iff_mem] at h
  have h1 : ∀ y ∈ ([1] : List (Equiv.Perm (Fin n))), y ∈ X := by simp [X.one_mem]
  exact search_sound hC _ _ _ _ h1 h1 g (h g hg)

end Search

section Dihedral

variable {M : Type*} [Group M]

@[expose] def IsDihPair (u v : M) : Prop :=
  u * u = 1 ∧ v * v = 1 ∧ u * v ≠ v * u ∧ (u * v) ^ 4 = 1

@[expose] def dihInvs (u v : M) : List M :=
  [u, v, u * v * u, v * u * v, (u * v) ^ 2]

theorem IsDihPair.map {N : Type*} [Group N] {u v : M} (h : IsDihPair u v) (f : M →* N)
    (hf : Function.Injective f) : IsDihPair (f u) (f v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [← map_mul, h1, map_one], by rw [← map_mul, h2, map_one], fun h => h3 ?_,
    by rw [← map_mul, ← map_pow, h4, map_one]⟩
  apply hf
  rw [map_mul, map_mul, h]

theorem IsDihPair.of_map {N : Type*} [Group N] {u v : M} (f : M →* N)
    (hf : Function.Injective f) (h : IsDihPair (f u) (f v)) : IsDihPair u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hf (by rw [map_mul, h1, map_one]), hf (by rw [map_mul, h2, map_one]), fun h => h3 ?_,
    hf (by rw [map_pow, map_mul, h4, map_one])⟩
  rw [← map_mul, h, map_mul]

theorem dihInvs_map {N : Type*} [Group N] (f : M →* N) (u v : M) :
    dihInvs (f u) (f v) = (dihInvs u v).map f := by
  simp [dihInvs, map_mul, map_pow]

theorem dihInvs_subset {H : Subgroup M} {u v : M} (hu : u ∈ H) (hv : v ∈ H) :
    ∀ t ∈ dihInvs u v, t ∈ H := by
  intro t ht
  simp only [dihInvs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact hu
  · exact hv
  · exact H.mul_mem (H.mul_mem hu hv) hu
  · exact H.mul_mem (H.mul_mem hv hu) hv
  · exact H.pow_mem (H.mul_mem hu hv) 2

theorem IsDihPair.orderOf_eq_two {u v : M} (h : IsDihPair u v) :
    ∀ t ∈ dihInvs u v, orderOf t = 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right h1
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right h2
  have hu1 : u ≠ 1 := by rintro rfl; simp at h3
  have hv1 : v ≠ 1 := by rintro rfl; simp at h3
  intro t ht
  simp only [dihInvs, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact orderOf_eq_prime (by rw [sq, h1]) hu1
  · exact orderOf_eq_prime (by rw [sq, h2]) hv1
  · refine orderOf_eq_prime ?_ ?_
    · calc (u * v * u) ^ 2 = u * (v * (u * u) * v) * u := by simp only [sq, mul_assoc]
        _ = 1 := by rw [h1, mul_one, h2, mul_one, h1]
    · intro h
      apply hv1
      calc v = u⁻¹ * (u * v * u) * u⁻¹ := by group
        _ = 1 := by rw [h, mul_one, hu, h1]
  · refine orderOf_eq_prime ?_ ?_
    · calc (v * u * v) ^ 2 = v * (u * (v * v) * u) * v := by simp only [sq, mul_assoc]
        _ = 1 := by rw [h2, mul_one, h1, mul_one, h2]
    · intro h
      apply hu1
      calc u = v⁻¹ * (v * u * v) * v⁻¹ := by group
        _ = 1 := by rw [h, mul_one, hv, h2]
  · refine orderOf_eq_prime (by rw [← pow_mul]; exact h4) ?_
    intro h
    apply h3
    calc u * v = (u * v) ^ 2 * (v⁻¹ * u⁻¹) := by simp [sq, mul_assoc]
      _ = v * u := by rw [h, one_mul, hu, hv]

end Dihedral

section Pairs

variable {n : ℕ}

@[expose] def commB (c t : Equiv.Perm (Fin n)) : Bool :=
  (List.finRange n).all fun i => decide (c (t i) = t (c i))

theorem commB_iff (c t : Equiv.Perm (Fin n)) : commB c t = true ↔ c * t = t * c := by
  simp only [commB, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  constructor
  · intro h
    ext i
    simp [h i]
  · intro h i
    simpa using congrArg (fun g : Equiv.Perm (Fin n) => g i) h

@[expose] def spread {α : Type*} (m : ℕ) (L : List α) : List α :=
  (List.range m).filterMap fun j => L[j * (L.length / m)]?

theorem mem_of_mem_spread {α : Type*} {m : ℕ} {L : List α} {a : α} (h : a ∈ spread m L) :
    a ∈ L := by
  simp only [spread, List.mem_filterMap] at h
  obtain ⟨j, -, hj⟩ := h
  exact List.mem_of_getElem? hj

@[expose] def dihB (u v : Equiv.Perm (Fin n)) : Bool :=
  decide (u * u = 1) && decide (v * v = 1) && !decide (u * v = v * u) && decide ((u * v) ^ 4 = 1)

theorem dihB_iff (u v : Equiv.Perm (Fin n)) : dihB u v = true ↔ IsDihPair u v := by
  simp [dihB, IsDihPair, and_assoc]

@[expose, noinline] def pairCheck (k m : ℕ) (Q LP targets : List (Equiv.Perm (Fin n))) : Bool :=
  Q.all fun u => Q.all fun v =>
    !dihB u v ||
      genCheck k ((dihInvs u v).flatMap fun t =>
        let t' := tab t
        spread m (LP.filter fun c => commB c t')) targets

theorem pairCheck_sound {k m : ℕ} {Q LP targets : List (Equiv.Perm (Fin n))}
    (h : pairCheck k m Q LP targets = true) (P : Subgroup (Equiv.Perm (Fin n)))
    (hLP : ∀ c ∈ LP, c ∈ P) {u v : Equiv.Perm (Fin n)} (hu : u ∈ Q) (hv : v ∈ Q)
    (huv : IsDihPair u v) (X : Subgroup (Equiv.Perm (Fin n)))
    (hX : ∀ c ∈ P, ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) : ∀ g ∈ targets, g ∈ X := by
  simp only [pairCheck, List.all_eq_true] at h
  have h' := h u hu v hv
  rw [(dihB_iff u v).2 huv, Bool.not_true, Bool.false_or] at h'
  refine genCheck_sound h' ?_
  intro c hc
  simp only [List.mem_flatMap] at hc
  obtain ⟨t, ht, hc⟩ := hc
  obtain ⟨hcLP, hct⟩ := List.mem_filter.1 (mem_of_mem_spread hc)
  rw [commB_iff, tab_eq] at hct
  exact hX c (hLP c hcLP) t ht hct

end Pairs

end CFSG.ComponentClassification.FooteSmall

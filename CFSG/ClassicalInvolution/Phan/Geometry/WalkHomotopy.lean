module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Diam
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.ClassicalInvolution.Phan

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

inductive CycleMove (E : ∀ x : V, Set (G.Walk x x)) {u v : V} : G.Walk u v → G.Walk u v → Prop
  | backtrack {x y : V} (p : G.Walk u x) (q : G.Walk x v) (h : G.Adj x y) :
      CycleMove E (p.append q) (p.append (.cons h (.cons h.symm q)))
  | elem {x : V} (p : G.Walk u x) (q : G.Walk x v) (c : G.Walk x x) (hc : c ∈ E x) :
      CycleMove E (p.append q) (p.append (c.append q))

@[expose] def CycleHomotopic (E : ∀ x : V, Set (G.Walk x x)) {u v : V} (p q : G.Walk u v) :
    Prop :=
  Relation.EqvGen (CycleMove E) p q

@[expose] def CycleTrivial (E : ∀ x : V, Set (G.Walk x x)) : Prop :=
  ∀ (u : V) (p : G.Walk u u), CycleHomotopic E p .nil

namespace CycleHomotopic

variable {E : ∀ x : V, Set (G.Walk x x)} {u v w : V} {p q r : G.Walk u v}

@[refl] theorem refl (p : G.Walk u v) : CycleHomotopic E p p := Relation.EqvGen.refl p

@[symm] theorem symm (h : CycleHomotopic E p q) : CycleHomotopic E q p :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem trans (h₁ : CycleHomotopic E p q) (h₂ : CycleHomotopic E q r) :
    CycleHomotopic E p r :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem induction {R : G.Walk u v → G.Walk u v → Prop} (h : CycleHomotopic E p q)
    (hmove : ∀ a b, CycleMove E a b → R a b) (hrefl : ∀ a, R a a)
    (hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c) : R p q := by
  induction h with
  | rel a b hab => exact hmove a b hab
  | refl a => exact hrefl a
  | symm a b _ ih => exact hsymm a b ih
  | trans a b c _ _ ih₁ ih₂ => exact htrans a b c ih₁ ih₂

end CycleHomotopic

theorem CycleMove.cycleHomotopic {E : ∀ x : V, Set (G.Walk x x)} {u v : V} {p q : G.Walk u v}
    (h : CycleMove E p q) : CycleHomotopic E p q :=
  Relation.EqvGen.rel _ _ h

theorem cycleHomotopic_backtrack (E : ∀ x : V, Set (G.Walk x x)) {u x y v : V} (p : G.Walk u x)
    (q : G.Walk x v) (h : G.Adj x y) :
    CycleHomotopic E (p.append q) (p.append (.cons h (.cons h.symm q))) :=
  (CycleMove.backtrack p q h).cycleHomotopic

theorem cycleHomotopic_elem (E : ∀ x : V, Set (G.Walk x x)) {u x v : V} (p : G.Walk u x)
    (q : G.Walk x v) {c : G.Walk x x} (hc : c ∈ E x) :
    CycleHomotopic E (p.append q) (p.append (c.append q)) :=
  (CycleMove.elem p q c hc).cycleHomotopic

theorem cycleHomotopic_of_mem (E : ∀ x : V, Set (G.Walk x x)) {x : V} {c : G.Walk x x}
    (hc : c ∈ E x) : CycleHomotopic E c .nil := by
  simpa using (cycleHomotopic_elem E (.nil : G.Walk x x) .nil hc).symm

theorem CycleMove.append_left {E : ∀ x : V, Set (G.Walk x x)} {w u v : V} (r : G.Walk w u)
    {p q : G.Walk u v} (h : CycleMove E p q) : CycleMove E (r.append p) (r.append q) := by
  cases h with
  | backtrack p q h =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .backtrack _ q h
  | elem p q c hc =>
    rw [Walk.append_assoc, Walk.append_assoc]
    exact .elem _ q c hc

theorem CycleMove.append_right {E : ∀ x : V, Set (G.Walk x x)} {u v w : V} {p q : G.Walk u v}
    (h : CycleMove E p q) (r : G.Walk v w) : CycleMove E (p.append r) (q.append r) := by
  cases h with
  | backtrack p q h =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, Walk.cons_append, Walk.cons_append]
    exact .backtrack p _ h
  | elem p q c hc =>
    rw [← Walk.append_assoc, ← Walk.append_assoc, ← Walk.append_assoc]
    exact .elem p _ c hc

theorem CycleMove.reverse {E : ∀ x : V, Set (G.Walk x x)}
    (hE : ∀ x (c : G.Walk x x), c ∈ E x → c.reverse ∈ E x) {u v : V} {p q : G.Walk u v}
    (h : CycleMove E p q) : CycleMove E p.reverse q.reverse := by
  cases h with
  | backtrack p q h =>
    simp only [Walk.reverse_append, Walk.reverse_cons, ← Walk.append_assoc, Walk.cons_append,
      Walk.nil_append]
    exact .backtrack q.reverse p.reverse h
  | elem p q c hc =>
    simp only [Walk.reverse_append, ← Walk.append_assoc]
    exact .elem q.reverse p.reverse c.reverse (hE _ c hc)

namespace CycleHomotopic

variable {E : ∀ x : V, Set (G.Walk x x)} {u v w : V}

theorem append_left (r : G.Walk w u) {p q : G.Walk u v} (h : CycleHomotopic E p q) :
    CycleHomotopic E (r.append p) (r.append q) := by
  induction h with
  | rel p q h => exact (h.append_left r).cycleHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append_right {p q : G.Walk u v} (h : CycleHomotopic E p q) (r : G.Walk v w) :
    CycleHomotopic E (p.append r) (q.append r) := by
  induction h with
  | rel p q h => exact (h.append_right r).cycleHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem append {p p' : G.Walk u v} {q q' : G.Walk v w} (hp : CycleHomotopic E p p')
    (hq : CycleHomotopic E q q') : CycleHomotopic E (p.append q) (p'.append q') :=
  (hp.append_right q).trans (hq.append_left p')

theorem cons (h : G.Adj w u) {p q : G.Walk u v} (hpq : CycleHomotopic E p q) :
    CycleHomotopic E (.cons h p) (.cons h q) := by
  simpa using hpq.append_left (.cons h .nil)

theorem reverse (hE : ∀ x (c : G.Walk x x), c ∈ E x → c.reverse ∈ E x) {p q : G.Walk u v}
    (h : CycleHomotopic E p q) : CycleHomotopic E p.reverse q.reverse := by
  induction h with
  | rel p q h => exact (h.reverse hE).cycleHomotopic
  | refl p => exact refl _
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end CycleHomotopic

theorem cycleHomotopic_cons_cons_nil (E : ∀ x : V, Set (G.Walk x x)) {x y : V} (h : G.Adj x y) :
    CycleHomotopic E (.cons h (.cons h.symm .nil) : G.Walk x x) .nil :=
  (cycleHomotopic_backtrack E (.nil : G.Walk x x) .nil h).symm

theorem cycleHomotopic_append_reverse (E : ∀ x : V, Set (G.Walk x x)) {u v : V}
    (p : G.Walk u v) : CycleHomotopic E (p.append p.reverse) .nil := by
  induction p with
  | nil => exact CycleHomotopic.refl _
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, Walk.cons_append, Walk.append_assoc]
    refine (CycleHomotopic.cons h (ih.append_right (.cons h.symm .nil))).trans ?_
    exact cycleHomotopic_cons_cons_nil E h

theorem cycleHomotopic_reverse_append (E : ∀ x : V, Set (G.Walk x x)) {u v : V}
    (p : G.Walk u v) : CycleHomotopic E (p.reverse.append p) .nil := by
  simpa using cycleHomotopic_append_reverse E p.reverse

theorem cycleHomotopic_of_append_reverse (E : ∀ x : V, Set (G.Walk x x)) {u v : V}
    {p q : G.Walk u v} (h : CycleHomotopic E (p.append q.reverse) .nil) :
    CycleHomotopic E p q := by
  have h₁ : CycleHomotopic E (p.append (q.reverse.append q)) p := by
    simpa using (cycleHomotopic_reverse_append E q).append_left p
  have h₂ : CycleHomotopic E ((p.append q.reverse).append q) q := by
    simpa using h.append_right q
  rw [← Walk.append_assoc] at h₂
  exact h₁.symm.trans h₂

theorem cycleHomotopic_insert_null (E : ∀ x : V, Set (G.Walk x x)) {u x v : V} (p : G.Walk u x)
    (q : G.Walk x v) {c : G.Walk x x} (hc : CycleHomotopic E c .nil) :
    CycleHomotopic E (p.append q) (p.append (c.append q)) := by
  have := (hc.append_right q).append_left p
  simpa using this.symm

theorem cycleTrivial_iff_homotopic (E : ∀ x : V, Set (G.Walk x x)) :
    CycleTrivial E ↔ ∀ (u v : V) (p q : G.Walk u v), CycleHomotopic E p q := by
  refine ⟨fun hG u v p q => ?_, fun h u p => h u u p .nil⟩
  exact cycleHomotopic_of_append_reverse E (hG u (p.append q.reverse))

section Lasso

variable (E : ∀ x : V, Set (G.Walk x x))

@[expose] def cycleWalkProd {b : V} (L : List (G.Walk b b)) : G.Walk b b :=
  L.foldr (fun q r => q.append r) .nil

@[simp] theorem cycleWalkProd_nil {b : V} : cycleWalkProd ([] : List (G.Walk b b)) = .nil := rfl

@[simp] theorem cycleWalkProd_cons {b : V} (q : G.Walk b b) (L : List (G.Walk b b)) :
    cycleWalkProd (q :: L) = q.append (cycleWalkProd L) := rfl

theorem cycleHomotopic_walkProd_nil {b : V} {L : List (G.Walk b b)}
    (h : ∀ q ∈ L, CycleHomotopic E q .nil) : CycleHomotopic E (cycleWalkProd L) .nil := by
  induction L with
  | nil => exact CycleHomotopic.refl _
  | cons q L ih =>
    simpa using (h q List.mem_cons_self).append (ih fun r hr => h r (List.mem_cons_of_mem q hr))

@[expose] def cycleLasso {b : V} (γ : ∀ x, G.Walk b x) {x y : V} (h : G.Adj x y) : G.Walk b b :=
  (γ x).append (.cons h (γ y).reverse)

theorem length_cycleLasso {b : V} (γ : ∀ x, G.Walk b x) {x y : V} (h : G.Adj x y) :
    (cycleLasso γ h).length = (γ x).length + (γ y).length + 1 := by
  simp [cycleLasso]
  omega

theorem cycleHomotopic_foldr_lasso {b : V} (γ : ∀ x, G.Walk b x) :
    ∀ {x y : V} (p : G.Walk x y), ∃ L : List (G.Walk b b),
      (∀ q ∈ L, ∃ (x' y' : V) (h : G.Adj x' y'), q = cycleLasso γ h) ∧
      CycleHomotopic E ((γ x).append (p.append (γ y).reverse)) (cycleWalkProd L)
  | x, _, .nil => ⟨[], by simp, by simpa using cycleHomotopic_append_reverse E (γ x)⟩
  | x, y, .cons (v := x') h p => by
    obtain ⟨L, hL, hp⟩ := cycleHomotopic_foldr_lasso γ p
    refine ⟨cycleLasso γ h :: L, fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨x, x', h, rfl⟩
      · exact hL q hq
    · set R := (γ x').append (p.append (γ y).reverse) with hR
      have h₁ : CycleHomotopic E ((γ x').reverse.append R) (p.append (γ y).reverse) := by
        have := (cycleHomotopic_reverse_append E (γ x')).append_right (p.append (γ y).reverse)
        rwa [Walk.nil_append, ← Walk.append_assoc] at this
      have e : (cycleLasso γ h).append R = (γ x).append (.cons h ((γ x').reverse.append R)) := by
        rw [cycleLasso, ← Walk.append_assoc, Walk.cons_append]
      rw [cycleWalkProd_cons]
      refine ((h₁.symm.cons h).append_left (γ x)).trans ?_
      rw [← e]
      exact hp.append_left (cycleLasso γ h)

theorem cycleTrivial_of_short_closed_walks {b : V} {δ : ℕ}
    (hb : ∀ x, ∃ p : G.Walk b x, p.length ≤ δ)
    (hshort : ∀ p : G.Walk b b, p.length ≤ 2 * δ + 1 → CycleHomotopic E p .nil) :
    CycleTrivial E := by
  choose γ hγ using hb
  intro u p
  obtain ⟨L, hL, hp⟩ := cycleHomotopic_foldr_lasso E γ p
  have hnull : CycleHomotopic E ((γ u).append (p.append (γ u).reverse)) .nil :=
    hp.trans (cycleHomotopic_walkProd_nil E fun q hq => by
      obtain ⟨x, y, h, rfl⟩ := hL q hq
      refine hshort _ ?_
      have := hγ x
      have := hγ y
      rw [length_cycleLasso]
      omega)
  have h₁ : CycleHomotopic E p (((γ u).reverse.append (γ u)).append
      (p.append ((γ u).reverse.append (γ u)))) := by
    have := (cycleHomotopic_reverse_append E (γ u)).symm.append
      ((cycleHomotopic_reverse_append E (γ u)).symm.append_left p)
    rwa [Walk.append_nil, Walk.nil_append] at this
  have h₂ : CycleHomotopic E (((γ u).reverse.append (γ u)).append
      (p.append ((γ u).reverse.append (γ u)))) ((γ u).reverse.append (γ u)) := by
    have := (hnull.append_right (γ u)).append_left (γ u).reverse
    simpa [Walk.append_assoc] using this
  exact h₁.trans (h₂.trans (cycleHomotopic_reverse_append E (γ u)))

theorem cycleTrivial_of_diam (hconn : G.Connected) (hfin : G.ediam ≠ ⊤)
    (hshort : ∀ (u : V) (p : G.Walk u u), p.length ≤ 2 * G.diam + 1 → CycleHomotopic E p .nil) :
    CycleTrivial E := by
  obtain ⟨b⟩ := hconn.nonempty
  refine cycleTrivial_of_short_closed_walks E (b := b) (δ := G.diam) (fun x => ?_) (hshort b)
  obtain ⟨p, hp⟩ := (hconn.preconnected b x).exists_walk_length_eq_dist
  exact ⟨p, hp ▸ SimpleGraph.dist_le_diam hfin⟩

end Lasso

section Cone

variable (E : ∀ x : V, Set (G.Walk x x))

theorem cycleHomotopic_replace_edge {x y e : V} (hxy : G.Adj x y) (hxe : G.Adj x e)
    (hye : G.Adj y e)
    (hT : CycleHomotopic E (.cons hxy (.cons hye (.cons hxe.symm .nil)) : G.Walk x x) .nil) :
    CycleHomotopic E (.cons hxy .nil : G.Walk x y) (.cons hxe (.cons hye.symm .nil)) := by
  refine cycleHomotopic_of_append_reverse E ?_
  simpa using hT

theorem cycleHomotopic_cone {e : V} (S : V → V → Prop)
    (hS : ∀ x y, S x y → ∃ (hxy : G.Adj x y) (hxe : G.Adj x e) (hye : G.Adj y e),
      CycleHomotopic E (.cons hxy (.cons hye (.cons hxe.symm .nil)) : G.Walk x x) .nil) :
    ∀ {u v : V} (p : G.Walk u v) (hu : G.Adj u e) (hv : G.Adj v e),
      (∀ d ∈ p.darts, S d.fst d.snd) →
      CycleHomotopic E p (.cons hu (.cons hv.symm .nil))
  | u, _, .nil, hu, hv, _ => (cycleHomotopic_cons_cons_nil E hu).symm
  | u, v, .cons (v := w) h p, hu, hv, hS' => by
    obtain ⟨_, hxe, hwe, hT⟩ := hS u w (hS' ⟨(u, w), h⟩ (by simp))
    have ih := cycleHomotopic_cone S hS p hwe hv (fun d hd => hS' d (by simp [hd]))
    have h₁ : CycleHomotopic E (.cons h p) (.cons h (.cons hwe (.cons hv.symm .nil))) :=
      ih.cons h
    have h₂ : CycleHomotopic E (.cons h (.cons hwe (.cons hv.symm .nil)))
        (.cons hxe (.cons hwe.symm (.cons hwe (.cons hv.symm .nil)))) := by
      have := (cycleHomotopic_replace_edge E h hxe hwe hT).append_right
        (.cons hwe (.cons hv.symm .nil))
      simpa using this
    have h₃ : CycleHomotopic E (.cons hxe (.cons hv.symm .nil))
        (.cons hxe (.cons hwe.symm (.cons hwe (.cons hv.symm .nil)))) := by
      have := cycleHomotopic_backtrack E (.cons hxe .nil : G.Walk u e) (.cons hv.symm .nil)
        hwe.symm
      simpa using this
    exact h₁.trans (h₂.trans h₃.symm)

theorem cycleHomotopic_cone_nil {e u : V} (S : V → V → Prop)
    (hS : ∀ x y, S x y → ∃ (hxy : G.Adj x y) (hxe : G.Adj x e) (hye : G.Adj y e),
      CycleHomotopic E (.cons hxy (.cons hye (.cons hxe.symm .nil)) : G.Walk x x) .nil)
    (p : G.Walk u u) (hu : G.Adj u e) (hp : ∀ d ∈ p.darts, S d.fst d.snd) :
    CycleHomotopic E p .nil :=
  (cycleHomotopic_cone E S hS p hu hu hp).trans (cycleHomotopic_cons_cons_nil E hu)

end Cone

end CFSG.ClassicalInvolution.Phan

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Group.Action.End
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
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

namespace CFSG.Combinatorics.UniqueCycleFaithful

variable {V : Type*} {G : SimpleGraph V}

@[expose] def IsCycleEdgeSet [DecidableEq V] (G : SimpleGraph V) (m : ℕ)
    (s : Finset (Sym2 V)) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = m ∧ p.edges.toFinset = s

theorem edges_toFinset_rotate [DecidableEq V] {u : V} (p : G.Walk u u) (w : V)
    (h : w ∈ p.support) : (p.rotate w h).edges.toFinset = p.edges.toFinset :=
  List.toFinset_eq_of_perm _ _ (p.rotate_edges w h).perm

theorem edges_toFinset_reverse [DecidableEq V] {u w : V} (p : G.Walk u w) :
    p.reverse.edges.toFinset = p.edges.toFinset := by
  rw [SimpleGraph.Walk.edges_reverse, List.toFinset_reverse]

theorem exists_other_cycle_edge {u : V} {p : G.Walk u u} (hp : p.IsCycle) {a b : V}
    (hab : s(a, b) ∈ p.edges) :
    ∃ c, c ≠ b ∧ s(a, c) ∈ p.edges ∧ ∀ w, s(a, w) ∈ p.edges → w = b ∨ w = c := by
  have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges hab
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp (hp.ncard_neighborSet_toSubgraph_eq_two ha)
  have hmem : ∀ w, w ∈ p.toSubgraph.neighborSet a ↔ s(a, w) ∈ p.edges := fun w => by
    rw [SimpleGraph.Subgraph.mem_neighborSet, ← SimpleGraph.Subgraph.mem_edgeSet,
      SimpleGraph.Walk.mem_edges_toSubgraph]
  have hpair : ∀ w, s(a, w) ∈ p.edges ↔ w = x ∨ w = y := fun w => by
    rw [← hmem, hset, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases (hpair b).mp hab with rfl | rfl
  · refine ⟨y, hxy.symm, (hpair y).mpr (Or.inr rfl), fun w hw => (hpair w).mp hw⟩
  · refine ⟨x, hxy, (hpair x).mpr (Or.inl rfl), fun w hw => ((hpair w).mp hw).symm⟩

theorem isCycleEdgeSet_image [DecidableEq V] (g : G ≃g G) {m : ℕ} {s : Finset (Sym2 V)}
    (hs : IsCycleEdgeSet G m s) : IsCycleEdgeSet G m (s.image (Sym2.map g)) := by
  obtain ⟨u, p, hp, hlen, rfl⟩ := hs
  refine ⟨g u, p.map g.toHom, (SimpleGraph.Walk.isCycle_map_iff_of_injective
    (f := g.toHom) g.injective).mpr hp, by rw [SimpleGraph.Walk.length_map, hlen], ?_⟩
  ext e
  simp only [SimpleGraph.Walk.edges_map, List.mem_toFinset, List.mem_map, Finset.mem_image]
  rfl

theorem map_mem_of_fix_path [DecidableEq V] {m : ℕ}
    (hcyc : ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z →
      ∃! s : Finset (Sym2 V), IsCycleEdgeSet G m s ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s)
    (g : G ≃g G) {x y z : V} (hxz : x ≠ z) (hxy : G.Adj x y) (hyz : G.Adj y z) (hgx : g x = x)
    (hgy : g y = y) (hgz : g z = z) {s : Finset (Sym2 V)} (hs : IsCycleEdgeSet G m s)
    (hsxy : s(x, y) ∈ s) (hsyz : s(y, z) ∈ s) : ∀ e ∈ s, Sym2.map g e ∈ s := by
  have himg : s.image (Sym2.map g) = s := by
    refine (hcyc x y z hxz hxy hyz).unique ⟨isCycleEdgeSet_image g hs, ?_, ?_⟩ ⟨hs, hsxy, hsyz⟩
    · rw [Finset.mem_image]
      exact ⟨s(x, y), hsxy, by rw [Sym2.map_mk, hgx, hgy]⟩
    · rw [Finset.mem_image]
      exact ⟨s(y, z), hsyz, by rw [Sym2.map_mk, hgy, hgz]⟩
  intro e he
  rw [← himg]
  exact Finset.mem_image_of_mem _ he

@[expose] def neighborRestriction (G : SimpleGraph V) (v : V) :
    MulAction.stabilizer (G ≃g G) v →* Equiv.Perm (G.neighborSet v) where
  toFun g := (g : G ≃g G).toEquiv.subtypeEquiv fun w => by
    have hg : (g : G ≃g G) v = v := g.2
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet]
    constructor
    · intro h
      have h' := (g : G ≃g G).map_adj_iff.mpr h
      rw [hg] at h'
      exact h'
    · intro h
      have h' : G.Adj ((g : G ≃g G) v) ((g : G ≃g G) w) := by
        rw [hg]
        exact h
      exact (g : G ≃g G).map_adj_iff.mp h'
  map_one' := by
    ext w
    rfl
  map_mul' g h := by
    ext w
    rfl

theorem neighborRestriction_apply (v : V) (g : MulAction.stabilizer (G ≃g G) v)
    (w : G.neighborSet v) : (neighborRestriction G v g w : V) = (g : G ≃g G) w := rfl

end CFSG.Combinatorics.UniqueCycleFaithful

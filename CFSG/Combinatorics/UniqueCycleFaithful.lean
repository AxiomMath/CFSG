module

public import CFSG.Combinatorics.UniqueCycleFaithfulSupport

public section

namespace CFSG.Combinatorics.UniqueCycleFaithful

variable {V : Type*} {G : SimpleGraph V}

theorem fix_neighbors_of_fix_neighbors [DecidableEq V] {m : ℕ}
    (hcyc : ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z →
      ∃! s : Finset (Sym2 V), IsCycleEdgeSet G m s ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s)
    (g : G ≃g G) {v : V} (hv : g v = v) (hN : ∀ w, G.Adj v w → g w = w) {a : V}
    (ha : G.Adj v a) : ∀ w, G.Adj a w → g w = w := by
  intro w haw
  by_cases hwv : w = v
  · rw [hwv]
    exact hv
  obtain ⟨s, ⟨hs, hsva, hsaw⟩, -⟩ := hcyc v a w (Ne.symm hwv) ha haw
  obtain ⟨u, p, hp, hlen, hps⟩ := hs
  have hmem : ∀ e, e ∈ s ↔ e ∈ p.edges := fun e => by rw [← hps, List.mem_toFinset]
  obtain ⟨b, hba, hvb, -⟩ := exists_other_cycle_edge hp ((hmem _).mp hsva)
  have hvb' : G.Adj v b := p.adj_of_mem_edges hvb
  have hga := hN a ha
  have hgb := hN b hvb'
  have hpres := map_mem_of_fix_path hcyc g hba hvb'.symm ha hgb hv hga ⟨u, p, hp, hlen, hps⟩
    ((hmem _).mpr (by rw [Sym2.eq_swap]; exact hvb)) hsva
  have hav : s(a, v) ∈ p.edges := by
    rw [Sym2.eq_swap]
    exact (hmem _).mp hsva
  obtain ⟨c, hcv, -, huniq⟩ := exists_other_cycle_edge hp hav
  have hwc : w = c := ((huniq w ((hmem _).mp hsaw)).resolve_left hwv)
  have hgw : s(a, g w) ∈ p.edges := by
    have h := hpres _ hsaw
    rw [Sym2.map_mk, hga] at h
    exact (hmem _).mp h
  rcases huniq (g w) hgw with h | h
  · exact absurd (g.injective (h.trans hv.symm)) hwv
  · rw [h, hwc]

theorem eq_one_of_fix_neighbors [DecidableEq V] {m : ℕ}
    (hcyc : ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z →
      ∃! s : Finset (Sym2 V), IsCycleEdgeSet G m s ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s)
    (hconn : G.Connected) (g : G ≃g G) {v : V} (hv : g v = v)
    (hN : ∀ w, G.Adj v w → g w = w) : g = 1 := by
  have key : ∀ (t u : V) (p : G.Walk u t), g u = u → (∀ w, G.Adj u w → g w = w) → g t = t := by
    intro t u p
    induction p with
    | nil => exact fun hu _ => hu
    | cons h q ih =>
      exact fun hu hNu => ih (hNu _ h) (fix_neighbors_of_fix_neighbors hcyc g hu hNu h)
  ext t
  obtain ⟨p⟩ := hconn.preconnected v t
  exact key t v p hv hN

theorem unique_fixed_length_cycles_make_neighborhood_action_faithful [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) (d : ℕ)
    (hreg : G.IsRegularOfDegree d) (_hd : 2 ≤ d) (m : ℕ) (_hm : 3 ≤ m)
    (hcyc : ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z →
      ∃! s : Finset (Sym2 V), (∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = m ∧
        p.edges.toFinset = s) ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s) :
    (∀ v : V, (∀ (g : MulAction.stabilizer (G ≃g G) v) (w : G.neighborSet v),
        (neighborRestriction G v g w : V) = (g : G ≃g G) w) ∧
      Function.Injective (neighborRestriction G v) ∧
      Nat.card (MulAction.stabilizer (G ≃g G) v) ≤ d.factorial) ∧
    Nat.card (G ≃g G) ≤ Fintype.card V * d.factorial := by
  have hcyc' : ∀ x y z : V, x ≠ z → G.Adj x y → G.Adj y z →
      ∃! s : Finset (Sym2 V), IsCycleEdgeSet G m s ∧ s(x, y) ∈ s ∧ s(y, z) ∈ s := hcyc
  have hinj : ∀ v : V, Function.Injective (neighborRestriction G v) := by
    intro v
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine eq_one_of_fix_neighbors hcyc' hconn (g : G ≃g G) (v := v) g.2 fun w hw => ?_
    have h := congrArg (fun σ : Equiv.Perm (G.neighborSet v) => (σ ⟨w, hw⟩ : V)) hg
    exact h
  have hcard : ∀ v : V, Nat.card (MulAction.stabilizer (G ≃g G) v) ≤ d.factorial := by
    intro v
    calc Nat.card (MulAction.stabilizer (G ≃g G) v) ≤ Nat.card (Equiv.Perm (G.neighborSet v)) :=
          Nat.card_le_card_of_injective _ (hinj v)
      _ = d.factorial := by
          rw [Nat.card_perm, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree, hreg v]
  refine ⟨fun v => ⟨fun g w => neighborRestriction_apply v g w, hinj v, hcard v⟩, ?_⟩
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (G ≃g G) v)]
  have horb : Nat.card ((G ≃g G) ⧸ MulAction.stabilizer (G ≃g G) v) ≤ Fintype.card V := by
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (G ≃g G) v),
      ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact Nat.mul_le_mul horb (hcard v)

end CFSG.Combinatorics.UniqueCycleFaithful

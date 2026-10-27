module

public import CFSG.Combinatorics.CubicBipartiteMooreSupport

public section

open CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.OuterLayer

universe u v u' v'

structure MarkedIncidenceSystem where
  Pt : Type u
  Ln : Type v
  inc : Pt → Ln → Prop
  marked : Set Pt

namespace MarkedIncidenceSystem

structure Iso (S : MarkedIncidenceSystem.{u, v}) (T : MarkedIncidenceSystem.{u', v'}) where
  pts : S.Pt ≃ T.Pt
  lines : S.Ln ≃ T.Ln
  inc_iff : ∀ x m, S.inc x m ↔ T.inc (pts x) (lines m)
  marked_iff : ∀ x, x ∈ S.marked ↔ pts x ∈ T.marked

def Iso.refl (S : MarkedIncidenceSystem.{u, v}) : S.Iso S :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem Iso.image_marked {S : MarkedIncidenceSystem.{u, v}} {T : MarkedIncidenceSystem.{u', v'}}
    (e : S.Iso T) : e.pts '' S.marked = T.marked := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (e.marked_iff x).mp hx
  · intro hy
    exact ⟨e.pts.symm y, (e.marked_iff _).mpr (by rwa [Equiv.apply_symm_apply]),
      Equiv.apply_symm_apply _ _⟩

@[expose] def ptGraph (S : MarkedIncidenceSystem.{u, v}) : SimpleGraph S.Pt :=
  SimpleGraph.fromRel fun x y => ∃ m, S.inc x m ∧ S.inc y m

end MarkedIncidenceSystem

variable {V : Type u}

@[expose] def IsOuterLine (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) (m : V) : Prop :=
  col m = true ∧ ∀ x : {v : V // col v = false}, G.Adj (x : V) m → i ≤ (pointGraph G col).dist w x

@[expose] def outerSystem (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) : MarkedIncidenceSystem.{u, u} where
  Pt := {x : {v : V // col v = false} // i ≤ (pointGraph G col).dist w x}
  Ln := {m : V // IsOuterLine G col w i m}
  inc x m := G.Adj ((x : {v : V // col v = false}) : V) m
  marked := {x | (pointGraph G col).dist w x = i}

@[expose] def outerGraph (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) : SimpleGraph {v : V // col v = false} :=
  SimpleGraph.fromRel fun x y => ∃ m, IsOuterLine G col w i m ∧ G.Adj (x : V) m ∧ G.Adj (y : V) m

@[expose] noncomputable def outerDist (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) (x y : {v : V // col v = false}) : ℕ∞ :=
  (outerGraph G col w i).edist x y

@[expose] def OuterRel (G : SimpleGraph V) (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (i : ℕ) (x y : {v : V // col v = false}) : Prop :=
  outerDist G col w i x y = 4 ∧ ∃ L : V, IsOuterLine G col w i L ∧ G.Adj (x : V) L ∧
    ∀ u : {v : V // col v = false}, G.Adj (u : V) L → u ≠ x → outerDist G col w i y u = 3

variable {G : SimpleGraph V} {col : G.Coloring Bool} {w : {v : V // col v = false}}

theorem outerGraph_adj {i : ℕ} {x y : {v : V // col v = false}} :
    (outerGraph G col w i).Adj x y ↔
      x ≠ y ∧ ∃ m, IsOuterLine G col w i m ∧ G.Adj (x : V) m ∧ G.Adj (y : V) m := by
  rw [outerGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, ⟨m, hm, hx, hy⟩ | ⟨m, hm, hy, hx⟩⟩ <;> exact ⟨hxy, m, hm, hx, hy⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

theorem le_dist_of_outerGraph_adj {i : ℕ} {x y : {v : V // col v = false}}
    (h : (outerGraph G col w i).Adj x y) : i ≤ (pointGraph G col).dist w x := by
  obtain ⟨-, m, hm, hx, -⟩ := outerGraph_adj.mp h
  exact hm.2 x hx

theorem outerDist_eq {i : ℕ}
    (x y : {x : {v : V // col v = false} // i ≤ (pointGraph G col).dist w x}) :
    outerDist G col w i x y = (outerSystem G col w i).ptGraph.edist x y := by
  have hS : ∀ {a b : (outerSystem G col w i).Pt}, (outerSystem G col w i).ptGraph.Adj a b ↔
      a ≠ b ∧ ∃ m : (outerSystem G col w i).Ln, (outerSystem G col w i).inc a m ∧
        (outerSystem G col w i).inc b m := by
    intro a b
    rw [MarkedIncidenceSystem.ptGraph, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨hab, ⟨m, ha, hb⟩ | ⟨m, hb, ha⟩⟩ <;> exact ⟨hab, m, ha, hb⟩
    · rintro ⟨hab, h⟩
      exact ⟨hab, Or.inl h⟩
  let f : (outerSystem G col w i).ptGraph →g outerGraph G col w i :=
    ⟨fun a => a.1, fun {a b} hab => by
      obtain ⟨hne, m, ha, hb⟩ := hS.mp hab
      exact outerGraph_adj.mpr ⟨fun e => hne (Subtype.ext e), m.1, m.2, ha, hb⟩⟩
  have hlift : ∀ (a b : {v : V // col v = false}) (p : (outerGraph G col w i).Walk a b)
      (ha : i ≤ (pointGraph G col).dist w a) (hb : i ≤ (pointGraph G col).dist w b),
      (outerSystem G col w i).ptGraph.edist ⟨a, ha⟩ ⟨b, hb⟩ ≤ p.length := by
    intro a b p
    induction p with
    | nil =>
      intro _ _
      rw [SimpleGraph.Walk.length_nil]
      exact (SimpleGraph.edist_eq_zero_iff.mpr rfl).le
    | @cons a c d h p ih =>
      intro ha hd
      have hc : i ≤ (pointGraph G col).dist w c := le_dist_of_outerGraph_adj h.symm
      obtain ⟨hne, m, hm, am, cm⟩ := outerGraph_adj.mp h
      have hadj : (outerSystem G col w i).ptGraph.Adj ⟨a, ha⟩ ⟨c, hc⟩ :=
        hS.mpr ⟨fun e => hne (congrArg Subtype.val e), ⟨m, hm⟩, am, cm⟩
      have h1 := (outerSystem G col w i).ptGraph.edist_triangle (u := ⟨a, ha⟩) (v := ⟨c, hc⟩)
        (w := ⟨d, hd⟩)
      rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at h1
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      exact h1.trans (by gcongr; exact ih hc hd)
  apply le_antisymm
  · by_cases hr : (outerSystem G col w i).ptGraph.Reachable x y
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
      rw [← hp, ← SimpleGraph.Walk.length_map f p]
      exact SimpleGraph.edist_le _
    · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
      exact le_top
  · by_cases hr : (outerGraph G col w i).Reachable x y
    · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
      rw [outerDist, ← hp]
      exact hlift _ _ p x.2 y.2
    · rw [outerDist, SimpleGraph.edist_eq_top_of_not_reachable hr]
      exact le_top

end CFSG.Combinatorics.OuterLayer

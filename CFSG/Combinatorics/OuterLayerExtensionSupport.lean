module

public import CFSG.Combinatorics.OuterLayerIncidenceSystems

public section

open CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.OuterLayer

universe u v u' v'

section General

variable {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'}

theorem edist_map_le (f : H →g H') (a b : W) : H'.edist (f a) (f b) ≤ H.edist a b := by
  by_cases hr : H.Reachable a b
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp, ← SimpleGraph.Walk.length_map f p]
    exact SimpleGraph.edist_le _
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

theorem edist_iso (f : H ≃g H') (a b : W) : H'.edist (f a) (f b) = H.edist a b := by
  refine le_antisymm (edist_map_le f.toHom a b) ?_
  have h := edist_map_le f.symm.toHom (f a) (f b)
  simpa only [RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, RelIso.symm_apply_apply]
    using h

theorem dist_iso (f : H ≃g H') (a b : W) : H'.dist (f a) (f b) = H.dist a b := by
  rw [SimpleGraph.dist, SimpleGraph.dist, edist_iso]

end General

namespace MarkedIncidenceSystem

variable {S : MarkedIncidenceSystem.{u, v}} {T : MarkedIncidenceSystem.{u', v'}}

theorem ptGraph_adj {a b : S.Pt} : S.ptGraph.Adj a b ↔ a ≠ b ∧ ∃ m, S.inc a m ∧ S.inc b m := by
  rw [ptGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hab, ⟨m, ha, hb⟩ | ⟨m, hb, ha⟩⟩ <;> exact ⟨hab, m, ha, hb⟩
  · rintro ⟨hab, h⟩
    exact ⟨hab, Or.inl h⟩

@[expose] def Iso.symm (e : S.Iso T) : T.Iso S where
  pts := e.pts.symm
  lines := e.lines.symm
  inc_iff x m := by
    simpa only [Equiv.apply_symm_apply] using (e.inc_iff (e.pts.symm x) (e.lines.symm m)).symm
  marked_iff x := by
    simpa only [Equiv.apply_symm_apply] using (e.marked_iff (e.pts.symm x)).symm

@[simp] theorem Iso.symm_pts_apply (e : S.Iso T) (x : S.Pt) : e.symm.pts (e.pts x) = x :=
  e.pts.symm_apply_apply x

@[simp] theorem Iso.pts_symm_apply (e : S.Iso T) (x : T.Pt) : e.pts (e.symm.pts x) = x :=
  e.pts.apply_symm_apply x

@[simp] theorem Iso.symm_lines_apply (e : S.Iso T) (m : S.Ln) : e.symm.lines (e.lines m) = m :=
  e.lines.symm_apply_apply m

@[simp] theorem Iso.lines_symm_apply (e : S.Iso T) (m : T.Ln) : e.lines (e.symm.lines m) = m :=
  e.lines.apply_symm_apply m

def Iso.ptGraphIso (e : S.Iso T) : S.ptGraph ≃g T.ptGraph where
  toEquiv := e.pts
  map_rel_iff' {a b} := by
    rw [ptGraph_adj, ptGraph_adj]
    constructor
    · rintro ⟨hab, m, ha, hb⟩
      refine ⟨fun h => hab (congrArg e.pts h), e.lines.symm m, ?_, ?_⟩
      · rw [e.inc_iff, Equiv.apply_symm_apply]
        exact ha
      · rw [e.inc_iff, Equiv.apply_symm_apply]
        exact hb
    · rintro ⟨hab, m, ha, hb⟩
      exact ⟨fun h => hab (e.pts.injective h), e.lines m, (e.inc_iff a m).mp ha,
        (e.inc_iff b m).mp hb⟩

variable {V : Type u} {V' : Type u'} {G : SimpleGraph V} {G' : SimpleGraph V'}
  {col : G.Coloring Bool} {col' : G'.Coloring Bool} {w : {v : V // col v = false}}
  {w' : {v : V' // col' v = false}} {i : ℕ}

theorem Iso.outerDist_eq (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    (x y : (outerSystem G col w i).Pt) :
    outerDist G' col' w' i (χ.pts x).1 (χ.pts y).1 = outerDist G col w i x.1 y.1 := by
  rw [OuterLayer.outerDist_eq (χ.pts x) (χ.pts y), OuterLayer.outerDist_eq x y]
  exact edist_iso χ.ptGraphIso x y

theorem Iso.outerGraph_adj (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    {x y : (outerSystem G col w i).Pt} (h : (outerGraph G col w i).Adj x.1 y.1) :
    (outerGraph G' col' w' i).Adj (χ.pts x).1 (χ.pts y).1 := by
  obtain ⟨hxy, m, hm, xm, ym⟩ := OuterLayer.outerGraph_adj.mp h
  refine OuterLayer.outerGraph_adj.mpr ⟨fun e => hxy ?_, (χ.lines ⟨m, hm⟩).1, (χ.lines ⟨m, hm⟩).2,
    (χ.inc_iff x ⟨m, hm⟩).mp xm, (χ.inc_iff y ⟨m, hm⟩).mp ym⟩
  rw [χ.pts.injective (Subtype.ext e)]

theorem Iso.outerGraph_adj_iff (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    (x y : (outerSystem G col w i).Pt) :
    (outerGraph G' col' w' i).Adj (χ.pts x).1 (χ.pts y).1 ↔ (outerGraph G col w i).Adj x.1 y.1 := by
  refine ⟨fun h => ?_, χ.outerGraph_adj⟩
  have := χ.symm.outerGraph_adj h
  rwa [Iso.symm_pts_apply, Iso.symm_pts_apply] at this

theorem Iso.outerRel (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    {x y : (outerSystem G col w i).Pt} (h : OuterRel G col w i x.1 y.1) :
    OuterRel G' col' w' i (χ.pts x).1 (χ.pts y).1 := by
  obtain ⟨hD, L, hL, xL, hLu⟩ := h
  refine ⟨by rw [χ.outerDist_eq]; exact hD, (χ.lines ⟨L, hL⟩).1, (χ.lines ⟨L, hL⟩).2,
    (χ.inc_iff x ⟨L, hL⟩).mp xL, fun u' hu'L hu'x => ?_⟩
  have hu'i : i ≤ (pointGraph G' col').dist w' u' := (χ.lines ⟨L, hL⟩).2.2 u' hu'L
  obtain ⟨u, hu⟩ := χ.pts.surjective ⟨u', hu'i⟩
  have huL : G.Adj u.1.1 L := (χ.inc_iff u ⟨L, hL⟩).mpr (by rw [hu]; exact hu'L)
  have hux : u.1 ≠ x.1 := fun e => hu'x (by
    have h2 : χ.pts u = χ.pts x := congrArg χ.pts (Subtype.ext e)
    rw [hu] at h2
    exact congrArg Subtype.val h2)
  have h3 := hLu u.1 huL hux
  rw [← χ.outerDist_eq, hu] at h3
  exact h3

theorem Iso.outerRel_iff (χ : (outerSystem G col w i).Iso (outerSystem G' col' w' i))
    (x y : (outerSystem G col w i).Pt) :
    OuterRel G' col' w' i (χ.pts x).1 (χ.pts y).1 ↔ OuterRel G col w i x.1 y.1 := by
  refine ⟨fun h => ?_, χ.outerRel⟩
  have := χ.symm.outerRel h
  rwa [Iso.symm_pts_apply, Iso.symm_pts_apply] at this

end MarkedIncidenceSystem

end CFSG.Combinatorics.OuterLayer

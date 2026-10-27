module

public import CFSG.Combinatorics.HexagonPeriodicPropagationSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonOppositeEdge CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.HexagonPeriodicPropagation

variable {V : Type*}

theorem nodup_seven {a b c d e f g : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (haf : a ≠ f) (hag : a ≠ g) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hbf : b ≠ f) (hbg : b ≠ g) (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f) (hcg : c ≠ g)
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    [a, b, c, d, e, f, g].Nodup := by
  simp [hab, hac, had, hae, haf, hag, hbc, hbd, hbe, hbf, hbg, hcd, hce, hcf, hcg, hde, hdf, hdg,
    hef, heg, hfg]

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}

namespace IsFrame

variable (F : IsFrame G col w ℓ p z q c ε)
include F

theorem repeat_label {v₀ v₁ v₂ v₃ v₄ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w v₀ = 3) (h₁ : (pointGraph G col).dist w v₁ = 3)
    (h₂ : (pointGraph G col).dist w v₂ = 3) (h₃ : (pointGraph G col).dist w v₃ = 3)
    (h₄ : (pointGraph G col).dist w v₄ = 3) (h01 : (pointGraph G col).Adj v₀ v₁)
    (h12 : (pointGraph G col).Adj v₁ v₂) (h23 : (pointGraph G col).Adj v₂ v₃)
    (h34 : (pointGraph G col).Adj v₃ v₄) (hnd : [v₀, v₁, v₂, v₃, v₄].Nodup)
    (hc : c v₀ v₁ = c v₃ v₄) : q v₀ v₁ = q v₃ v₄ :=
  (opposite_edge_equal_label_separation_and_four_path_repeat G F.moore col w ℓ F.inj F.root p
    F.line F.ne F.label z q c ε F.data).2 v₀ h₀ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ h01 h12 h23 h34 hnd hc

theorem no_pentagon {x₀ x₁ x₂ x₃ x₄ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w x₀ = 3) (h₁ : (pointGraph G col).dist w x₁ = 3)
    (h₂ : (pointGraph G col).dist w x₂ = 3) (h₃ : (pointGraph G col).dist w x₃ = 3)
    (h₄ : (pointGraph G col).dist w x₄ = 3) (h01 : (pointGraph G col).Adj x₀ x₁)
    (h12 : (pointGraph G col).Adj x₁ x₂) (h23 : (pointGraph G col).Adj x₂ x₃)
    (h34 : (pointGraph G col).Adj x₃ x₄) (h40 : (pointGraph G col).Adj x₄ x₀) (h02 : x₀ ≠ x₂)
    (h03 : x₀ ≠ x₃) (h13 : x₁ ≠ x₃) : False := by
  have hD := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  exact no_far_pentagon F.moore col ((hD w x₀ 3).mp h₀) ((hD w x₁ 3).mp h₁) ((hD w x₂ 3).mp h₂)
    ((hD w x₃ 3).mp h₃) ((hD w x₄ 3).mp h₄) ((hA _ _).mp h01) ((hA _ _).mp h12)
    ((hA _ _).mp h23) ((hA _ _).mp h34) ((hA _ _).mp h40) (fun h => h02 (Subtype.ext h))
    (fun h => h03 (Subtype.ext h)) (fun h => h13 (Subtype.ext h))

theorem edge {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y) :
    ∃ m : V, G.neighborFinset m = {(x : V), (y : V), (z x y : V)} ∧ G.Adj (x : V) m ∧
      G.Adj (y : V) m ∧ G.Adj (z x y : V) m ∧ G.dist (w : V) (z x y) = 4 ∧
      G.dist (w : V) (q x y) = 2 ∧ G.dist (z x y : V) (q x y) = 2 ∧
      G.dist (q x y : V) x = 4 ∧ G.dist (q x y : V) y = 4 ∧ G.dist (q x y : V) m = 3 :=
  frame_edge F.moore col F.data hx hy hxy

theorem colour_eq_of_third_eq {x y x' y' : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hy : (pointGraph G col).dist w y = 3)
    (hxy : (pointGraph G col).Adj x y) (hx' : (pointGraph G col).dist w x' = 3)
    (hy' : (pointGraph G col).dist w y' = 3) (hxy' : (pointGraph G col).Adj x' y')
    (h : z x y = z x' y') : q x y = q x' y' ∧ c x y = c x' y' := by
  have hq : q x y = q x' y' := by
    have h1 := ((F.data x hx y hy hxy).2.1 (q x y)).mpr rfl
    rw [h] at h1
    exact (((F.data x' hx' y' hy' hxy').2.1 (q x y)).mp h1)
  refine ⟨hq, ?_⟩
  have e := (F.data x hx y hy hxy).2.2
  rw [hq, (F.data x' hx' y' hy' hxy').2.2] at e
  exact (label_injective F.moore col F.inj F.root F.line F.ne F.label e).1.symm

theorem exists_edge_of_third {x α : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hα : (pointGraph G col).dist w α = 2)
    (hxα : G.dist (x : V) α = 2) :
    ∃ x', (pointGraph G col).dist w x' = 3 ∧ (pointGraph G col).Adj x x' ∧ z x x' = α := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have hx6 : G.dist (w : V) x = 6 := (hd w x 3).mp hx
  have hα4 : G.dist (w : V) α = 4 := (hd w α 2).mp hα
  obtain ⟨mu, hxmu, hαmu⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn hxα
  obtain ⟨a', x', hNmu, -, hx', hx'x⟩ := far_lines F.moore col w x hx mu hxmu
  have hx'mu : G.Adj (x' : V) mu := by
    have h : (x' : V) ∈ G.neighborFinset mu := by rw [hNmu]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
  have hxx' : (pointGraph G col).Adj x x' := (hA _ _).mpr
    (dist_eq_two_of_adj_adj F.moore.conn col (fun h => hx'x (Subtype.ext h).symm)
      (x.2.trans x'.2.symm) hxmu hx'mu)
  refine ⟨x', hx', hxx', ?_⟩
  have hN := (F.data x hx x' hx' hxx').1 mu hxmu hx'mu
  have hzmu : G.Adj (z x x' : V) mu := by
    have h : (z x x' : V) ∈ G.neighborFinset mu := by rw [hN]; simp
    exact ((SimpleGraph.mem_neighborFinset _ _ _).mp h).symm
  obtain ⟨_m, -, -, -, -, hz4, -⟩ := F.edge hx hx' hxx'
  exact Subtype.ext (pred_unique F.moore.cyc F.moore.conn (k := 4) (by norm_num)
    (dist_eq_five_of_adj F.moore col hx6 hxmu) hzmu.symm hαmu.symm hz4 hα4)

end IsFrame

end CFSG.Combinatorics.HexagonPeriodicPropagation

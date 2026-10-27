module

public import CFSG.Combinatorics.PeriodicOppositeRecognition
public import CFSG.Combinatorics.OuterLayerPredecessorsSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation
  CFSG.Combinatorics.HexagonAlternatingOctagons CFSG.Combinatorics.AperiodicOppositeComponents
  CFSG.Combinatorics.PeriodicOppositeRecognition

namespace CFSG.Combinatorics.OuterLayer

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}

theorem edge_line (F : IsFrame G col w ℓ p z q c ε) {x y : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) (hy : (pointGraph G col).dist w y = 3)
    (hxy : (pointGraph G col).Adj x y) :
    ∃ m : V, G.neighborFinset m = {(x : V), (y : V), (z x y : V)} ∧ G.Adj (x : V) m ∧
      G.Adj (y : V) m ∧ G.Adj (z x y : V) m ∧ (pointGraph G col).dist w (z x y) = 2 := by
  obtain ⟨m, hN, xm, ym, zm, hz4, -⟩ := frame_edge F.moore col F.data hx hy hxy
  exact ⟨m, hN, xm, ym, zm, (point_dist_eq_iff F.moore.conn col w _ 2).mpr hz4⟩

theorem exists_edge_of_dist_two (F : IsFrame G col w ℓ p z q c ε) {t : {v : V // col v = false}}
    (ht : (pointGraph G col).dist w t = 2) :
    ∃ x y : {v : V // col v = false}, (pointGraph G col).dist w x = 3 ∧
      (pointGraph G col).dist w y = 3 ∧ (pointGraph G col).Adj x y ∧ z x y = t := by
  obtain ⟨D, tD, -, -, hother⟩ := inner_layer_lines F.moore col w (r := 2) (Or.inr rfl) t ht
  obtain ⟨L, hL, hLD⟩ := Finset.exists_mem_ne
    (show 1 < (G.neighborFinset (t : V)).card by
      rw [SimpleGraph.card_neighborFinset_eq_degree, F.moore.deg]
      norm_num) D
  have tL : G.Adj (t : V) L := (SimpleGraph.mem_neighborFinset _ _ _).mp hL
  obtain ⟨b, d, hN, hbd, hb, hd⟩ := hother L tL hLD
  have bL : G.Adj (b : V) L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have dL : G.Adj (d : V) L := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
  have hbd' : (pointGraph G col).Adj b d := (point_adj_iff F.moore.conn col b d).mpr
    (dist_eq_two_of_adj_adj F.moore.conn col (fun e => hbd (Subtype.ext e)) (b.2.trans d.2.symm)
      bL dL)
  refine ⟨b, d, hb, hd, hbd', ?_⟩
  obtain ⟨-, -, -, -, -, hz2⟩ := edge_line F hb hd hbd'
  have hzN : (z b d : V) ∈ G.neighborFinset L := by
    rw [(F.data b hb d hd hbd').1 L bL dL]
    simp
  rw [hN] at hzN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzN
  rcases hzN with h | h | h
  · exact Subtype.ext h
  · rw [Subtype.ext h] at hz2
    omega
  · rw [Subtype.ext h] at hz2
    omega

theorem third_eq_of_walk (F : IsFrame G col w ℓ p z q c ε)
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w x₀ = 3) (h₁ : (pointGraph G col).dist w x₁ = 3)
    (h₂ : (pointGraph G col).dist w x₂ = 3) (h₃ : (pointGraph G col).dist w x₃ = 3)
    (h₄ : (pointGraph G col).dist w x₄ = 3) (h₅ : (pointGraph G col).dist w x₅ = 3)
    (h₆ : (pointGraph G col).dist w x₆ = 3) (a₀ : (pointGraph G col).Adj x₀ x₁)
    (a₁ : (pointGraph G col).Adj x₁ x₂) (a₂ : (pointGraph G col).Adj x₂ x₃)
    (a₃ : (pointGraph G col).Adj x₃ x₄) (a₄ : (pointGraph G col).Adj x₄ x₅)
    (a₅ : (pointGraph G col).Adj x₅ x₆) (c₀ : c x₀ x₁ = k) (c₁ : c x₁ x₂ = i)
    (c₂ : c x₂ x₃ = j) (c₃ : c x₃ x₄ = i) (c₄ : c x₄ x₅ = j) (c₅ : c x₅ x₆ = k) :
    (∀ m m' : V, G.Adj (x₀ : V) m → G.Adj (x₁ : V) m → G.Adj (x₅ : V) m' →
      G.Adj (x₆ : V) m' → m ≠ m') ∧ z x₀ x₁ = z x₅ x₆ := by
  obtain ⟨r, hr'⟩ := exists_colour_moving G F.moore col w ℓ F.inj F.root p F.line F.ne F.label z q
    c ε F.data
  have hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
      (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i := fun i x hx => (hr' i x hx).1
  have hconn := (periodic_point_opposite_graph_recognition_and_automorphism_bound G F.moore col w
    ℓ F.inj F.root p F.line F.ne F.label z q c ε F.data hper).1
  have hQ : ∀ x (hx : (pointGraph G col).dist w x = 3),
      x ∈ compSet ((oppGraph G col w).connectedComponentMk ⟨x₀, h₀⟩) :=
    fun x hx => ⟨hx, SimpleGraph.ConnectedComponent.sound (hconn.preconnected _ _)⟩
  obtain ⟨y, hy, hyp⟩ := hper
  obtain ⟨-, hl, -, hz⟩ := (periodic_opposite_component_alternating_octagons_and_equal_third_points
    G F.moore col w ℓ F.inj F.root p F.line F.ne F.label z q c ε F.data r hr
    ((oppGraph G col w).connectedComponentMk ⟨x₀, h₀⟩)
    ⟨y, ⟨hy.1, fun n => hQ _ (hy.2.1 n), hy.2.2⟩, hyp⟩ i j k hij hjk hik).1
    x₀ (hQ x₀ h₀) x₁ (hQ x₁ h₁) x₂ (hQ x₂ h₂) x₃ (hQ x₃ h₃) x₄ (hQ x₄ h₄) x₅ (hQ x₅ h₅)
    x₆ (hQ x₆ h₆) a₀ a₁ a₂ a₃ a₄ a₅ c₀ c₁ c₂ c₃ c₄ c₅
  exact ⟨hl, hz⟩

theorem eq_of_third_eq (F : IsFrame G col w ℓ p z q c ε)
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : {v : V // col v = false}}
    (h₀ : (pointGraph G col).dist w x₀ = 3) (h₁ : (pointGraph G col).dist w x₁ = 3)
    (h₂ : (pointGraph G col).dist w x₂ = 3) (h₃ : (pointGraph G col).dist w x₃ = 3)
    (h₄ : (pointGraph G col).dist w x₄ = 3) (h₅ : (pointGraph G col).dist w x₅ = 3)
    (h₆ : (pointGraph G col).dist w x₆ = 3) (a₀ : (pointGraph G col).Adj x₀ x₁)
    (a₁ : (pointGraph G col).Adj x₁ x₂) (a₂ : (pointGraph G col).Adj x₂ x₃)
    (a₃ : (pointGraph G col).Adj x₃ x₄) (a₄ : (pointGraph G col).Adj x₄ x₅)
    (a₅ : (pointGraph G col).Adj x₅ x₆) (c₀ : c x₀ x₁ = k) (c₁ : c x₁ x₂ = i)
    (c₂ : c x₂ x₃ = j) (c₃ : c x₃ x₄ = i) (c₄ : c x₄ x₅ = j) (c₅ : c x₅ x₆ = k)
    {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y)
    (hz : z x y = z x₀ x₁) :
    (x = x₀ ∧ y = x₁ ∨ x = x₁ ∧ y = x₀) ∨ (x = x₅ ∧ y = x₆ ∨ x = x₆ ∧ y = x₅) := by
  obtain ⟨hl, hz5⟩ := third_eq_of_walk F hper hij hjk hik h₀ h₁ h₂ h₃ h₄ h₅ h₆ a₀ a₁ a₂ a₃ a₄ a₅
    c₀ c₁ c₂ c₃ c₄ c₅
  obtain ⟨L₀, hN₀, x₀L, x₁L, tL₀, ht⟩ := edge_line F h₀ h₁ a₀
  obtain ⟨L₅, hN₅, x₅L, x₆L, tL₅, -⟩ := edge_line F h₅ h₆ a₅
  obtain ⟨L, hN, xL, yL, tL, -⟩ := edge_line F hx hy hxy
  rw [← hz5] at hN₅ tL₅
  rw [hz] at hN tL
  obtain ⟨D, tD, -, ⟨a, s, hND, ha, hs, -⟩, -⟩ :=
    inner_layer_lines F.moore col w (r := 2) (Or.inr rfl) (z x₀ x₁) ht
  have hnotD : ∀ {M : V} {u : {v : V // col v = false}}, G.Adj (u : V) M →
      (pointGraph G col).dist w u = 3 → M ≠ D := by
    intro M u uM hu e
    rw [e] at uM
    have huN : (u : V) ∈ G.neighborFinset D := (SimpleGraph.mem_neighborFinset _ _ _).mpr uM.symm
    rw [hND] at huN
    simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    rcases huN with h | h | h <;> rw [Subtype.ext h] at hu <;> omega
  have h05 : L₀ ≠ L₅ := hl L₀ L₅ x₀L x₁L x₅L x₆L
  have hNt : G.neighborFinset (z x₀ x₁ : V) = {D, L₀, L₅} := neighborFinset_eq F.moore tD.symm
    tL₀.symm tL₅.symm (hnotD x₀L h₀).symm (hnotD x₅L h₅).symm h05
  have hLN : L ∈ G.neighborFinset (z x₀ x₁ : V) := (SimpleGraph.mem_neighborFinset _ _ _).mpr tL
  rw [hNt] at hLN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hLN
  have hpair : ∀ {M : V} {a₁ a₂ : {v : V // col v = false}},
      G.neighborFinset M = {(a₁ : V), (a₂ : V), (z x₀ x₁ : V)} → G.Adj (x : V) M →
        G.Adj (y : V) M → (x = a₁ ∧ y = a₂ ∨ x = a₂ ∧ y = a₁) := by
    intro M a₁ a₂ hM xM yM
    have hxN : (x : V) ∈ G.neighborFinset M := (SimpleGraph.mem_neighborFinset _ _ _).mpr xM.symm
    have hyN : (y : V) ∈ G.neighborFinset M := (SimpleGraph.mem_neighborFinset _ _ _).mpr yM.symm
    rw [hM] at hxN hyN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxN hyN
    have hxt : (x : V) ≠ z x₀ x₁ := fun e => by rw [Subtype.ext e] at hx; omega
    have hyt : (y : V) ≠ z x₀ x₁ := fun e => by rw [Subtype.ext e] at hy; omega
    have hne : x ≠ y := hxy.ne
    rcases hxN with h1 | h1 | h1 <;> rcases hyN with h2 | h2 | h2
    · exact absurd ((Subtype.ext h1).trans (Subtype.ext h2).symm) hne
    · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
    · exact absurd h2 hyt
    · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    · exact absurd ((Subtype.ext h1).trans (Subtype.ext h2).symm) hne
    · exact absurd h2 hyt
    · exact absurd h1 hxt
    · exact absurd h1 hxt
    · exact absurd h1 hxt
  rcases hLN with h | h | h
  · exact absurd h (hnotD xL hx)
  · rw [h] at xL yL
    exact Or.inl (hpair hN₀ xL yL)
  · rw [h] at xL yL
    exact Or.inr (hpair hN₅ xL yL)

theorem outerGraph_two_adj_iff (F : IsFrame G col w ℓ p z q c ε) {a b : {v : V // col v = false}}
    (ha : (pointGraph G col).dist w a = 3) (hb : (pointGraph G col).dist w b = 3) :
    (outerGraph G col w 2).Adj a b ↔ (pointGraph G col).Adj a b := by
  refine ⟨fun h => outerGraph_le 2 h, fun h => ?_⟩
  obtain ⟨m, hN, am, bm, -, hz⟩ := edge_line F ha hb h
  refine outerGraph_adj.mpr ⟨h.ne, m, ⟨col_eq_true_of_adj col a.2 am, fun u hu => ?_⟩, am, bm⟩
  have huN : (u : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
  rw [hN] at huN
  simp only [Finset.mem_insert, Finset.mem_singleton] at huN
  rcases huN with h' | h' | h' <;> rw [Subtype.ext h'] <;> omega

theorem outerGraph_two_adj_iff_mixed (F : IsFrame G col w ℓ p z q c ε)
    {a t : {v : V // col v = false}} (ha : (pointGraph G col).dist w a = 3)
    (ht : (pointGraph G col).dist w t = 2) :
    (outerGraph G col w 2).Adj a t ↔ ∃ y : {v : V // col v = false},
      (pointGraph G col).dist w y = 3 ∧ (pointGraph G col).Adj a y ∧ z a y = t := by
  constructor
  · intro h
    obtain ⟨hat, m, -, am, tm⟩ := outerGraph_adj.mp h
    obtain ⟨a', b', hN, ha', hb', hb'a⟩ := far_lines F.moore col w a ha m am
    have b'm : G.Adj (b' : V) m :=
      ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have hab' : (pointGraph G col).Adj a b' := (point_adj_iff F.moore.conn col a b').mpr
      (dist_eq_two_of_adj_adj F.moore.conn col (fun e => hb'a (Subtype.ext e).symm)
        (a.2.trans b'.2.symm) am b'm)
    refine ⟨b', hb', hab', ?_⟩
    have hzN : (z a b' : V) ∈ G.neighborFinset m := by
      rw [(F.data a ha b' hb' hab').1 m am b'm]
      simp
    have htN : (t : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr tm.symm
    obtain ⟨-, -, -, -, -, hz2⟩ := edge_line F ha hb' hab'
    rw [hN] at hzN htN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzN htN
    have e1 : z a b' = a' := by
      rcases hzN with h' | h' | h' <;> rw [Subtype.ext h'] at hz2
      · omega
      · exact Subtype.ext h'
      · omega
    have e2 : t = a' := by
      rcases htN with h' | h' | h' <;> rw [Subtype.ext h'] at ht
      · omega
      · exact Subtype.ext h'
      · omega
    rw [e1, e2]
  · rintro ⟨y, hy, hay, rfl⟩
    obtain ⟨m, hN, am, ym, zm, hz⟩ := edge_line F ha hy hay
    refine outerGraph_adj.mpr ⟨fun e => by rw [e, hz] at ha; omega, m,
      ⟨col_eq_true_of_adj col a.2 am, fun u hu => ?_⟩, am, zm⟩
    have huN : (u : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr hu.symm
    rw [hN] at huN
    simp only [Finset.mem_insert, Finset.mem_singleton] at huN
    rcases huN with h' | h' | h' <;> rw [Subtype.ext h'] <;> omega

theorem not_outerGraph_two_adj (H : MooreHyp G) {s t : {v : V // col v = false}}
    (hs : (pointGraph G col).dist w s = 2) (ht : (pointGraph G col).dist w t = 2) :
    ¬ (outerGraph G col w 2).Adj s t := by
  intro h
  obtain ⟨hst, m, hm, sm, tm⟩ := outerGraph_adj.mp h
  obtain ⟨D, -, hDchar, -, hother⟩ := inner_layer_lines H col w (r := 2) (Or.inr rfl) s hs
  by_cases hmD : m = D
  ·
    obtain ⟨u, um, hu⟩ := (hDchar m sm).mpr hmD
    have := hm.2 u um
    omega
  · obtain ⟨b, d, hN, -, hb, hd⟩ := hother m sm hmD
    have htN : (t : V) ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr tm.symm
    rw [hN] at htN
    simp only [Finset.mem_insert, Finset.mem_singleton] at htN
    rcases htN with h' | h' | h'
    · exact hst (Subtype.ext h').symm
    · rw [Subtype.ext h'] at ht
      omega
    · rw [Subtype.ext h'] at ht
      omega

end CFSG.Combinatorics.OuterLayer

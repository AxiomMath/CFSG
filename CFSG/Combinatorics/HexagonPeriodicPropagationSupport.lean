module

public import CFSG.Combinatorics.HexagonFourEdgePath

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonOppositeEdge CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.HexagonPeriodicPropagation

variable {V : Type*} [Fintype V] [DecidableEq V]

structure IsFrame (G : SimpleGraph V) [DecidableRel G.Adj] (col : G.Coloring Bool)
    (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (p : Fin 3 → Fin 2 → {v : V // col v = false})
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2) : Prop where
  moore : MooreHyp G
  inj : Function.Injective ℓ
  root : ∀ i, G.Adj (w : V) (ℓ i)
  line : ∀ i e, G.Adj (p i e : V) (ℓ i)
  ne : ∀ i e, p i e ≠ w
  label : ∀ i, Function.Injective (p i)
  data : IsFrameData G col w p z q c ε

omit [Fintype V] [DecidableEq V] in
abbrev IsHex (G : SimpleGraph V) (col : G.Coloring Bool) (w : {v : V // col v = false})
    (x : Fin 6 → {v : V // col v = false}) : Prop :=
  Function.Injective x ∧ (∀ n, (pointGraph G col).dist w (x n) = 3) ∧
    ∀ n, (pointGraph G col).Adj (x n) (x (n + 1))

omit [Fintype V] [DecidableEq V] in
abbrev IsPeriodic {col : V → Bool}
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (x : Fin 6 → {v : V // col v = false}) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n

omit [Fintype V] in
abbrev hexEdges {col : V → Bool} (x : Fin 6 → {v : V // col v = false}) :
    Finset (Sym2 {v : V // col v = false}) :=
  univ.image fun n => s(x n, x (n + 1))

theorem fin_three_cases {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (x : Fin 3) :
    x = i ∨ x = j ∨ x = k := by
  revert i j k x
  decide

theorem pattern_distinct (n : Fin 6) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ![i, j, k, i, j, k] n ≠ ![i, j, k, i, j, k] (n + 1) ∧
      ![i, j, k, i, j, k] (n + 1) ≠ ![i, j, k, i, j, k] (n + 2) ∧
      ![i, j, k, i, j, k] n ≠ ![i, j, k, i, j, k] (n + 2) := by
  revert n i j k
  decide

section Dihedral

variable {G : SimpleGraph V} {col : G.Coloring Bool} {w : {v : V // col v = false}}

omit [Fintype V] [DecidableEq V] in
theorem IsHex.rotate {x : Fin 6 → {v : V // col v = false}} (hx : IsHex G col w x) (k : Fin 6) :
    IsHex G col w (fun n => x (n + k)) := by
  refine ⟨fun a b h => add_right_cancel (hx.1 h), fun n => hx.2.1 _, fun n => ?_⟩
  have h := hx.2.2 (n + k)
  rwa [show n + k + 1 = n + 1 + k by abel] at h

omit [Fintype V] [DecidableEq V] in
theorem IsHex.reflect {x : Fin 6 → {v : V // col v = false}} (hx : IsHex G col w x) (k : Fin 6) :
    IsHex G col w (fun n => x (k - n)) := by
  refine ⟨fun a b h => sub_right_injective (hx.1 h), fun n => hx.2.1 _, fun n => ?_⟩
  have h := (hx.2.2 (k - (n + 1))).symm
  rwa [show k - (n + 1) + 1 = k - n by abel] at h

omit [Fintype V] in
theorem hexEdges_rotate (x : Fin 6 → {v : V // col v = false}) (k : Fin 6) :
    hexEdges (fun n => x (n + k)) = hexEdges x := by
  ext e
  simp only [hexEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n + k, by rw [show n + k + 1 = n + 1 + k by abel]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n - k, by rw [show n - k + k = n by abel, show n - k + 1 + k = n + 1 by abel]⟩

omit [Fintype V] in
theorem hexEdges_reflect (x : Fin 6 → {v : V // col v = false}) (k : Fin 6) :
    hexEdges (fun n => x (k - n)) = hexEdges x := by
  ext e
  simp only [hexEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨k - (n + 1), by rw [show k - (n + 1) + 1 = k - n by abel, Sym2.eq_swap]⟩
  · rintro ⟨n, rfl⟩
    exact ⟨k - (n + 1), by
      rw [show k - (k - (n + 1)) = n + 1 by abel, show k - (k - (n + 1) + 1) = n by abel,
        Sym2.eq_swap]⟩

omit [Fintype V] [DecidableEq V] in
theorem IsPeriodic.rotate {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
    {x : Fin 6 → {v : V // col v = false}} (hx : IsPeriodic c x) (k : Fin 6) :
    IsPeriodic c (fun n => x (n + k)) := by
  obtain ⟨i, j, l, hij, hjl, hil, h⟩ := hx
  have hv : ∀ n m : Fin 6, ![i, j, l, i, j, l] (n + m) =
      ![![i, j, l, i, j, l] m, ![i, j, l, i, j, l] (m + 1), ![i, j, l, i, j, l] (m + 2),
        ![i, j, l, i, j, l] m, ![i, j, l, i, j, l] (m + 1), ![i, j, l, i, j, l] (m + 2)] n := by
    intro n m
    fin_cases n <;> fin_cases m <;> rfl
  obtain ⟨d1, d2, d3⟩ := pattern_distinct k hij hjl hil
  refine ⟨![i, j, l, i, j, l] k, ![i, j, l, i, j, l] (k + 1), ![i, j, l, i, j, l] (k + 2),
    d1, d2, d3, fun n => ?_⟩
  show c (x (n + k)) (x (n + 1 + k)) = _
  rw [show n + 1 + k = n + k + 1 by abel, h (n + k), hv]

end Dihedral

namespace IsFrame

variable {G : SimpleGraph V} [DecidableRel G.Adj] {col : G.Coloring Bool}
  {w : {v : V // col v = false}} {ℓ : Fin 3 → V} {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  (F : IsFrame G col w ℓ p z q c ε)
include F

theorem symm {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y) : c y x = c x y :=
  (frame_symm F.moore col F.inj F.root F.line F.ne F.label F.data hx hy hxy).2.2.1

theorem unique {x y y' : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hy' : (pointGraph G col).dist w y' = 3)
    (hxy : (pointGraph G col).Adj x y) (hxy' : (pointGraph G col).Adj x y')
    (h : c x y = c x y') : y = y' :=
  frame_colour_unique F.moore col F.inj F.root F.line F.ne F.label F.data hx hy hy' hxy hxy' h

theorem exists_colour {x : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (i : Fin 3) :
    ∃ y, (pointGraph G col).dist w y = 3 ∧ (pointGraph G col).Adj x y ∧ c x y = i :=
  exists_adj_colour_eq F.moore col F.inj F.root F.line F.ne F.label F.data hx i

theorem no_triangle {a b d : {v : V // col v = false}} (ha : (pointGraph G col).dist w a = 3)
    (hb : (pointGraph G col).dist w b = 3) (hd : (pointGraph G col).dist w d = 3)
    (hab : (pointGraph G col).Adj a b) (hbd : (pointGraph G col).Adj b d)
    (hda : (pointGraph G col).Adj d a) : False := by
  have hD := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  exact no_far_triangle F.moore col ((hD w a 3).mp ha) ((hD w b 3).mp hb) ((hD w d 3).mp hd)
    ((hA a b).mp hab) ((hA b d).mp hbd) ((hA d a).mp hda)

theorem no_square {a b d e : {v : V // col v = false}} (ha : (pointGraph G col).dist w a = 3)
    (hb : (pointGraph G col).dist w b = 3) (hd : (pointGraph G col).dist w d = 3)
    (he : (pointGraph G col).dist w e = 3) (hab : (pointGraph G col).Adj a b)
    (hbd : (pointGraph G col).Adj b d) (hde : (pointGraph G col).Adj d e)
    (hea : (pointGraph G col).Adj e a) (had : a ≠ d) (hbe : b ≠ e) : False := by
  have hD := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  exact no_far_square F.moore col ((hD w a 3).mp ha) ((hD w b 3).mp hb) ((hD w d 3).mp hd)
    ((hD w e 3).mp he) ((hA a b).mp hab) ((hA b d).mp hbd) ((hA d e).mp hde) ((hA e a).mp hea)
    (fun h => had (Subtype.ext h)) (fun h => hbe (Subtype.ext h))

theorem count_hex {x : Fin 6 → {v : V // col v = false}} (hx : IsHex G col w x) (i : Fin 3) :
    (if c (x 0) (x 1) = i then 1 else 0) + (if c (x 1) (x 2) = i then 1 else 0) +
      (if c (x 2) (x 3) = i then 1 else 0) + (if c (x 3) (x 4) = i then 1 else 0) +
      (if c (x 4) (x 5) = i then 1 else 0) + (if c (x 5) (x 0) = i then 1 else 0) = 2 := by
  have h := six_cycle_colours F.moore col F.inj F.root F.line F.ne F.label F.data hx.1 hx.2.1
    hx.2.2 i
  rw [Finset.card_filter, Fin.sum_univ_six] at h
  exact h

theorem complete {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {v₀ v₁ v₂ v₃ v₄ : {v : V // col v = false}} (h₀ : (pointGraph G col).dist w v₀ = 3)
    (h₁ : (pointGraph G col).dist w v₁ = 3) (h₂ : (pointGraph G col).dist w v₂ = 3)
    (h₃ : (pointGraph G col).dist w v₃ = 3) (h₄ : (pointGraph G col).dist w v₄ = 3)
    (h01 : (pointGraph G col).Adj v₀ v₁) (h12 : (pointGraph G col).Adj v₁ v₂)
    (h23 : (pointGraph G col).Adj v₂ v₃) (h34 : (pointGraph G col).Adj v₃ v₄)
    (hnd : [v₀, v₁, v₂, v₃, v₄].Nodup) (hc₀ : c v₀ v₁ = i) (hc₁ : c v₁ v₂ = j)
    (hc₂ : c v₂ v₃ = k) (hc₃ : c v₃ v₄ = i) :
    ∃ u, ((pointGraph G col).dist w u = 3 ∧ (pointGraph G col).Adj v₀ u ∧
        (pointGraph G col).Adj v₄ u) ∧
      (∀ u', (pointGraph G col).dist w u' = 3 → (pointGraph G col).Adj v₀ u' →
        (pointGraph G col).Adj v₄ u' → u' = u) ∧
      [v₀, v₁, v₂, v₃, v₄, u].Nodup ∧ ((c v₄ u = j ∧ c u v₀ = k) ∨ (c v₄ u = k ∧ c u v₀ = j)) :=
  (opposite_four_edge_path_completion_and_six_cycle_color_counts G F.moore col w ℓ F.inj F.root p
    F.line F.ne F.label z q c ε F.data).2 i j k hij hjk hik v₀ h₀ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ h01 h12
    h23 h34 hnd hc₀ hc₁ hc₂ hc₃

theorem periodic_reflect {x : Fin 6 → {v : V // col v = false}} (hx : IsHex G col w x)
    (hp : IsPeriodic c x) (k : Fin 6) : IsPeriodic c (fun n => x (k - n)) := by
  obtain ⟨i, j, l, hij, hjl, hil, h⟩ := hp
  have hv : ∀ n m : Fin 6, ![i, j, l, i, j, l] (m - (n + 1)) =
      ![![i, j, l, i, j, l] (m + 2), ![i, j, l, i, j, l] (m + 1), ![i, j, l, i, j, l] m,
        ![i, j, l, i, j, l] (m + 2), ![i, j, l, i, j, l] (m + 1), ![i, j, l, i, j, l] m] n := by
    intro n m
    fin_cases n <;> fin_cases m <;> rfl
  obtain ⟨d1, d2, d3⟩ := pattern_distinct k hij hjl hil
  refine ⟨![i, j, l, i, j, l] (k + 2), ![i, j, l, i, j, l] (k + 1), ![i, j, l, i, j, l] k,
    d2.symm, d1.symm, d3.symm, fun n => ?_⟩
  show c (x (k - n)) (x (k - (n + 1))) = _
  have hadj := hx.2.2 (k - (n + 1))
  rw [show k - (n + 1) + 1 = k - n by abel] at hadj
  have h' := h (k - (n + 1))
  rw [show k - (n + 1) + 1 = k - n by abel] at h'
  rw [F.symm (hx.2.1 _) (hx.2.1 _) hadj, h', hv]

end IsFrame

end CFSG.Combinatorics.HexagonPeriodicPropagation

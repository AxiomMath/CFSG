module

public import CFSG.Combinatorics.HexagonLayers
public import Mathlib.Algebra.Order.Group.Action.End

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers

namespace CFSG.Combinatorics.HexagonStabilizerFaithful

variable {V : Type*}

section Parts

variable (G : SimpleGraph V) (col : G.Coloring Bool)

@[expose] def partAut : Subgroup (G ≃g G) where
  carrier := {f | ∀ v, col (f v) = col v}
  mul_mem' {f g} hf hg v := (hf (g v)).trans (hg v)
  one_mem' _ := rfl
  inv_mem' {f} hf v := by
    have h := hf (f⁻¹ v)
    rw [RelIso.apply_inv_self] at h
    exact h.symm

variable {G col}

theorem mem_partAut {f : G ≃g G} : f ∈ partAut G col ↔ ∀ v, col (f v) = col v :=
  Iff.rfl

theorem mem_partAut_iff_image (f : G ≃g G) :
    f ∈ partAut G col ↔ f '' {v | col v = false} = {v | col v = false} ∧
      f '' {v | col v = true} = {v | col v = true} := by
  rw [mem_partAut]
  constructor
  · intro hf
    have himg : ∀ b : Bool, f '' {v | col v = b} = {v | col v = b} := by
      intro b
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hf x, hx]
      · intro hy
        refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
        rw [← hf (f.symm y), f.apply_symm_apply]
        exact hy
    exact ⟨himg false, himg true⟩
  · rintro ⟨hP, hL⟩ v
    have key : ∀ b : Bool, f '' {v | col v = b} = {v | col v = b} → col v = b →
        col (f v) = b := by
      intro b hb hv
      have h : f v ∈ f '' {v | col v = b} := Set.mem_image_of_mem f hv
      rw [hb] at h
      exact h
    cases hv : col v
    · exact key false hP hv
    · exact key true hL hv

theorem exists_line_map_iff {f : G ≃g G} (hf : f ∈ partAut G col) (a b : V) :
    (∃ ℓ : V, col ℓ = true ∧ G.Adj (f a) ℓ ∧ G.Adj (f b) ℓ) ↔
      ∃ ℓ : V, col ℓ = true ∧ G.Adj a ℓ ∧ G.Adj b ℓ := by
  rw [mem_partAut] at hf
  constructor
  · rintro ⟨ℓ, hℓ, ha, hb⟩
    refine ⟨f.symm ℓ, ?_, ?_, ?_⟩
    · rw [← hf (f.symm ℓ), f.apply_symm_apply]
      exact hℓ
    · rw [← f.map_adj_iff, f.apply_symm_apply]
      exact ha
    · rw [← f.map_adj_iff, f.apply_symm_apply]
      exact hb
  · rintro ⟨ℓ, hℓ, ha, hb⟩
    exact ⟨f ℓ, (hf ℓ).trans hℓ, f.map_adj_iff.mpr ha, f.map_adj_iff.mpr hb⟩

variable (G col)

@[expose] def pointAut (f : partAut G col) : pointGraph G col ≃g pointGraph G col where
  toEquiv := (f : G ≃g G).toEquiv.subtypeEquiv fun v => by
    change col v = false ↔ col ((f : G ≃g G) v) = false
    rw [mem_partAut.mp f.2 v]
  map_rel_iff' {a b} := by
    rw [SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    refine and_congr ?_ (or_congr (exists_line_map_iff f.2 (a : V) b)
      (exists_line_map_iff f.2 (b : V) a))
    exact (Equiv.injective _).ne_iff

theorem pointAut_apply (f : partAut G col) (x : {v : V // col v = false}) :
    (pointAut G col f x : V) = (f : G ≃g G) x :=
  rfl

end Parts

theorem dist_iso_le {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'} (φ : H ≃g H')
    (u v : W) : H'.dist (φ u) (φ v) ≤ H.dist u v := by
  by_cases h : H.Reachable u v
  · obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    calc H'.dist (φ u) (φ v) ≤ (p.map φ.toHom).length := SimpleGraph.dist_le _
      _ = H.dist u v := by rw [SimpleGraph.Walk.length_map, hp]
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable
      (fun h' => h (SimpleGraph.Iso.reachable_iff.mp h'))]
    exact Nat.zero_le _

theorem dist_iso {W W' : Type*} {H : SimpleGraph W} {H' : SimpleGraph W'} (φ : H ≃g H')
    (u v : W) : H'.dist (φ u) (φ v) = H.dist u v := by
  refine le_antisymm (dist_iso_le φ u v) ?_
  have h := dist_iso_le φ.symm (φ u) (φ v)
  rwa [RelIso.symm_apply_apply, RelIso.symm_apply_apply] at h

theorem dist_iso_of_fixed {W : Type*} {H : SimpleGraph W} (φ : H ≃g H) {a : W} (ha : φ a = a)
    (x : W) : H.dist a (φ x) = H.dist a x := by
  calc H.dist a (φ x) = H.dist (φ a) (φ x) := by rw [ha]
    _ = H.dist a x := dist_iso φ a x

variable (G : SimpleGraph V) (col : G.Coloring Bool)

theorem pointAut_stab {w : {v : V // col v = false}}
    (g : MulAction.stabilizer (partAut G col) (w : V)) : pointAut G col g w = w :=
  Subtype.ext (MulAction.mem_stabilizer_iff.mp g.2)

@[expose] def oppositeRestriction (w : {v : V // col v = false}) :
    MulAction.stabilizer (partAut G col) (w : V) →*
      ((pointGraph G col).induce {x | (pointGraph G col).dist w x = 3} ≃g
        (pointGraph G col).induce {x | (pointGraph G col).dist w x = 3}) where
  toFun g :=
    { toEquiv := (pointAut G col g).toEquiv.subtypeEquiv fun x => by
        change (pointGraph G col).dist w x = 3 ↔
          (pointGraph G col).dist w (pointAut G col g x) = 3
        rw [dist_iso_of_fixed _ (pointAut_stab G col g)]
      map_rel_iff' {a b} := (pointAut G col g).map_adj_iff (v := (a : _)) (w := (b : _)) }
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

theorem oppositeRestriction_apply (w : {v : V // col v = false})
    (g : MulAction.stabilizer (partAut G col) (w : V))
    (x : {x | (pointGraph G col).dist w x = 3}) :
    ((oppositeRestriction G col w g x : {v : V // col v = false}) : V) =
      ((g : partAut G col) : G ≃g G) x :=
  rfl

variable {G col}

theorem exists_frame_labels [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3)
    (w : {v : V // col v = false}) :
    ∃ (ℓ : Fin 3 → V) (p : Fin 3 → Fin 2 → {v : V // col v = false}), Function.Injective ℓ ∧
      (∀ i, G.Adj (w : V) (ℓ i)) ∧ (∀ i e, G.Adj (p i e : V) (ℓ i)) ∧ (∀ i e, p i e ≠ w) ∧
      ∀ i, Function.Injective (p i) := by
  classical
  have h3 : (G.neighborFinset (w : V)).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Finset.card_eq_three.mp h3
  have hwa : G.Adj (w : V) a := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hwb : G.Adj (w : V) b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hwc : G.Adj (w : V) c := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hℓ : Function.Injective ![a, b, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij hab | exact absurd hij hac | exact absurd hij hbc
      | exact absurd hij.symm hab | exact absurd hij.symm hac | exact absurd hij.symm hbc
  have hwℓ : ∀ i, G.Adj (w : V) (![a, b, c] i) := by
    intro i
    fin_cases i
    exacts [hwa, hwb, hwc]
  have hpts : ∀ i, ∃ x y : V, x ≠ y ∧ G.Adj x (![a, b, c] i) ∧ G.Adj y (![a, b, c] i) ∧
      x ≠ w ∧ y ≠ w := by
    intro i
    have h2 : ((G.neighborFinset (![a, b, c] i)).erase (w : V)).card = 2 := by
      rw [Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).mpr (hwℓ i).symm),
        SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    obtain ⟨x, y, hxy, hE⟩ := Finset.card_eq_two.mp h2
    have hx : x ∈ (G.neighborFinset (![a, b, c] i)).erase (w : V) := by rw [hE]; simp
    have hy : y ∈ (G.neighborFinset (![a, b, c] i)).erase (w : V) := by rw [hE]; simp
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hx hy
    exact ⟨x, y, hxy, hx.2.symm, hy.2.symm, hx.1, hy.1⟩
  choose x y hxy hx hy hxw hyw using hpts
  have hcol : ∀ i {u : V}, G.Adj u (![a, b, c] i) → col u = false := fun i _ hu =>
    col_eq_false_of_adj col (col_eq_true_of_adj col w.2 (hwℓ i)) hu
  refine ⟨![a, b, c], fun i => ![⟨x i, hcol i (hx i)⟩, ⟨y i, hcol i (hy i)⟩], hℓ, hwℓ, ?_, ?_, ?_⟩
  · intro i e
    fin_cases e
    exacts [hx i, hy i]
  · intro i e
    fin_cases e
    · exact fun h => hxw i (congrArg Subtype.val h)
    · exact fun h => hyw i (congrArg Subtype.val h)
  · intro i e f hef
    fin_cases e <;> fin_cases f
    · rfl
    · exact absurd (congrArg Subtype.val hef) (hxy i)
    · exact absurd (congrArg Subtype.val hef).symm (hxy i)
    · rfl

theorem eq_of_adj_adj (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    {a b m m' : V} (hab : a ≠ b) (ham : G.Adj a m) (hbm : G.Adj b m) (ham' : G.Adj a m')
    (hbm' : G.Adj b m') : m = m' := by
  by_contra hne
  have hc : (SimpleGraph.Walk.cons ham (SimpleGraph.Walk.cons hbm.symm (SimpleGraph.Walk.cons
      hbm' (SimpleGraph.Walk.cons ham'.symm SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    simp [ham.ne, ham.ne.symm, hbm.ne.symm, hbm'.ne, ham'.ne.symm, ham'.ne, hab, hab.symm, hne]
  have h := hcyc a _ hc
  simp at h

theorem exists_adj_ne [Fintype V] [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 3) (x m : V) :
    ∃ m', G.Adj x m' ∧ m' ≠ m := by
  classical
  have h3 : (G.neighborFinset x).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨a, b, _c, hab, -, -, hN⟩ := Finset.card_eq_three.mp h3
  have ha : G.Adj x a := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  have hb : G.Adj x b := (SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)
  by_cases ham : a = m
  · exact ⟨b, hb, fun hbm => hab (ham.trans hbm.symm)⟩
  · exact ⟨a, ha, ham⟩

theorem fix_third [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length) (g : G ≃g G) {x b c m : V}
    (hN : G.neighborFinset m = {x, b, c}) (hbc : b ≠ c) (hb : g b = b) (hc : g c = c) :
    g x = x := by
  have hadj : ∀ {u : V}, u ∈ G.neighborFinset m → G.Adj u m := fun hu =>
    ((SimpleGraph.mem_neighborFinset _ _ _).mp hu).symm
  have hxm : G.Adj x m := hadj (by rw [hN]; simp)
  have hbm : G.Adj b m := hadj (by rw [hN]; simp)
  have hcm : G.Adj c m := hadj (by rw [hN]; simp)
  have hgm : g m = m := by
    have hb' : G.Adj b (g m) := by
      rw [← hb]
      exact g.map_adj_iff.mpr hbm
    have hc' : G.Adj c (g m) := by
      rw [← hc]
      exact g.map_adj_iff.mpr hcm
    exact (eq_of_adj_adj hcyc hbc hbm hcm hb' hc').symm
  have hgx : g x ∈ G.neighborFinset m := by
    rw [SimpleGraph.mem_neighborFinset, ← hgm]
    exact (g.map_adj_iff.mpr hxm).symm
  rw [hN] at hgx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgx
  rcases hgx with h | h | h
  · exact h
  · rw [h, g.injective (h.trans hb.symm)]
  · rw [h, g.injective (h.trans hc.symm)]

theorem eq_one_of_fix_opposite [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcard : Fintype.card V = 126) (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false}) (g : G ≃g G) (hgw : g w = w)
    (hO : ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x = 3 → g x = x) :
    g = 1 := by
  obtain ⟨ℓ, p, hℓ, hwℓ, hpℓ, hpw, hp⟩ := exists_frame_labels hdeg w
  obtain ⟨⟨-, hle⟩, hlines, -⟩ := order_two_hexagon_layers_and_opposite_edge_coordinates G hcard
    hconn hdeg col hcyc w ℓ hℓ hwℓ p hpℓ hpw hp
  have hstep : ∀ r : ℕ, (r = 1 ∨ r = 2) →
      (∀ y : {v : V // col v = false}, (pointGraph G col).dist w y = r + 1 → g y = y) →
      ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x = r → g x = x := by
    intro r hr hfix x hx
    obtain ⟨m, -, -, -, hother⟩ := hlines r hr x hx
    obtain ⟨m', hxm', hne⟩ := exists_adj_ne hdeg (x : V) m
    obtain ⟨b, c, hN, hbc, hb, hc⟩ := hother m' hxm' hne
    exact fix_third hcyc g hN (fun h => hbc (Subtype.ext h)) (hfix b hb) (hfix c hc)
  have h2 := hstep 2 (Or.inr rfl) hO
  have h1 := hstep 1 (Or.inl rfl) h2
  have hpt : ∀ x : {v : V // col v = false}, g x = x := by
    intro x
    have hx := hle x
    rcases (by omega : (pointGraph G col).dist w x = 0 ∨ (pointGraph G col).dist w x = 1 ∨
      (pointGraph G col).dist w x = 2 ∨ (pointGraph G col).dist w x = 3) with h | h | h | h
    · have hwx : (w : V) = x :=
        hconn.dist_eq_zero_iff.mp ((point_dist_eq_iff hconn col w x 0).mp h)
      rw [← hwx, hgw]
    · exact h1 x h
    · exact h2 x h
    · exact hO x h
  have hline : ∀ v : V, col v = true → g v = v := by
    intro v hv
    have h3 : (G.neighborFinset v).card = 3 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
    obtain ⟨a, b, _c, hab, -, -, hN⟩ := Finset.card_eq_three.mp h3
    have ha : G.Adj a v := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have hb : G.Adj b v := ((SimpleGraph.mem_neighborFinset _ _ _).mp (by rw [hN]; simp)).symm
    have hga : g a = a := hpt ⟨a, col_eq_false_of_adj col hv ha⟩
    have hgb : g b = b := hpt ⟨b, col_eq_false_of_adj col hv hb⟩
    have ha' : G.Adj a (g v) := by
      rw [← hga]
      exact g.map_adj_iff.mpr ha
    have hb' : G.Adj b (g v) := by
      rw [← hgb]
      exact g.map_adj_iff.mpr hb
    exact (eq_of_adj_adj hcyc hab ha hb ha' hb').symm
  ext v
  change g v = v
  cases hv : col v
  · exact hpt ⟨v, hv⟩
  · exact hline v hv

variable (G col)

theorem oppositeRestriction_injective [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcard : Fintype.card V = 126) (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false}) : Function.Injective (oppositeRestriction G col w) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x = 3 →
      ((g : partAut G col) : G ≃g G) x = x := fun x hx =>
    congrArg (fun φ => ((φ ⟨x, hx⟩ : {v : V // col v = false}) : V)) hg
  exact Subtype.ext (Subtype.ext (eq_one_of_fix_opposite hcard hconn hdeg hcyc w _
    (MulAction.mem_stabilizer_iff.mp g.2) hfix))

end CFSG.Combinatorics.HexagonStabilizerFaithful

module

public import CFSG.Combinatorics.HexagonLayersPoints
public import CFSG.Combinatorics.CubicBipartiteMoore

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore

namespace CFSG.Combinatorics.HexagonLayers

theorem order_two_hexagon_layers_and_opposite_edge_coordinates {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcard : Fintype.card V = 126)
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v = 3) (col : G.Coloring Bool)
    (hcyc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 12 ≤ c.length)
    (w : {v : V // col v = false}) (ℓ : Fin 3 → V) (hℓ : Function.Injective ℓ)
    (hwℓ : ∀ i, G.Adj (w : V) (ℓ i)) (p : Fin 3 → Fin 2 → {v : V // col v = false})
    (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i)) (hpw : ∀ i e, p i e ≠ w)
    (hp : ∀ i, Function.Injective (p i)) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    ((∀ k : Fin 4, (univ.filter fun x => Γ.dist w x = k).card = ![1, 6, 24, 32] k) ∧
      ∀ x, Γ.dist w x ≤ 3) ∧
    (∀ r : ℕ, (r = 1 ∨ r = 2) → ∀ x, Γ.dist w x = r →
      ∃ m : V, G.Adj (x : V) m ∧
        (∀ m' : V, G.Adj (x : V) m' →
          ((∃ y : {v : V // col v = false}, G.Adj (y : V) m' ∧ Γ.dist w y = r - 1) ↔ m' = m)) ∧
        (∃ a t : {v : V // col v = false}, G.neighborFinset m = {(x : V), (a : V), (t : V)} ∧
          Γ.dist w a = r - 1 ∧ Γ.dist w t = r ∧ t ≠ x) ∧
        ∀ m' : V, G.Adj (x : V) m' → m' ≠ m → ∃ b c : {v : V // col v = false},
          G.neighborFinset m' = {(x : V), (b : V), (c : V)} ∧ b ≠ c ∧
            Γ.dist w b = r + 1 ∧ Γ.dist w c = r + 1) ∧
    (∀ x ∈ O, ∀ m : V, G.Adj (x : V) m → ∃ a b : {v : V // col v = false},
      G.neighborFinset m = {(x : V), (a : V), (b : V)} ∧ Γ.dist w a = 2 ∧ b ∈ O ∧ b ≠ x) ∧
    (∀ s : {v : V // col v = false}, Γ.dist w s = 1 ↔ ∃! ie : Fin 3 × Fin 2, p ie.1 ie.2 = s) ∧
    ∃ (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
      (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
      (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
      (r : Fin 3 → {v : V // col v = false} → {v : V // col v = false})
      (lam : {v : V // col v = false} → Fin 3 → Fin 2),
      (∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y →
        (∃! m : V, G.Adj (x : V) m ∧ G.Adj (y : V) m) ∧
        (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
          G.neighborFinset m = {(x : V), (y : V), (z x y : V)}) ∧
        Γ.dist w (z x y) = 2 ∧
        (∀ t, Γ.Adj (z x y) t ∧ Γ.dist w t = 1 ↔ t = q x y) ∧
        q x y = p (c x y) (ε x y)) ∧
      (∀ x ∈ O, (univ.filter fun y => y ∈ O ∧ Γ.Adj x y).card = 3 ∧
        ∀ i : Fin 3, ∃! y, y ∈ O ∧ Γ.Adj x y ∧ c x y = i) ∧
      (∀ (i : Fin 3), ∀ x ∈ O,
        r i x ∈ O ∧ Γ.Adj x (r i x) ∧ c x (r i x) = i ∧ r i (r i x) = x ∧ r i x ≠ x) ∧
      (∀ x ∈ O, ∀ i j : Fin 3, i ≠ j → r i x ≠ r j x) ∧
      (∀ (v : O) (cy : (Γ.induce O).Walk v v), cy.IsCycle →
        cy.length ≠ 3 ∧ cy.length ≠ 4 ∧ cy.length ≠ 5) ∧
      (∀ x ∈ O, ∀ i : Fin 3, (∃! e : Fin 2, Γ.dist x (p i e) = 2) ∧
        Γ.dist x (p i (lam x i)) = 2 ∧ (∀ e, e ≠ lam x i → Γ.dist x (p i e) = 3) ∧
        Γ.dist x w = 3) ∧
      (∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y →
        lam x (c x y) = ε x y ∧ lam y (c x y) = ε x y ∧
          ∀ j : Fin 3, j ≠ c x y → lam x j ≠ lam y j) := by
  intro Γ O
  have H : MooreHyp G := ⟨hcard, hconn, hdeg, hcyc⟩
  have hd : ∀ (a b : {v : V // col v = false}) (k : ℕ),
      Γ.dist a b = k ↔ G.dist (a : V) b = 2 * k := point_dist_eq_iff hconn col
  have hA : ∀ a b : {v : V // col v = false}, Γ.Adj a b ↔ G.dist (a : V) b = 2 :=
    point_adj_iff hconn col
  have hO : ∀ x : {v : V // col v = false}, x ∈ O ↔ G.dist (w : V) x = 6 := fun x => hd w x 3
  obtain ⟨-, -, -, -, -, -, -, hlay, -, -, -, -⟩ :=
    cubic_bipartite_moore_equality_and_nearest_point_property G hcard hconn hdeg col hcyc
  have hlabel : ∀ s : {v : V // col v = false}, ∃ ie : Fin 3 × Fin 2,
      Γ.dist w s = 1 → s = p ie.1 ie.2 := by
    intro s
    by_cases hs : Γ.dist w s = 1
    · obtain ⟨i, e, h⟩ := exists_label H col hℓ hwℓ hpℓ hpw hp ((hd w s 1).mp hs)
      exact ⟨(i, e), fun _ => (Subtype.ext h).symm⟩
    · exact ⟨(0, 0), fun h => absurd h hs⟩
  choose lab hlab using hlabel
  have hthird : ∀ x y : {v : V // col v = false}, ∃ t : {v : V // col v = false},
      x ∈ O → y ∈ O → Γ.Adj x y →
        (∀ m : V, G.Adj (x : V) m → G.Adj (y : V) m →
          G.neighborFinset m = {(x : V), (y : V), (t : V)}) ∧ Γ.dist w t = 2 := by
    intro x y
    by_cases h : x ∈ O ∧ y ∈ O ∧ Γ.Adj x y
    · obtain ⟨t, ht⟩ := third_point H col w h.1 h.2.1 h.2.2
      exact ⟨t, fun _ _ _ => ht⟩
    · exact ⟨x, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z hz using hthird
  have hbelow : ∀ t : {v : V // col v = false}, ∃ s : {v : V // col v = false},
      Γ.dist w t = 2 → ∀ s', Γ.Adj t s' ∧ Γ.dist w s' = 1 ↔ s' = s := by
    intro t
    by_cases ht : Γ.dist w t = 2
    · obtain ⟨s, hs⟩ := exists_unique_lower_point H col w ht
      exact ⟨s, fun _ => hs⟩
    · exact ⟨t, fun h => absurd h ht⟩
  choose q₀ hq₀ using hbelow
  obtain ⟨c, hc⟩ : ∃ c : {v : V // col v = false} → {v : V // col v = false} → Fin 3,
      ∀ x y, c x y = (lab (q₀ (z x y))).1 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2,
      ∀ x y, ε x y = (lab (q₀ (z x y))).2 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : {v : V // col v = false} → Fin 3 → Fin 2,
      ∀ x i, lam x i = if Γ.dist x (p i 0) = 2 then 0 else 1 := ⟨_, fun _ _ => rfl⟩
  have hedge : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → Γ.dist w (q₀ (z x y)) = 1 ∧
      Γ.Adj (z x y) (q₀ (z x y)) ∧ q₀ (z x y) = p (c x y) (ε x y) := by
    intro x hx y hy hxy
    have h1 := ((hq₀ (z x y) (hz x y hx hy hxy).2) (q₀ (z x y))).mpr rfl
    refine ⟨h1.2, h1.1, ?_⟩
    rw [hc, hε]
    exact hlab _ h1.2
  have hedgeG : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → ∃ m : V, G.Adj (x : V) m ∧ G.Adj (y : V) m ∧
      G.Adj (z x y : V) m ∧ G.dist (w : V) (z x y) = 4 ∧
      G.dist (z x y : V) (p (c x y) (ε x y)) = 2 ∧ G.dist (w : V) (p (c x y) (ε x y)) = 2 := by
    intro x hx y hy hxy
    obtain ⟨m, ⟨hxm, hym⟩, -⟩ := exists_unique_common_line H col hxy
    obtain ⟨hN, hz2⟩ := hz x y hx hy hxy
    obtain ⟨h1, h2, h3⟩ := hedge x hx y hy hxy
    have hzm : G.Adj (z x y : V) m := by
      have : (z x y : V) ∈ G.neighborFinset m := by rw [hN m hxm hym]; simp
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp this).symm
    refine ⟨m, hxm, hym, hzm, (hd w _ 2).mp hz2, ?_, ?_⟩
    · rw [← h3]
      exact (hA _ _).mp h2
    · rw [← h3]
      exact (hd w _ 1).mp h1
  have hfour : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y →
      G.dist (x : V) (p (c x y) (ε x y)) = 4 ∧ G.dist (y : V) (p (c x y) (ε x y)) = 4 := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hym, hzm, -, h2, h3⟩ := hedgeG x hx y hy hxy
    exact ⟨dist_eq_four_of_lower H ((hO x).mp hx) hxm hzm h3 h2,
      dist_eq_four_of_lower H ((hO y).mp hy) hym hzm h3 h2⟩
  have hbits : ∀ x ∈ O, ∀ i : Fin 3,
      (Γ.dist x (p i 0) = 2 ∧ Γ.dist x (p i 1) = 3) ∨
        (Γ.dist x (p i 0) = 3 ∧ Γ.dist x (p i 1) = 2) :=
    fun x hx i => bits H col hwℓ hpℓ hpw hp hx i
  have h23 : ∀ x ∈ O, ∀ (i : Fin 3) (e : Fin 2),
      Γ.dist x (p i e) = 2 ∨ Γ.dist x (p i e) = 3 := by
    intro x hx i e
    rcases hbits x hx i with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases e <;> simp [h0, h1]
  have hbit : ∀ x ∈ O, ∀ (i : Fin 3) (e : Fin 2), Γ.dist x (p i e) = 2 ↔ e = lam x i := by
    intro x hx i e
    rw [hlam]
    rcases hbits x hx i with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases e <;> simp [h0, h1]
  have hcol_ex : ∀ x ∈ O, ∀ i : Fin 3, ∃ y, y ∈ O ∧ Γ.Adj x y ∧ c x y = i := by
    intro x hx i
    have hx6 := (hO x).mp hx
    have hq2 : G.dist (w : V) (p i (lam x i)) = 2 := dist_label H col hwℓ hpℓ hpw i _
    have hxq : G.dist (x : V) (p i (lam x i)) = 4 := (hd x _ 2).mp ((hbit x hx i _).mpr rfl)
    obtain ⟨m, y, t, hxm, hym, htm, hyx, hy, ht, htq⟩ := exists_far_edge H col hx6 hq2 hxq
    obtain ⟨y, rfl⟩ : ∃ y' : {v : V // col v = false}, (y' : V) = y :=
      ⟨⟨y, col_eq_false_of_adj col (col_eq_true_of_adj col x.2 hxm) hym⟩, rfl⟩
    have hyO : y ∈ O := (hO y).mpr hy
    have hxy : Γ.Adj x y := (hA x y).mpr
      (dist_eq_two_of_adj_adj hconn col (fun h => hyx h.symm) (x.2.trans y.2.symm) hxm hym)
    refine ⟨y, hyO, hxy, ?_⟩
    obtain ⟨hN, hz2⟩ := hz x y hx hyO hxy
    have htN : t ∈ G.neighborFinset m := (SimpleGraph.mem_neighborFinset _ _ _).mpr htm.symm
    rw [hN m hxm hym] at htN
    simp only [Finset.mem_insert, Finset.mem_singleton] at htN
    have htz : t = (z x y : V) := by
      rcases htN with h | h | h
      · rw [h] at ht
        omega
      · rw [h] at ht
        omega
      · exact h
    have hpz := (hq₀ (z x y) hz2 (p i (lam x i))).mp
      ⟨(hA _ _).mpr (by rw [← htz]; exact htq), (hd w _ 1).mpr hq2⟩
    obtain ⟨-, -, h3⟩ := hedge x hx y hyO hxy
    rw [← hpz] at h3
    exact ((label_injective H col hℓ hwℓ hpℓ hpw hp h3).1).symm
  have hcol_un : ∀ x ∈ O, ∀ y ∈ O, ∀ y' ∈ O, Γ.Adj x y → Γ.Adj x y' → c x y = c x y' →
      y = y' := by
    intro x hx y hy y' hy' hxy hxy' hcc
    have hx6 := (hO x).mp hx
    obtain ⟨m, hxm, hym, hzm, -, h2, h3⟩ := hedgeG x hx y hy hxy
    obtain ⟨m', hxm', hym', hzm', -, h2', h3'⟩ := hedgeG x hx y' hy' hxy'
    have he : ε x y = ε x y' := by
      have e1 := (hbit x hx (c x y) (ε x y)).mp ((hd x _ 2).mpr (hfour x hx y hy hxy).1)
      have e2 := (hbit x hx (c x y') (ε x y')).mp ((hd x _ 2).mpr (hfour x hx y' hy' hxy').1)
      rw [e1, e2, hcc]
    rw [← hcc, ← he] at h2' h3'
    have hmm := line_eq_of_lower H col hx6 hxm hzm hxm' hzm' h3 h2 h2'
    subst hmm
    by_contra hne
    exact not_three_far_on_line H col hx6 ((hO y).mp hy) ((hO y').mp hy') hxm hym hym'
      (fun h => hxy.ne (Subtype.ext h)) (fun h => hxy'.ne (Subtype.ext h))
      (fun h => hne (Subtype.ext h))
  have hcard3 : ∀ x ∈ O, (univ.filter fun y => y ∈ O ∧ Γ.Adj x y).card = 3 := by
    intro x hx
    have h := Finset.card_bij (s := univ.filter fun y => y ∈ O ∧ Γ.Adj x y)
      (t := (univ : Finset (Fin 3))) (fun y _ => c x y) (fun _ _ => Finset.mem_univ _)
      (fun y₁ hy₁ y₂ hy₂ h => by
        rw [Finset.mem_filter] at hy₁ hy₂
        exact hcol_un x hx y₁ hy₁.2.1 y₂ hy₂.2.1 hy₁.2.2 hy₂.2.2 h)
      (fun i _ => by
        obtain ⟨y, hy, hxy, hci⟩ := hcol_ex x hx i
        exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, hxy⟩, hci⟩)
    rw [h, Finset.card_univ, Fintype.card_fin]
  have hzsymm : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → z y x = z x y := by
    intro x hx y hy hxy
    obtain ⟨m, ⟨hxm, hym⟩, -⟩ := exists_unique_common_line H col hxy
    obtain ⟨hN, -⟩ := hz x y hx hy hxy
    obtain ⟨hN', hz2'⟩ := hz y x hy hx hxy.symm
    have hmem : (z y x : V) ∈ G.neighborFinset m := by rw [hN' m hym hxm]; simp
    rw [hN m hxm hym] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have h4 : G.dist (w : V) (z y x) = 4 := (hd w _ 2).mp hz2'
    rcases hmem with h | h | h
    · rw [h, (hO x).mp hx] at h4
      omega
    · rw [h, (hO y).mp hy] at h4
      omega
    · exact Subtype.ext h
  have hcsymm : ∀ x ∈ O, ∀ y ∈ O, Γ.Adj x y → c y x = c x y := by
    intro x hx y hy hxy
    rw [hc, hc, hzsymm x hx y hy hxy]
  have hrex : ∀ (i : Fin 3) (x : {v : V // col v = false}), ∃ y : {v : V // col v = false},
      x ∈ O → y ∈ O ∧ Γ.Adj x y ∧ c x y = i := by
    intro i x
    by_cases hx : x ∈ O
    · obtain ⟨y, hy⟩ := hcol_ex x hx i
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose r hr using hrex
  have hP₁ : ∀ s : {v : V // col v = false},
      Γ.dist w s = 1 ↔ ∃! ie : Fin 3 × Fin 2, p ie.1 ie.2 = s := by
    intro s
    constructor
    · intro hs
      obtain ⟨i, e, h⟩ := exists_label H col hℓ hwℓ hpℓ hpw hp ((hd w s 1).mp hs)
      refine ⟨(i, e), Subtype.ext h, fun ie hie => ?_⟩
      obtain ⟨h1, h2⟩ :=
        label_injective H col hℓ hwℓ hpℓ hpw hp (hie.trans (Subtype.ext h).symm)
      exact Prod.ext h1 h2
    · rintro ⟨⟨i, e⟩, rfl, -⟩
      exact (hd w _ 1).mpr (dist_label H col hwℓ hpℓ hpw i e)
  refine ⟨⟨fun k => hlay w k, fun x => ?_⟩, fun n hn x hx => inner_layer_lines H col w hn x hx,
    fun x hx m hm => far_lines H col w x hx m hm, hP₁, z, fun x y => q₀ (z x y), c, ε, r, lam,
    fun x hx y hy hxy => ?_, fun x hx => ⟨hcard3 x hx, fun i => ?_⟩, fun i x hx => ?_,
    fun x hx i j hij h => ?_, fun v cy hcy => ?_, fun x hx i => ?_, fun x hx y hy hxy => ?_⟩
  ·
    have h1 : Γ.dist w x = G.dist (w : V) x / 2 := (point_dist hconn col w x).1
    have h2 := dist_le_six hcyc hconn col hdeg hcard (w : V) x
    omega
  ·
    obtain ⟨hN, hz2⟩ := hz x y hx hy hxy
    exact ⟨exists_unique_common_line H col hxy, hN, hz2, hq₀ (z x y) hz2,
      (hedge x hx y hy hxy).2.2⟩
  ·
    obtain ⟨y, hy, hxy, hci⟩ := hcol_ex x hx i
    exact ⟨y, ⟨hy, hxy, hci⟩, fun y' ⟨hy', hxy', hci'⟩ =>
      hcol_un x hx y' hy' y hy hxy' hxy (hci'.trans hci.symm)⟩
  ·
    obtain ⟨hy, hxy, hci⟩ := hr i x hx
    obtain ⟨hy2, hxy2, hci2⟩ := hr i (r i x) hy
    exact ⟨hy, hxy, hci, hcol_un (r i x) hy (r i (r i x)) hy2 x hx hxy2 hxy.symm
      (hci2.trans ((hcsymm x hx (r i x) hy hxy).trans hci).symm), hxy.ne.symm⟩
  ·
    exact hij ((hr i x hx).2.2.symm.trans ((congrArg (c x) h).trans (hr j x hx).2.2))
  ·
    have hfar : ∀ t : O, G.dist (w : V) ((t : {v : V // col v = false}) : V) = 6 :=
      fun t => (hO t).mp t.2
    have hadj : ∀ {a b : O}, (Γ.induce O).Adj a b →
        G.dist ((a : {v : V // col v = false}) : V) ((b : {v : V // col v = false}) : V) = 2 :=
      fun h => (hA _ _).mp h
    have hne : ∀ {a b : O}, a ≠ b →
        ((a : {v : V // col v = false}) : V) ≠ ((b : {v : V // col v = false}) : V) :=
      fun h h' => h (Subtype.ext (Subtype.ext h'))
    refine ⟨fun h3 => ?_, fun h4 => ?_, fun h5 => ?_⟩
    · obtain ⟨a, b, hva, hab, hbv, -, -, -⟩ := exists_of_isCycle_three hcy h3
      exact no_far_triangle H col (hfar v) (hfar a) (hfar b) (hadj hva) (hadj hab) (hadj hbv)
    · obtain ⟨a, b, d, hva, hab, hbd, hdv, had, hbv⟩ := exists_of_isCycle_four hcy h4
      exact no_far_square H col (hfar v) (hfar a) (hfar b) (hfar d) (hadj hva) (hadj hab)
        (hadj hbd) (hadj hdv) (hne hbv.symm) (hne had)
    · obtain ⟨a, b, d, e, hva, hab, hbd, hde, hev, had, -, hbv, -, hdv⟩ :=
        exists_of_isCycle_five hcy h5
      exact no_far_pentagon H col (hfar v) (hfar a) (hfar b) (hfar d) (hfar e) (hadj hva)
        (hadj hab) (hadj hbd) (hadj hde) (hadj hev) (hne hbv.symm) (hne hdv.symm) (hne had)
  ·
    refine ⟨⟨lam x i, (hbit x hx i _).mpr rfl, fun e he => (hbit x hx i e).mp he⟩,
      (hbit x hx i _).mpr rfl,
      fun e he => (h23 x hx i e).resolve_left fun h => he ((hbit x hx i e).mp h), ?_⟩
    rw [SimpleGraph.dist_comm]
    exact hx
  ·
    obtain ⟨hfx, hfy⟩ := hfour x hx y hy hxy
    have e1 := (hbit x hx (c x y) (ε x y)).mp ((hd x _ 2).mpr hfx)
    have e2 := (hbit y hy (c x y) (ε x y)).mp ((hd y _ 2).mpr hfy)
    refine ⟨e1.symm, e2.symm, fun j hj hxyj => hj ?_⟩
    have hx2 := (hbit x hx j (lam x j)).mpr rfl
    have hy2 := (hbit y hy j (lam x j)).mpr hxyj
    obtain ⟨m, hxm, hym, hzm, hz4, h2, h3⟩ := hedgeG x hx y hy hxy
    have heq := eq_of_dist_four_four H col ((hO x).mp hx) ((hO y).mp hy)
      (fun h => hxy.ne (Subtype.ext h)) hxm hym hzm hz4 h3 h2
      (dist_label H col hwℓ hpℓ hpw j _) ((hd x _ 2).mp hx2) ((hd y _ 2).mp hy2)
    exact (label_injective H col hℓ hwℓ hpℓ hpw hp (Subtype.ext heq)).1

end CFSG.Combinatorics.HexagonLayers

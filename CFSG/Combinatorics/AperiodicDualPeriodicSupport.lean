module

public import CFSG.Combinatorics.HexagonStabilizerFaithfulSupport
public import CFSG.Combinatorics.AperiodicCentralInvolutionMap
public import CFSG.Combinatorics.AperiodicFiveOfSixSupport
public import CFSG.Combinatorics.HexagonAlternatingOctagons
public import Std.Tactic.BVDecide.Normalize.Bool

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Dual

variable {V : Type*} {G : SimpleGraph V}

@[expose] def dualCol (col : G.Coloring Bool) : G.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun v => !col v) fun {_ _} h e => col.valid h (by simpa using e)

@[simp] theorem dualCol_apply (col : G.Coloring Bool) (v : V) : dualCol col v = !col v :=
  rfl

end Dual

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_frameData (H : MooreHyp G) (col : G.Coloring Bool)
    (u : {v : V // col v = false}) :
    ∃ (ℓ : Fin 3 → V) (p : Fin 3 → Fin 2 → {v : V // col v = false})
      (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
      (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
      (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2),
      Function.Injective ℓ ∧ (∀ i, G.Adj (u : V) (ℓ i)) ∧ (∀ i e, G.Adj (p i e : V) (ℓ i)) ∧
        (∀ i e, p i e ≠ u) ∧ (∀ i, Function.Injective (p i)) ∧
        IsFrameData G col u p z q c ε := by
  obtain ⟨ℓ, p, hℓ, huℓ, hpℓ, hpu, hp⟩ :=
    HexagonStabilizerFaithful.exists_frame_labels (col := col) H.deg u
  obtain ⟨-, -, -, -, z, q, c, ε, -, -, hedge, -⟩ :=
    order_two_hexagon_layers_and_opposite_edge_coordinates G H.card H.conn H.deg col H.cyc u ℓ hℓ
      huℓ p hpℓ hpu hp
  exact ⟨ℓ, p, z, q, c, ε, hℓ, huℓ, hpℓ, hpu, hp, fun x hx y hy hxy =>
    ⟨(hedge x hx y hy hxy).2.1, (hedge x hx y hy hxy).2.2.2.1, (hedge x hx y hy hxy).2.2.2.2⟩⟩

variable {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F in
theorem dist_ell_edge_line {x y : {v : V // col v = false}} (hx : (pointGraph G col).dist w x = 3)
    (hy : (pointGraph G col).dist w y = 3) (hxy : (pointGraph G col).Adj x y) {L : V}
    (hxL : G.Adj (x : V) L) (hyL : G.Adj (y : V) L) {i₀ : Fin 3} (hi₀ : c x y ≠ i₀) :
    G.dist (ℓ i₀) L = 6 := by
  have hd := point_dist_eq_iff F.moore.conn col
  have adj1 : ∀ {a b : V}, G.Adj a b → G.dist a b = 1 :=
    fun h => SimpleGraph.dist_eq_one_iff_adj.mpr h
  obtain ⟨m, -, xm, ym, zm, -, -, zq2, -⟩ := F.edge hx hy hxy
  have hLm : L = m :=
    line_eq_of_two F (fun h => hxy.ne (Subtype.ext h)) x.2 y.2 hxL hyL xm ym
  subst hLm
  have hqℓ : G.Adj (q x y : V) (ℓ (c x y)) := by
    rw [(F.data x hx y hy hxy).2.2]
    exact F.line _ _
  have hw5 : G.dist (w : V) L = 5 := dist_eq_five_of_adj F.moore col ((hd w x 3).mp hx) xm
  have hh4 : G.dist (ℓ (c x y)) L = 4 := by
    have h1 := F.moore.conn.dist_triangle (u := ℓ (c x y)) (v := (q x y : V)) (w := L)
    have h2 := F.moore.conn.dist_triangle (u := (q x y : V)) (v := (z x y : V)) (w := L)
    have h3 := F.moore.conn.dist_triangle (u := (w : V)) (v := ℓ (c x y)) (w := L)
    have e1 : G.dist (ℓ (c x y)) (q x y : V) = 1 := by rw [SimpleGraph.dist_comm]; exact adj1 hqℓ
    have e2 : G.dist (q x y : V) (z x y : V) = 2 := by rw [SimpleGraph.dist_comm]; exact zq2
    have e3 : G.dist (z x y : V) L = 1 := adj1 zm
    have e4 : G.dist (w : V) (ℓ (c x y)) = 1 := adj1 (F.root _)
    omega
  have hge : 4 ≤ G.dist (ℓ i₀) L := by
    have h := F.moore.conn.dist_triangle (u := (w : V)) (v := ℓ i₀) (w := L)
    rw [adj1 (F.root i₀)] at h
    omega
  have hcolL : col L = true := col_eq_true_of_adj col x.2 xm
  have hcolℓ : col (ℓ i₀) = true := col_eq_true_of_adj col w.2 (F.root i₀)
  obtain ⟨n, hn⟩ := even_dist_of_col_eq F.moore.conn col (hcolℓ.trans hcolL.symm)
  have hle := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (ℓ i₀) L
  have hne4 : G.dist (ℓ i₀) L ≠ 4 := by
    intro h4
    have := pred_unique F.moore.cyc F.moore.conn (k := 4) (by norm_num)
      (show G.dist L (w : V) = 4 + 1 by rw [SimpleGraph.dist_comm]; exact hw5) (F.root i₀)
      (F.root (c x y)) (by rw [SimpleGraph.dist_comm]; exact h4)
      (by rw [SimpleGraph.dist_comm]; exact hh4)
    exact hi₀ (F.inj this).symm
  omega

include F in
theorem dist_ell_lower_line {A s E : V} (hA : G.dist (w : V) A = 4) (hs : G.dist (w : V) s = 2)
    (hAE : G.Adj A E) (hsE : G.Adj s E) {i₀ j : Fin 3} (hsℓ : G.Adj s (ℓ j)) (hij : i₀ ≠ j) :
    G.dist (w : V) E = 3 ∧ G.dist (ℓ i₀) E = 4 := by
  have adj1 : ∀ {a b : V}, G.Adj a b → G.dist a b = 1 :=
    fun h => SimpleGraph.dist_eq_one_iff_adj.mpr h
  have hw3 : G.dist (w : V) E = 3 := by
    have h1 := F.moore.conn.dist_triangle (u := (w : V)) (v := s) (w := E)
    have h2 := F.moore.conn.dist_triangle (u := (w : V)) (v := E) (w := A)
    rw [adj1 hsE] at h1
    rw [SimpleGraph.dist_comm (u := E), adj1 hAE] at h2
    omega
  refine ⟨hw3, ?_⟩
  have hle4 : G.dist (ℓ i₀) E ≤ 4 := by
    have h1 := F.moore.conn.dist_triangle (u := ℓ i₀) (v := (w : V)) (w := E)
    have h2 := F.moore.conn.dist_triangle (u := (w : V)) (v := ℓ j) (w := E)
    have h3 := F.moore.conn.dist_triangle (u := ℓ j) (v := s) (w := E)
    have e1 : G.dist (ℓ i₀) (w : V) = 1 := by rw [SimpleGraph.dist_comm]; exact adj1 (F.root i₀)
    have e2 : G.dist (w : V) (ℓ j) = 1 := adj1 (F.root j)
    have e3 : G.dist (ℓ j) s = 1 := by rw [SimpleGraph.dist_comm]; exact adj1 hsℓ
    have e4 : G.dist s E = 1 := adj1 hsE
    omega
  have hge : 2 ≤ G.dist (ℓ i₀) E := by
    have h := F.moore.conn.dist_triangle (u := (w : V)) (v := ℓ i₀) (w := E)
    rw [adj1 (F.root i₀)] at h
    omega
  have hcolE : col E = true := col_eq_true_of_adj col
    (col_eq_false_of_adj col (col_eq_true_of_adj col w.2 (F.root j)) hsℓ) hsE
  have hcolℓ : col (ℓ i₀) = true := col_eq_true_of_adj col w.2 (F.root i₀)
  obtain ⟨n, hn⟩ := even_dist_of_col_eq F.moore.conn col (hcolℓ.trans hcolE.symm)
  have hne2 : G.dist (ℓ i₀) E ≠ 2 := by
    intro h2
    obtain ⟨x, hℓx, hEx⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn h2
    have hx2 : G.dist (w : V) x = 2 := by
      rcases dist_adj F.moore.conn col hℓx (w : V) with h | h
      · rw [adj1 (F.root i₀)] at h
        exact h
      · rw [adj1 (F.root i₀)] at h
        have hxw : (w : V) = x :=
          (F.moore.conn.dist_eq_zero_iff (u := (w : V)) (v := x)).mp (by omega)
        rw [← hxw] at hEx
        rw [adj1 hEx.symm] at hw3
        omega
    have hxs : x = s := pred_unique F.moore.cyc F.moore.conn (k := 2) (by norm_num)
      (show G.dist (w : V) E = 2 + 1 from hw3) hEx hsE.symm hx2 hs
    rw [hxs] at hℓx
    exact hij (F.inj (pred_unique F.moore.cyc F.moore.conn (k := 1) (by norm_num)
      (show G.dist (w : V) s = 1 + 1 from hs) hℓx.symm hsℓ (adj1 (F.root i₀)) (adj1 (F.root j))))
  omega

include F hr haper in
theorem exists_periodic_dual {u : {v : V // dualCol col v = false}} (hwu : G.Adj (w : V) u)
    {ℓ' : Fin 3 → V} (hℓ' : Function.Injective ℓ') (hwℓ' : ∀ i, G.Adj (u : V) (ℓ' i))
    {p' : Fin 3 → Fin 2 → {v : V // dualCol col v = false}}
    (hpℓ' : ∀ i e, G.Adj (p' i e : V) (ℓ' i)) (hpw' : ∀ i e, p' i e ≠ u)
    (hp' : ∀ i, Function.Injective (p' i))
    {z' q' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} →
      {v : V // dualCol col v = false}}
    {c' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 3}
    {ε' : {v : V // dualCol col v = false} → {v : V // dualCol col v = false} → Fin 2}
    (hdata' : IsFrameData G (dualCol col) u p' z' q' c' ε') :
    ∃ x : Fin 6 → {v : V // dualCol col v = false},
      IsHex G (dualCol col) u x ∧ IsPeriodic c' x := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hd' := point_dist_eq_iff F.moore.conn (dualCol col)
  have hA := point_adj_iff F.moore.conn col
  have hA' := point_adj_iff F.moore.conn (dualCol col)
  have hV : ∀ {a b : {v : V // col v = false}}, a ≠ b → (a : V) ≠ b :=
    fun h h' => h (Subtype.ext h')
  have f : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      G.dist (w : V) x = 6 := fun hx => (hd w _ 3).mp hx
  by_contra hnot
  have haper' : ∀ x : Fin 6 → {v : V // dualCol col v = false}, IsHex G (dualCol col) u x →
      ¬ IsPeriodic c' x := fun x hx hpx => hnot ⟨x, hx, hpx⟩
  have F' : IsFrame G (dualCol col) u ℓ' p' z' q' c' ε' :=
    ⟨F.moore, hℓ', hwℓ', hpℓ', hpw', hp', hdata'⟩
  obtain ⟨r', hr'⟩ := HexagonAlternatingOctagons.exists_colour_moving G F.moore (dualCol col) u ℓ'
    hℓ' hwℓ' p' hpℓ' hpw'
    hp' z' q' c' ε' hdata'
  have hr'' := fun i x hx => (hr' i x hx).1
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (u : V) = ℓ i₀ := by
    have h : (u : V) ∈ G.neighborFinset (w : V) := (SimpleGraph.mem_neighborFinset _ _ _).mpr hwu
    rw [neighborFinset_root F.moore F.inj F.root] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  obtain ⟨jj, kk, h0j, hjk, h0k⟩ :=
    (by decide : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k) i₀
  obtain ⟨y₀, hy₀, -⟩ :=
    exists_dist_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (w : V)
  have hy₀col : col y₀ = false := by
    have h := (even_dist_iff F.moore.conn col (w : V) y₀).mp (by rw [hy₀]; decide)
    rw [Bool.coe_iff_coe, w.2] at h
    exact h.symm
  obtain ⟨γ, hγV⟩ : ∃ γ : {v : V // col v = false}, (γ : V) = y₀ := ⟨⟨y₀, hy₀col⟩, rfl⟩
  have hγ : (pointGraph G col).dist w γ = 3 := (hd w γ 3).mpr (by rw [hγV]; exact hy₀)
  obtain ⟨δ, hδr⟩ : ∃ δ, r jj γ = δ := ⟨_, rfl⟩
  obtain ⟨hδ, hγδ, hcγδ⟩ := hδr ▸ hr jj γ hγ
  obtain ⟨a, har⟩ : ∃ a, r kk δ = a := ⟨_, rfl⟩
  obtain ⟨ha, hδa, hcδa⟩ := har ▸ hr kk δ hδ
  obtain ⟨b, hbr⟩ : ∃ b, r jj a = b := ⟨_, rfl⟩
  obtain ⟨hb, hab, hcab⟩ := hbr ▸ hr jj a ha
  have hσγ : r kk b = sigmaMap G col w γ := by
    rw [← (paths_to_sigmaMap F hr haper hγ hjk.symm h0j.symm h0k.symm).1, hδr, har, hbr]
  obtain ⟨hσγO, hbσ, hcbσ⟩ := hσγ ▸ hr kk b hb
  have hσδ : r jj (sigmaMap G col w γ) = sigmaMap G col w δ := by
    rw [← hδr, sigmaMap_r F hr haper hγ]
  obtain ⟨hσδO, hσγδ, hcσγδ⟩ := hσδ ▸ hr jj _ hσγO
  have himg : ∀ {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      ∀ {i j : Fin 3}, i ≠ j → r i x ≠ r j x := fun hx i j hij e =>
    hij ((hr i _ hx).2.2.symm.trans ((congrArg (c _) e).trans (hr j _ hx).2.2))
  have hinv : ∀ {i : Fin 3} {x : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      r i (r i x) = x := fun hx => F.r_invol hr hx
  have nγa : γ ≠ a := by
    rw [← hinv (i := jj) hγ, hδr, ← har]
    exact himg hδ hjk
  have nδb : δ ≠ b := fun e => himg hδ hjk.symm (by
    rw [har]
    conv_rhs => rw [e, ← hbr, hinv ha])
  have naσ : a ≠ sigmaMap G col w γ := fun e => himg ha hjk (by
    conv_rhs => rw [e, ← hσγ, hinv hb]
    exact hbr)
  have nbσδ : b ≠ sigmaMap G col w δ := by
    rw [← hinv (i := kk) hb, hσγ, ← hσδ]
    exact himg hσγO hjk.symm
  have nδσ : δ ≠ sigmaMap G col w γ := by
    intro e
    have h3 := dist_three_of_word F hr hδ hjk.symm hjk
    rw [har, hbr, hσγ, ← e, SimpleGraph.dist_self] at h3
    omega
  obtain ⟨L₁, -, γL₁, δL₁, AL₁, A4, -⟩ := F.edge hγ hδ hγδ
  obtain ⟨L₂, -, δL₂, aL₂, -⟩ := F.edge hδ ha hδa
  obtain ⟨L₃, -, aL₃, bL₃, -⟩ := F.edge ha hb hab
  obtain ⟨L₄, -, bL₄, σL₄, -⟩ := F.edge hb hσγO hbσ
  obtain ⟨L₅, -, σL₅, σδL₅, BL₅, B4, -⟩ := F.edge hσγO hσδO hσγδ
  have hfar : ∀ {L : V} {x y t : {v : V // col v = false}}, (pointGraph G col).dist w x = 3 →
      (pointGraph G col).dist w y = 3 → (pointGraph G col).dist w t = 3 → G.Adj (x : V) L →
      G.Adj (y : V) L → G.Adj (t : V) L → x ≠ y → x ≠ t → y ≠ t → False :=
    fun hx hy ht hxL hyL htL hxy hxt hyt =>
      not_three_far_on_line F.moore col (f hx) (f hy) (f ht) hxL hyL htL (hV hxy) (hV hxt) (hV hyt)
  have n12 : L₁ ≠ L₂ := fun e => hfar hγ hδ ha γL₁ δL₁ (e ▸ aL₂) hγδ.ne nγa hδa.ne
  have n23 : L₂ ≠ L₃ := fun e => hfar hδ ha hb δL₂ aL₂ (e ▸ bL₃) hδa.ne nδb hab.ne
  have n34 : L₃ ≠ L₄ := fun e => hfar ha hb hσγO aL₃ bL₃ (e ▸ σL₄) hab.ne naσ hbσ.ne
  have n45 : L₄ ≠ L₅ := fun e => hfar hb hσγO hσδO bL₄ σL₄ (e ▸ σδL₅) hbσ.ne nbσδ hσγδ.ne
  have n13 : L₁ ≠ L₃ := fun e => hfar hδ ha hb (e ▸ δL₁) aL₃ bL₃ hδa.ne nδb hab.ne
  have n14 : L₁ ≠ L₄ := fun e => hfar hδ hb hσγO (e ▸ δL₁) bL₄ σL₄ nδb nδσ hbσ.ne
  have n24 : L₂ ≠ L₄ := fun e => hfar hδ hb hσγO (e ▸ δL₂) bL₄ σL₄ nδb nδσ hbσ.ne
  have hAB := adj_third_sigmaMap F hr haper hγ hδ hγδ
  obtain ⟨E, AE, BE⟩ := exists_adj_adj_of_dist_eq_two F.moore.conn ((hA _ _).mp hAB)
  have hwE : G.dist (w : V) E = 2 + 1 := by
    have h1 := dist_adj F.moore.conn col AE (w : V)
    rcases h1 with h | h
    ·
      exfalso
      obtain ⟨a₀, b₀, c₀, hN, ha₀, hb₀, hc₀, -⟩ :=
        nbr_structure F.moore col (k := 4) (by norm_num) (show G.dist (w : V) E = 4 + 1 by omega)
      have hmem : ∀ {t : V}, G.Adj t E → G.dist (w : V) t = 4 → t = a₀ := by
        intro t htE ht4
        have htN : t ∈ G.neighborFinset E := (SimpleGraph.mem_neighborFinset _ _ _).mpr htE.symm
        rw [hN] at htN
        simp only [Finset.mem_insert, Finset.mem_singleton] at htN
        rcases htN with h' | h' | h'
        · exact h'
        · rw [h'] at ht4
          omega
        · rw [h'] at ht4
          omega
      exact hAB.ne (Subtype.ext ((hmem AE A4).trans (hmem BE B4).symm))
    · omega
  obtain ⟨s₀, Es₀, hs₀⟩ := pred_exists F.moore.conn hwE
  have hs₀col : col s₀ = false := col_eq_false_of_adj col (col_eq_true_of_adj col
    (z γ δ).2 AE) Es₀.symm
  obtain ⟨s, hsV⟩ : ∃ s : {v : V // col v = false}, (s : V) = s₀ := ⟨⟨s₀, hs₀col⟩, rfl⟩
  rw [← hsV] at Es₀ hs₀
  have hAs : (pointGraph G col).Adj (z γ δ) s := (hA _ _).mpr (dist_eq_two_of_adj_adj
    F.moore.conn col (fun h => by rw [h, hs₀] at A4; omega) ((z γ δ).2.trans s.2.symm) AE
    Es₀.symm)
  have hsq : s = q γ δ := ((F.data γ hγ δ hδ hγδ).2.1 s).mp ⟨hAs, (hd w s 1).mpr hs₀⟩
  have hsℓ : G.Adj (s : V) (ℓ jj) := by
    rw [hsq, (F.data γ hγ δ hδ hγδ).2.2, hcγδ]
    exact F.line _ _
  obtain ⟨hwE3, hE4⟩ := dist_ell_lower_line F A4 hs₀ AE Es₀.symm hsℓ h0j
  have d₁ := dist_ell_edge_line F hγ hδ hγδ γL₁ δL₁ (by rw [hcγδ]; exact h0j.symm)
  have d₂ := dist_ell_edge_line F hδ ha hδa δL₂ aL₂ (by rw [hcδa]; exact h0k.symm)
  have d₃ := dist_ell_edge_line F ha hb hab aL₃ bL₃ (by rw [hcab]; exact h0j.symm)
  have d₄ := dist_ell_edge_line F hb hσγO hbσ bL₄ σL₄ (by rw [hcbσ]; exact h0k.symm)
  have d₅ := dist_ell_edge_line F hσγO hσδO hσγδ σL₅ σδL₅ (by rw [hcσγδ]; exact h0j.symm)
  have hw5 : ∀ {x : {v : V // col v = false}} {L : V}, (pointGraph G col).dist w x = 3 →
      G.Adj (x : V) L → G.dist (w : V) L = 5 := fun hx hxL => dist_eq_five_of_adj F.moore col
    (f hx) hxL
  have nE1 : E ≠ L₁ := fun e => by have := hw5 hγ γL₁; rw [← e] at this; omega
  have n5E : L₅ ≠ E := fun e => by have := hw5 hσγO σL₅; rw [e] at this; omega
  have hline : ∀ {x : {v : V // col v = false}} {L : V}, G.Adj (x : V) L → dualCol col L = false :=
    fun {x _} hxL => by simp [col_eq_true_of_adj col x.2 hxL]
  let D : ∀ {x : {v : V // col v = false}} {L : V}, G.Adj (x : V) L →
      {v : V // dualCol col v = false} := fun {_ L} hxL => ⟨L, hline hxL⟩
  have hO' : ∀ {x : {v : V // col v = false}} {L : V} (hxL : G.Adj (x : V) L),
      G.dist (ℓ i₀) L = 6 → D hxL ∈ oppSet G (dualCol col) u := fun hxL h6 =>
    (hd' u _ 3).mpr (by rw [hi₀]; exact h6)
  have hadj' : ∀ {x x' t : {v : V // col v = false}} {L L' : V} (hxL : G.Adj (x : V) L)
      (hx'L' : G.Adj (x' : V) L'), G.Adj (t : V) L → G.Adj (t : V) L' → L ≠ L' →
      (pointGraph G (dualCol col)).Adj (D hxL) (D hx'L') := fun hxL hx'L' htL htL' hne =>
    (hA' _ _).mpr (dist_eq_two_of_adj_adj F.moore.conn (dualCol col) hne
      ((hline hxL).trans (hline hx'L').symm) htL.symm htL'.symm)
  have hne' : ∀ {x x' : {v : V // col v = false}} {L L' : V} (hxL : G.Adj (x : V) L)
      (hx'L' : G.Adj (x' : V) L'), L ≠ L' → D hxL ≠ D hx'L' :=
    fun _ _ hne e => hne (congrArg Subtype.val e)
  have hE := mem_of_five F' hr'' haper' (hO' γL₁ d₁) (hO' δL₂ d₂) (hO' aL₃ d₃) (hO' bL₄ d₄)
    (hO' σL₅ d₅) (hadj' γL₁ δL₂ δL₁ δL₂ n12) (hadj' δL₂ aL₃ aL₂ aL₃ n23)
    (hadj' aL₃ bL₄ bL₃ bL₄ n34) (hadj' bL₄ σL₅ σL₄ σL₅ n45) (hadj' σL₅ AE BL₅ BE n5E)
    (hadj' AE γL₁ AE AL₁ nE1) (hne' γL₁ aL₃ n13) (hne' γL₁ bL₄ n14) (hne' δL₂ bL₄ n24)
  have h6 := (hd' u _ 3).mp hE
  rw [hi₀] at h6
  change G.dist (ℓ i₀) E = 2 * 3 at h6
  omega

end CFSG.Combinatorics.AperiodicOppositeComponents

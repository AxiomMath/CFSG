module

public import CFSG.Combinatorics.AperiodicSixteenRecognition
public import CFSG.Combinatorics.AperiodicSixteenGraphSupport
public import CFSG.Combinatorics.HexagonAlternatingOctagonsOrbit
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph

namespace CFSG.Combinatorics.HexagonPeriodicPropagation.IsFrame

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  (F : IsFrame G col w ℓ p z q c ε)
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
include F hr

theorem rel_of_aperiodic
    (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {x : {v : V // col v = false}}
    (hx : (pointGraph G col).dist w x = 3) : r k (r j (r i x)) = r i (r k (r j x)) := by
  obtain ⟨v₁, hv₁⟩ : ∃ y, r i x = y := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ y, r j v₁ = y := ⟨_, rfl⟩
  obtain ⟨v₃, hv₃⟩ : ∃ y, r k v₂ = y := ⟨_, rfl⟩
  obtain ⟨v₄, hv₄⟩ : ∃ y, r i v₃ = y := ⟨_, rfl⟩
  have st : ∀ {l : Fin 3} {a b}, (pointGraph G col).dist w a = 3 → r l a = b →
      (pointGraph G col).dist w b = 3 ∧ (pointGraph G col).Adj a b ∧ c a b = l :=
    fun ha hb => hb ▸ hr _ _ ha
  obtain ⟨h₁, a01, c01⟩ := st hx hv₁
  obtain ⟨h₂, a12, c12⟩ := st h₁ hv₂
  obtain ⟨h₃, a23, c23⟩ := st h₂ hv₃
  obtain ⟨h₄, a34, c34⟩ := st h₃ hv₄
  have hne : ∀ {a b d : {v : V // col v = false}}, c b a ≠ c b d → a ≠ d :=
    fun h e => h (by rw [e])
  have n02 : x ≠ v₂ := hne (b := v₁) (by rw [F.symm hx h₁ a01, c01, c12]; exact hij)
  have n13 : v₁ ≠ v₃ := hne (b := v₂) (by rw [F.symm h₁ h₂ a12, c12, c23]; exact hjk)
  have n24 : v₂ ≠ v₄ := hne (b := v₃) (by rw [F.symm h₂ h₃ a23, c23, c34]; exact hik.symm)
  have n03 : x ≠ v₃ := fun e => F.no_triangle hx h₁ h₂ a01 a12 (by rw [e]; exact a23)
  have n14 : v₁ ≠ v₄ := fun e => F.no_triangle h₁ h₂ h₃ a12 a23 (by rw [e]; exact a34)
  have n04 : x ≠ v₄ := fun e =>
    F.no_square hx h₁ h₂ h₃ a01 a12 a23 (by rw [e]; exact a34) n02 n13
  have hnd : [x, v₁, v₂, v₃, v₄].Nodup :=
    nodup_five a01.ne n02 n03 n04 a12.ne n13 n14 a23.ne n24 a34.ne
  obtain ⟨u, ⟨hu, h0u, h4u⟩, -, hnd6, hcol⟩ :=
    F.complete hij hjk hik hx h₁ h₂ h₃ h₄ a01 a12 a23 a34 hnd c01 c12 c23 c34
  rcases hcol with ⟨c4u, cu0⟩ | ⟨c4u, cu0⟩
  ·
    exfalso
    refine haper ![x, v₁, v₂, v₃, v₄, u] ⟨List.nodup_ofFn.mp (by simpa [List.ofFn_succ] using hnd6),
      fun m => ?_, fun m => ?_⟩ ⟨i, j, k, hij, hjk, hik, fun m => ?_⟩
    · fin_cases m
      exacts [hx, h₁, h₂, h₃, h₄, hu]
    · fin_cases m
      exacts [a01, a12, a23, a34, h4u, h0u.symm]
    · fin_cases m
      exacts [c01, c12, c23, c34, c4u, cu0]
  ·
    have hu' : r k v₄ = u := F.r_eq hr h₄ hu h4u c4u
    have hx' : r j u = x := F.r_eq hr hu hx h0u.symm cu0
    have e1 : r j x = r k v₄ := by rw [← hx', ← hu', F.r_invol hr (hr k v₄ h₄).1]
    have e2 : r k (r j x) = v₄ := by rw [e1, F.r_invol hr h₄]
    have e3 : r i (r k (r j x)) = v₃ := by rw [e2, ← hv₄, F.r_invol hr h₃]
    rw [e3, ← hv₃, ← hv₂, ← hv₁]

end CFSG.Combinatorics.HexagonPeriodicPropagation.IsFrame

namespace CFSG.Combinatorics.AperiodicOppositeComponents

open CFSG.Combinatorics.HexagonPeriodicPropagation

section Sets

variable {V : Type*}

abbrev oppSet (G : SimpleGraph V) (col : G.Coloring Bool) (w : {v : V // col v = false}) :
    Set {v : V // col v = false} :=
  {x | (pointGraph G col).dist w x = 3}

abbrev oppGraph (G : SimpleGraph V) (col : G.Coloring Bool) (w : {v : V // col v = false}) :
    SimpleGraph (oppSet G col w) :=
  (pointGraph G col).induce (oppSet G col w)

abbrev compSet {G : SimpleGraph V} {col : G.Coloring Bool} {w : {v : V // col v = false}}
    (Q : (oppGraph G col w).ConnectedComponent) : Set {v : V // col v = false} :=
  {x | ∃ h : x ∈ oppSet G col w, (oppGraph G col w).connectedComponentMk ⟨x, h⟩ = Q}

theorem mem_compSet_of_adj {G : SimpleGraph V} {col : G.Coloring Bool}
    {w : {v : V // col v = false}} {Q : (oppGraph G col w).ConnectedComponent}
    {x y : {v : V // col v = false}} (hx : x ∈ compSet Q) (hy : (pointGraph G col).dist w y = 3)
    (hxy : (pointGraph G col).Adj x y) : y ∈ compSet Q := by
  obtain ⟨hx', hxQ⟩ := hx
  exact ⟨hy, (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G := oppGraph G col w) (v := ⟨x, hx'⟩) (w := ⟨y, hy⟩) hxy).symm.trans hxQ⟩

variable {G : SimpleGraph V} {col : G.Coloring Bool} {w : {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)

include hr in
theorem r_mem_compSet {Q : (oppGraph G col w).ConnectedComponent} {x : {v : V // col v = false}}
    (hx : x ∈ compSet Q) (i : Fin 3) : r i x ∈ compSet Q :=
  mem_compSet_of_adj hx (hr i x hx.1).1 (hr i x hx.1).2.1

@[expose] def compR (Q : (oppGraph G col w).ConnectedComponent) (i : Fin 3) (x : compSet Q) :
    compSet Q :=
  ⟨r i x, r_mem_compSet hr x.2 i⟩

theorem compR_fix (Q : (oppGraph G col w).ConnectedComponent) (i : Fin 3) (x : compSet Q) :
    compR hr Q i x ≠ x := fun h =>
  (hr i x x.2.1).2.1.ne (congrArg Subtype.val h).symm

theorem compR_dist (Q : (oppGraph G col w).ConnectedComponent) (x : compSet Q) :
    Function.Injective fun i => compR hr Q i x := fun i j h =>
  (hr i x x.2.1).2.2.symm.trans
    ((congrArg (fun y => c x y) (congrArg Subtype.val h)).trans (hr j x x.2.1).2.2)

end Sets

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}

variable (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)

include F in
theorem compR_inv (Q : (oppGraph G col w).ConnectedComponent) (i : Fin 3) (x : compSet Q) :
    compR hr Q i (compR hr Q i x) = x :=
  Subtype.ext (F.r_invol hr x.2.1)

include F in
theorem adj_of_colourGraph_adj (Q : (oppGraph G col w).ConnectedComponent) {a b : compSet Q}
    (hab : (colourGraph (compR hr Q)).Adj a b) : (pointGraph G col).Adj a b := by
  obtain ⟨-, i, rfl⟩ := (colourGraph_adj (compR_inv F hr Q)).mp hab
  exact (hr i a a.2.1).2.1

include F in
theorem compR_conn (Q : (oppGraph G col w).ConnectedComponent) :
    (colourGraph (compR hr Q)).Connected := by
  have key : ∀ (u v : oppSet G col w) (W : (oppGraph G col w).Walk u v)
      (hu : (u : {v : V // col v = false}) ∈ compSet Q)
      (hv : (v : {v : V // col v = false}) ∈ compSet Q),
      (colourGraph (compR hr Q)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v W
    induction W with
    | nil => exact fun _ _ => SimpleGraph.Reachable.refl _
    | @cons a b d h W ih =>
      intro ha hd
      have hb : (b : {v : V // col v = false}) ∈ compSet Q := mem_compSet_of_adj ha b.2 h
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) (ih hb hd)
      rw [colourGraph_adj (compR_inv F hr Q)]
      refine ⟨fun e => h.ne (Subtype.ext
        (congrArg (fun y : compSet Q => (y : {v : V // col v = false})) e)), c a b,
        Subtype.ext ?_⟩
      exact (F.r_eq hr a.2 b.2 h rfl).symm
  induction Q using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    have : Nonempty (compSet ((oppGraph G col w).connectedComponentMk v)) := ⟨⟨v, v.2, rfl⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨ha, haQ⟩ := a.2
    obtain ⟨hb, hbQ⟩ := b.2
    obtain ⟨W⟩ := SimpleGraph.ConnectedComponent.exact (haQ.trans hbQ.symm)
    exact key _ _ W a.2 b.2

include F in
theorem compR_cyc (Q : (oppGraph G col w).ConnectedComponent) (x : compSet Q)
    (cy : (colourGraph (compR hr Q)).Walk x x) (hcy : cy.IsCycle) :
    cy.length ≠ 3 ∧ cy.length ≠ 4 ∧ cy.length ≠ 5 := by
  have hadj : ∀ {a b : compSet Q}, (colourGraph (compR hr Q)).Adj a b →
      (pointGraph G col).Adj a b := fun h => adj_of_colourGraph_adj F hr Q h
  refine ⟨fun hl => ?_, fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨a, b, hxa, hab, hbx, -, -, -⟩ := exists_of_isCycle_three hcy hl
    exact F.no_triangle x.2.1 a.2.1 b.2.1 (hadj hxa) (hadj hab) (hadj hbx)
  · obtain ⟨a, b, d, hxa, hab, hbd, hdx, had, hbx⟩ := exists_of_isCycle_four hcy hl
    exact F.no_square x.2.1 a.2.1 b.2.1 d.2.1 (hadj hxa) (hadj hab) (hadj hbd) (hadj hdx)
      (fun h => hbx (Subtype.ext h.symm)) (fun h => had (Subtype.ext h))
  · obtain ⟨a, b, d, e, hxa, hab, hbd, hde, hex, had, -, hbx, -, hdx⟩ :=
      exists_of_isCycle_five hcy hl
    exact F.no_pentagon x.2.1 a.2.1 b.2.1 d.2.1 e.2.1 (hadj hxa) (hadj hab) (hadj hbd)
      (hadj hde) (hadj hex) (fun h => hbx (Subtype.ext h.symm))
      (fun h => hdx (Subtype.ext h.symm)) (fun h => had (Subtype.ext h))

include F in
theorem compR_rel
    (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)
    (Q : (oppGraph G col w).ConnectedComponent) (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (x : compSet Q) :
    compR hr Q k (compR hr Q j (compR hr Q i x)) = compR hr Q i (compR hr Q k (compR hr Q j x)) :=
  Subtype.ext (F.rel_of_aperiodic hr haper hij hjk hik x.2.1)

include F hr in
theorem exists_equiv
    (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)
    (Q : (oppGraph G col w).ConnectedComponent) :
    (∃ φ : K ≃ compSet Q, ∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) ∧
      Nat.card (compSet Q) = 16 := by
  obtain ⟨hex, -, -, hcard⟩ := aperiodic_involution_relations_recognize_sixteen_graph
    (compR hr Q) (compR_inv F hr Q) (compR_fix hr Q) (compR_dist hr Q) (compR_conn F hr Q)
    (compR_cyc F hr Q) (compR_rel F hr haper Q)
  refine ⟨?_, hcard⟩
  obtain ⟨x₀⟩ := (compR_conn F hr Q).nonempty
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hex x₀
  exact ⟨φ, fun g i => congrArg Subtype.val (hφ g i)⟩

section Equiv

variable {Q : (oppGraph G col w).ConnectedComponent} (φ : K ≃ compSet Q)
  (hφ : ∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g))

include F hr hφ in
theorem adj_iff_of_equiv (g h : K) :
    (pointGraph G col).Adj (φ g) (φ h) ↔ T.Adj g h := by
  constructor
  · intro hgh
    refine ⟨c (φ g) (φ h), φ.injective (Subtype.ext ?_)⟩
    rw [hφ]
    exact (F.r_eq hr (φ g).2.1 (φ h).2.1 hgh rfl).symm
  · rintro ⟨i, rfl⟩
    rw [hφ]
    exact (hr i _ (φ g).2.1).2.1

include F hr hφ in
theorem dist_eq_of_equiv (g h : K) :
    (oppGraph G col w).dist ⟨φ g, (φ g).2.1⟩ ⟨φ h, (φ h).2.1⟩ = T.dist g h := by
  apply le_antisymm
  ·
    obtain ⟨W, hW⟩ := AperiodicSixteenGraph.connected.exists_walk_length_eq_dist g h
    let f : T →g oppGraph G col w :=
      ⟨fun g => ⟨φ g, (φ g).2.1⟩, fun {a b} hab => (adj_iff_of_equiv F hr φ hφ a b).mpr hab⟩
    calc _ ≤ (W.map f).length := SimpleGraph.dist_le _
      _ = T.dist g h := by rw [SimpleGraph.Walk.length_map, hW]
  ·
    have key : ∀ (u v : oppSet G col w) (W : (oppGraph G col w).Walk u v)
        (hu : (u : {v : V // col v = false}) ∈ compSet Q)
        (hv : (v : {v : V // col v = false}) ∈ compSet Q),
        T.dist (φ.symm ⟨u, hu⟩) (φ.symm ⟨v, hv⟩) ≤ W.length := by
      intro u v W
      induction W with
      | nil => exact fun _ _ => by simp
      | @cons a b d hab W ih =>
        intro ha hd
        have hb : (b : {v : V // col v = false}) ∈ compSet Q := mem_compSet_of_adj ha b.2 hab
        have hT : T.Adj (φ.symm ⟨a, ha⟩) (φ.symm ⟨b, hb⟩) := by
          rw [← adj_iff_of_equiv F hr φ hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact hab
        have htri := AperiodicSixteenGraph.connected.dist_triangle (u := φ.symm ⟨a, ha⟩)
          (v := φ.symm ⟨b, hb⟩) (w := φ.symm ⟨d, hd⟩)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hT] at htri
        have := ih hb hd
        rw [SimpleGraph.Walk.length_cons]
        omega
    have hreach : (oppGraph G col w).Reachable ⟨φ g, (φ g).2.1⟩ ⟨φ h, (φ h).2.1⟩ :=
      SimpleGraph.ConnectedComponent.exact ((φ g).2.2.trans (φ h).2.2.symm)
    obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
    have := key _ _ W (φ g).2 (φ h).2
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at this
    omega

include F hr hφ in
theorem eq_of_dist_four (g : K) {y : {v : V // col v = false}} (hy : y ∈ oppSet G col w)
    (h : (oppGraph G col w).dist ⟨φ g, (φ g).2.1⟩ ⟨y, hy⟩ = 4) :
    y = φ (τ g) := by
  have hreach : (oppGraph G col w).Reachable ⟨φ g, (φ g).2.1⟩ ⟨y, hy⟩ := by
    by_contra hn
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hn] at h
    exact absurd h (by decide)
  have hyQ : y ∈ compSet Q :=
    ⟨hy, (SimpleGraph.ConnectedComponent.sound hreach).symm.trans (φ g).2.2⟩
  obtain ⟨k, hk⟩ := φ.surjective ⟨y, hyQ⟩
  have hd := dist_eq_of_equiv F hr φ hφ g k
  have hky : (φ k : {v : V // col v = false}) = y := congrArg Subtype.val hk
  simp only [hky] at hd
  rw [h] at hd
  rw [← hky, (dist_eq_four_iff g k).mp hd.symm]

include F hr hφ in
theorem paths_eq_image (h e : K) :
    {m : {v : V // col v = false} × {v : V // col v = false} |
      (φ h : {v : V // col v = false}) ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧
        m.2 ∈ oppSet G col w ∧
        (φ e : {v : V // col v = false}) ∈ oppSet G col w ∧
        (pointGraph G col).Adj (φ h) m.1 ∧ (pointGraph G col).Adj m.1 m.2 ∧
        (pointGraph G col).Adj m.2 (φ e) ∧
        [(φ h : {v : V // col v = false}), m.1, m.2, φ e].Nodup} =
      (fun m : K × K => ((φ m.1 : {v : V // col v = false}), (φ m.2 : {v : V // col v = false}))) ''
        {m : K × K | T.Adj h m.1 ∧ T.Adj m.1 m.2 ∧ T.Adj m.2 e ∧ [h, m.1, m.2, e].Nodup} := by
  have hinj : Function.Injective fun g : K => (φ g : {v : V // col v = false}) :=
    Subtype.val_injective.comp φ.injective
  ext ⟨y₁, y₂⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨-, h₁, h₂, -, a01, a12, a23, hnd⟩
    have hy₁ : y₁ ∈ compSet Q := mem_compSet_of_adj (φ h).2 h₁ a01
    have hy₂ : y₂ ∈ compSet Q := mem_compSet_of_adj hy₁ h₂ a12
    obtain ⟨a, ha⟩ := φ.surjective ⟨y₁, hy₁⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨y₂, hy₂⟩
    have ha' : (φ a : {v : V // col v = false}) = y₁ := congrArg Subtype.val ha
    have hb' : (φ b : {v : V // col v = false}) = y₂ := congrArg Subtype.val hb
    refine ⟨a, b, ⟨?_, ?_, ?_, ?_⟩, ha', hb'⟩
    · rw [← adj_iff_of_equiv F hr φ hφ, ha']
      exact a01
    · rw [← adj_iff_of_equiv F hr φ hφ, ha', hb']
      exact a12
    · rw [← adj_iff_of_equiv F hr φ hφ, hb']
      exact a23
    · refine List.Nodup.of_map (fun g : K => (φ g : {v : V // col v = false})) ?_
      simpa [ha', hb'] using hnd
  · rintro ⟨a, b, ⟨a01, a12, a23, hnd⟩, rfl, rfl⟩
    refine ⟨(φ h).2.1, (φ a).2.1, (φ b).2.1, (φ e).2.1, (adj_iff_of_equiv F hr φ hφ h a).mpr a01,
      (adj_iff_of_equiv F hr φ hφ a b).mpr a12, (adj_iff_of_equiv F hr φ hφ b e).mpr a23, ?_⟩
    simpa using hnd.map hinj

end Equiv

end CFSG.Combinatorics.AperiodicOppositeComponents

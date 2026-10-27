module

public import CFSG.Geometry.GeneralizedQuadrangles.Basic

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V}

@[expose] noncomputable def varianceTrace [Fintype V] (Γ : SimpleGraph V) (x y : V) : Finset V :=
  Finset.univ.filter fun u => Γ.dist x u = 2 ∧ Γ.dist y u = 2

@[expose] noncomputable def varianceZ [Fintype V] (Γ : SimpleGraph V)
    (c : Γ.Coloring (Fin 2)) (X : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun z => c z = 0 ∧ ∀ a ∈ X, 2 < Γ.dist z a

@[expose] noncomputable def varianceTz (Γ : SimpleGraph V) (T : Finset V) (z : V) : ℕ :=
  (T.filter fun u => Γ.dist z u ≤ 2).card

section Basic

variable [Fintype V] [DecidableRel Γ.Adj]

@[simp] theorem mem_varianceTrace {x y u : V} :
    u ∈ varianceTrace Γ x y ↔ Γ.dist x u = 2 ∧ Γ.dist y u = 2 := by
  simp [varianceTrace]

@[simp] theorem mem_varianceZ {c : Γ.Coloring (Fin 2)} {X : Finset V} {z : V} :
    z ∈ varianceZ Γ c X ↔ c z = 0 ∧ ∀ a ∈ X, 2 < Γ.dist z a := by
  classical
  simp [varianceZ]

@[simp] theorem mem_varianceTz_iff {T : Finset V} {z u : V} :
    u ∈ T.filter (fun u => Γ.dist z u ≤ 2) ↔ u ∈ T ∧ Γ.dist z u ≤ 2 := by
  simp

theorem degree_eq_t_add_one_of_color_zero {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {v : V}
    (hv : c v = 0) : Γ.degree v = t + 1 := by
  rw [hdeg v, if_pos hv]

theorem degree_eq_s_add_one_of_color_one {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {v : V}
    (hv : c v = 1) : Γ.degree v = s + 1 := by
  rw [hdeg v, if_neg (by rw [hv]; decide)]

theorem varianceTrace_card (hP : IsGeneralizedPolygon Γ 4)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) :
    (varianceTrace Γ x y).card = t + 1 := by
  classical
  have hcoe : (varianceTrace Γ x y : Set V) = traceSet Γ x y := by
    ext u
    simp [varianceTrace, traceSet]
  rw [← Set.ncard_coe_finset, hcoe, ncard_trace hP hxy]
  exact degree_eq_t_add_one_of_color_zero hdeg hx

theorem color_eq_zero_of_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {x y u : V} (hx : c x = 0)
    (hu : u ∈ varianceTrace Γ x y) : c u = 0 := by
  rw [mem_varianceTrace] at hu
  rw [← hx]
  exact ((hP.eq_iff_even_dist c x u).2 (by rw [hu.1]; norm_num)).symm

theorem color_eq_zero_of_mem_span (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {x y z : V} (hx : c x = 0) (hxy : Γ.dist x y = 4)
    (hz : z ∈ spanSet Γ x y) : c z = 0 := by
  rw [← hx]
  exact color_eq_of_mem_span hP hT c hxy hz

theorem dist_eq_four_of_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4)
    {x y u v : V} (hxy : Γ.dist x y = 4) (hu : u ∈ varianceTrace Γ x y)
    (hv : v ∈ varianceTrace Γ x y) (huv : u ≠ v) : Γ.dist u v = 4 := by
  rw [mem_varianceTrace] at hu hv
  exact dist_eq_four_of_mem_trace hP hxy hu hv huv

theorem dist_eq_two_of_mem_span_of_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {x y z u : V} (hxy : Γ.dist x y = 4)
    (hz : z ∈ spanSet Γ x y) (hu : u ∈ varianceTrace Γ x y) : Γ.dist z u = 2 := by
  rw [mem_varianceTrace] at hu
  exact dist_eq_two_of_mem_span_of_mem_trace hP hT hxy hz hu

theorem card_le_t_add_one_of_subset_span (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) : X.card ≤ t + 1 := by
  classical
  have hTcard : (varianceTrace Γ x y).card = t + 1 :=
    varianceTrace_card hP c hdeg hx hxy
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hTcard]; omega : 0 < _)
  let f : {a // a ∈ X} → V := fun a =>
    commonNeighbor hP
      (dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX a.2) hu)
  have hf_mem : ∀ a, f a ∈ Γ.neighborFinset u := by
    intro a
    rw [mem_neighborFinset]
    dsimp only [f]
    exact commonNeighbor_adj_right hP _
  have hfinj : Set.InjOn f (X.attach : Set {a // a ∈ X}) := by
    intro a _ a' _ haeq
    by_contra hne
    have hne' : a.1 ≠ a'.1 := fun h => hne (Subtype.ext h)
    have h4 : Γ.dist a.1 a'.1 = 4 :=
      dist_eq_four_of_mem_span hP hT hxy (hX a.2) (hX a'.2) hne'
    have hLa : Γ.Adj (f a) a.1 := by
      dsimp only [f]
      exact (commonNeighbor_adj_left hP _).symm
    have hLa' : Γ.Adj (f a) a'.1 := by
      rw [haeq]
      dsimp only [f]
      exact (commonNeighbor_adj_left hP _).symm
    have h2 : Γ.dist a.1 a'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLa.symm hLa' hne'
    omega
  calc
    X.card = X.attach.card := (Finset.card_attach).symm
    _ = (X.attach.image f).card := (Finset.card_image_of_injOn hfinj).symm
    _ ≤ (Γ.neighborFinset u).card := Finset.card_le_card (by
          intro L hL
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hL
          exact hf_mem a)
    _ = Γ.degree u := card_neighborFinset_eq_degree Γ u
    _ = t + 1 :=
      degree_eq_t_add_one_of_color_zero hdeg
        (color_eq_zero_of_mem_varianceTrace hP hx hu)

theorem dist_eq_four_of_mem_X (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V} (hX : (X : Set V) ⊆ spanSet Γ x y)
    {a a' : V} (ha : a ∈ X) (ha' : a' ∈ X) (hne : a ≠ a') : Γ.dist a a' = 4 :=
  dist_eq_four_of_mem_span hP hT hxy (hX ha) (hX ha') hne

theorem not_mem_X_of_mem_varianceTrace (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V} (hX : (X : Set V) ⊆ spanSet Γ x y)
    {u : V} (hu : u ∈ varianceTrace Γ x y) : u ∉ X := by
  intro huX
  rw [mem_varianceTrace] at hu
  exact not_mem_spanSet_of_mem_traceSet hP hT hxy hu (hX huX)

theorem not_mem_varianceTrace_of_mem_varianceZ (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) {x y : V} (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) {c : Γ.Coloring (Fin 2)}
    {z : V} (hz : z ∈ varianceZ Γ c X) : z ∉ varianceTrace Γ x y := by
  intro hzT
  obtain ⟨a, haX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  rw [mem_varianceZ] at hz
  have h2 : Γ.dist a z = 2 :=
    dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hzT
  rw [dist_comm] at h2
  have hzlt : 2 < Γ.dist z a := hz.2 a haX
  omega

theorem two_lt_dist_of_ne_of_not_dist_two (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {z a : V} (hz : c z = 0) (ha : c a = 0)
    (hne : z ≠ a) (h2 : Γ.dist z a ≠ 2) : 2 < Γ.dist z a := by
  have heven : Even (Γ.dist z a) := (hP.eq_iff_even_dist c z a).1 (hz.trans ha.symm)
  have hle : Γ.dist z a ≤ 4 := hP.dist_le (by norm_num) z a
  have hpos : Γ.dist z a ≠ 0 := by
    intro h0
    exact hne ((hP.connected.dist_eq_zero_iff).mp h0)
  obtain ⟨k, hk⟩ := heven
  omega

theorem mem_varianceZ_of_forall {c : Γ.Coloring (Fin 2)} {X : Finset V} {z : V}
    (hz0 : c z = 0) (hz : ∀ a ∈ X, 2 < Γ.dist z a) : z ∈ varianceZ Γ c X := by
  classical
  rw [mem_varianceZ]
  exact ⟨hz0, hz⟩

@[expose] noncomputable def varianceLinesMissing (Γ : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel Γ.Adj] (u : V) (X : Finset V) : Finset V :=
  (Γ.neighborFinset u).filter fun L => ∀ a ∈ X, ¬ Γ.Adj L a

theorem card_erase_neighborFinset_of_line [DecidableEq V] {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {u L : V}
    (huL : Γ.Adj u L) (hL : c L = 1) :
    ((Γ.neighborFinset L).erase u).card = s := by
  rw [Finset.card_erase_of_mem (by simpa using huL.symm)]
  rw [card_neighborFinset_eq_degree, degree_eq_s_add_one_of_color_one hdeg hL]
  omega

theorem varianceLinesMissing_card [DecidableEq V] (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {u : V} (hu : u ∈ varianceTrace Γ x y) :
    (varianceLinesMissing Γ u X).card = t + 1 - X.card := by
  classical
  let N := Γ.neighborFinset u
  let Meet := N.filter fun L => ∃ a ∈ X, Γ.Adj L a
  have hNcard : N.card = t + 1 := by
    rw [show N = Γ.neighborFinset u from rfl, card_neighborFinset_eq_degree,
      degree_eq_t_add_one_of_color_zero hdeg
        (color_eq_zero_of_mem_varianceTrace hP hx hu)]
  have hmiss : varianceLinesMissing Γ u X = N \ Meet := by
    ext L
    simp only [varianceLinesMissing, N, Meet, Finset.mem_filter, Finset.mem_sdiff,
      not_exists, not_and]
    tauto
  have hMeetSub : Meet ⊆ N := Finset.filter_subset _ _
  have hcardMiss : (N \ Meet).card = N.card - Meet.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hMeetSub]
  let f : {a // a ∈ X} → V := fun a =>
    commonNeighbor hP (dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy
      (hX a.2) hu)
  have hMeetEq : Meet = X.attach.image f := by
    ext L
    constructor
    · intro hL
      have hL' : L ∈ N ∧ ∃ a ∈ X, Γ.Adj L a := by
        simpa only [Meet, Finset.mem_filter] using hL
      obtain ⟨hLN, hL2⟩ := hL'
      obtain ⟨a, haX, hLa⟩ := hL2
      have hu' : u ∈ traceSet Γ x y := by simpa [mem_varianceTrace] using hu
      have hua : Γ.dist a u = 2 :=
        dist_eq_two_of_mem_span_of_mem_trace hP hT hxy (hX haX) hu'
      have hfa : f ⟨a, haX⟩ = commonNeighbor hP hua := by
        dsimp only [f]
      have hLN' : Γ.Adj u L := by simpa [N] using hLN
      have hLaeq : L = f ⟨a, haX⟩ := by
        rw [hfa]
        exact eq_commonNeighbor hP hua hLa.symm hLN'
      exact Finset.mem_image.mpr ⟨⟨a, haX⟩, Finset.mem_attach _ _, hLaeq.symm⟩
    · intro hL
      obtain ⟨a, -, haeq⟩ := Finset.mem_image.mp hL
      have hu' : u ∈ traceSet Γ x y := by simpa [mem_varianceTrace] using hu
      have hua : Γ.dist a.1 u = 2 :=
        dist_eq_two_of_mem_span_of_mem_trace hP hT hxy (hX a.2) hu'
      have hfa : f a = commonNeighbor hP hua := by
        dsimp only [f]
      refine Finset.mem_filter.mpr ⟨?_, ⟨a.1, a.2, ?_⟩⟩
      · rw [← haeq]
        change f a ∈ Γ.neighborFinset u
        rw [mem_neighborFinset, hfa]
        exact commonNeighbor_adj_right hP hua
      · rw [← haeq, hfa]
        exact (commonNeighbor_adj_left hP hua).symm
  have hfinj : Set.InjOn f (X.attach : Set {a // a ∈ X}) := by
    intro a _ a' _ haeq
    by_contra hne
    have hne' : a.1 ≠ a'.1 := fun h => hne (Subtype.ext h)
    have h4 : Γ.dist a.1 a'.1 = 4 :=
      dist_eq_four_of_mem_span hP hT hxy (hX a.2) (hX a'.2) hne'
    have hu' : u ∈ traceSet Γ x y := by simpa [mem_varianceTrace] using hu
    have hua : Γ.dist a.1 u = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT hxy (hX a.2) hu'
    have hua' : Γ.dist a'.1 u = 2 :=
      dist_eq_two_of_mem_span_of_mem_trace hP hT hxy (hX a'.2) hu'
    have hfa : f a = commonNeighbor hP hua := by
      dsimp only [f]
    have hfa' : f a' = commonNeighbor hP hua' := by
      dsimp only [f]
    have hLa : Γ.Adj (f a) a.1 := by
      rw [hfa]
      exact (commonNeighbor_adj_left hP hua).symm
    have hLa' : Γ.Adj (f a) a'.1 := by
      rw [haeq, hfa']
      exact (commonNeighbor_adj_left hP hua').symm
    have h2 : Γ.dist a.1 a'.1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLa.symm hLa' hne'
    omega
  have hMeetCard : Meet.card = X.card := by
    rw [hMeetEq, Finset.card_image_of_injOn hfinj, Finset.card_attach]
  rw [hmiss, hcardMiss, hMeetCard, hNcard]

theorem eq_of_adj_of_dist_two_of_not_adj (hP : IsGeneralizedPolygon Γ 4)
    {c : Γ.Coloring (Fin 2)} {a L z u : V} (haL : ¬ Γ.Adj a L)
    (hLz : Γ.Adj L z) (hLu : Γ.Adj L u) (haz : Γ.dist a z = 2)
    (hau : Γ.dist a u = 2) : z = u := by
  have hca : c a ≠ c L := by
    intro h
    have h1 : c a = c z := (hP.eq_iff_even_dist c a z).2 (by rw [haz]; norm_num)
    exact (c.valid hLz) (h.symm.trans h1)
  have hdist : Γ.dist a L = 3 := dist_eq_three_of_not_adj_of_color_ne hP c haL hca
  exact (existsUnique_proj hP hdist).unique ⟨hLz, haz⟩ ⟨hLu, hau⟩

theorem dist_eq_two_of_le_two_of_mem_varianceZ_of_mem_varianceTrace
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) {z u : V}
    (hz : z ∈ varianceZ Γ c X) (hu : u ∈ varianceTrace Γ x y)
    (hle : Γ.dist z u ≤ 2) : Γ.dist z u = 2 := by
  have hzMem : z ∈ varianceZ Γ c X := hz
  rw [mem_varianceZ] at hz
  have hcu : c u = 0 := color_eq_zero_of_mem_varianceTrace hP hx hu
  have heven : Even (Γ.dist z u) :=
    (hP.eq_iff_even_dist c z u).1 (hz.1.trans hcu.symm)
  have hne0 : Γ.dist z u ≠ 0 := by
    intro h0
    have hzu : z = u := (hP.connected.dist_eq_zero_iff).mp h0
    exact not_mem_varianceTrace_of_mem_varianceZ hP hT hxy hX hm (hzu ▸ hzMem) hu
  obtain ⟨k, hk⟩ := heven
  omega

theorem varianceZ_filter_eq_biUnion [DecidableEq V]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {u : V} (hu : u ∈ varianceTrace Γ x y) :
    (varianceZ Γ c X).filter (fun z => Γ.dist z u = 2)
      = (varianceLinesMissing Γ u X).biUnion fun L => (Γ.neighborFinset L).erase u := by
  classical
  ext z
  constructor
  · intro hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzZ, hzu⟩ := hz
    rw [mem_varianceZ] at hzZ
    obtain ⟨hz0, hzfar⟩ := hzZ
    let L := commonNeighbor hP hzu
    have hLz : Γ.Adj L z := (commonNeighbor_adj_left hP hzu).symm
    have hLu : Γ.Adj L u := (commonNeighbor_adj_right hP hzu).symm
    have hLmiss : L ∈ varianceLinesMissing Γ u X := by
      rw [varianceLinesMissing, Finset.mem_filter]
      refine ⟨by simpa using hLu.symm, ?_⟩
      intro a haX hLa
      have hza : Γ.dist z a = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP hLz.symm hLa (by
          intro h
          have hlt := hzfar a haX
          rw [h] at hlt
          simp at hlt)
      have := hzfar a haX
      omega
    refine Finset.mem_biUnion.mpr ⟨L, hLmiss, ?_⟩
    rw [Finset.mem_erase, mem_neighborFinset]
    refine ⟨?_, hLz⟩
    intro h
    subst h
    simp at hzu
  · intro hz
    obtain ⟨L, hLmiss, hzL⟩ := Finset.mem_biUnion.mp hz
    rw [varianceLinesMissing, Finset.mem_filter] at hLmiss
    obtain ⟨hLu_mem, hLmissX⟩ := hLmiss
    rw [mem_neighborFinset] at hLu_mem
    rw [Finset.mem_erase, mem_neighborFinset] at hzL
    obtain ⟨hzu_ne, hLz⟩ := hzL
    have hzu : Γ.dist z u = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hLz.symm hLu_mem.symm
        (by intro h; exact hzu_ne h)
    have hcu : c u = 0 := color_eq_zero_of_mem_varianceTrace hP hx hu
    have hcz : c z = 0 := by
      rw [← hcu]
      exact (hP.eq_iff_even_dist c z u).2 (by rw [hzu]; norm_num)
    have hzfar : ∀ a ∈ X, 2 < Γ.dist z a := by
      intro a haX
      have hca : c a = 0 := color_eq_zero_of_mem_span hP hT hx hxy (hX haX)
      have hzane : z ≠ a := by
        intro h
        exact hLmissX a haX (by simpa [h] using hLz)
      have hza2 : Γ.dist z a ≠ 2 := by
        intro hza
        have hau : Γ.dist a u = 2 :=
          dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu
        have haL : ¬ Γ.Adj a L := fun h => hLmissX a haX h.symm
        have hzu_eq : z = u :=
          eq_of_adj_of_dist_two_of_not_adj (hP := hP) (c := c) haL hLz hLu_mem.symm
            (by rw [SimpleGraph.dist_comm]; exact hza) hau
        exact hzu_ne hzu_eq
      exact two_lt_dist_of_ne_of_not_dist_two hP hcz hca hzane hza2
    rw [Finset.mem_filter]
    exact ⟨mem_varianceZ_of_forall hcz hzfar, hzu⟩

theorem disjoint_erase_neighborFinset [DecidableEq V] (hP : IsGeneralizedPolygon Γ 4)
    {u L L' : V} (hL : L ∈ Γ.neighborFinset u) (hL' : L' ∈ Γ.neighborFinset u)
    (hne : L ≠ L') :
    Disjoint ((Γ.neighborFinset L).erase u) ((Γ.neighborFinset L').erase u) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [Finset.mem_erase, mem_neighborFinset] at hz hz'
  obtain ⟨hzu, hLz⟩ := hz
  obtain ⟨-, hL'z⟩ := hz'
  rw [mem_neighborFinset] at hL hL'
  have hzu2 : Γ.dist z u = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hLz.symm hL.symm hzu
  have e1 : L = commonNeighbor hP hzu2 :=
    eq_commonNeighbor hP hzu2 hLz.symm hL
  have e2 : L' = commonNeighbor hP hzu2 :=
    eq_commonNeighbor hP hzu2 hL'z.symm hL'
  exact hne (e1.trans e2.symm)

theorem sum_centres (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    ∑ z ∈ varianceZ Γ c X, varianceTz Γ (varianceTrace Γ x y) z
      = (t + 1) * (t + 1 - X.card) * s := by
  classical
  have hstep : ∀ z ∈ varianceZ Γ c X,
      varianceTz Γ (varianceTrace Γ x y) z
        = ∑ u ∈ varianceTrace Γ x y, if Γ.dist z u = 2 then 1 else 0 := by
    intro z hz
    rw [varianceTz, Finset.card_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hiff := dist_eq_two_of_le_two_of_mem_varianceZ_of_mem_varianceTrace
      hP hT c hdeg hx hxy hX hm hz hu
    by_cases h2 : Γ.dist z u = 2
    · rw [if_pos (le_of_eq h2), if_pos h2]
    · rw [if_neg (by intro hle; exact h2 (hiff hle)), if_neg h2]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ u ∈ varianceTrace Γ x y,
      ∑ z ∈ varianceZ Γ c X, (if Γ.dist z u = 2 then 1 else 0)
        = s * (t + 1 - X.card) := by
    intro u hu
    rw [← Finset.card_filter]
    rw [varianceZ_filter_eq_biUnion hP hT c hdeg hx hxy hX hu]
    rw [Finset.card_biUnion]
    · calc
        ∑ L ∈ varianceLinesMissing Γ u X, ((Γ.neighborFinset L).erase u).card
            = ∑ L ∈ varianceLinesMissing Γ u X, s := by
              refine Finset.sum_congr rfl fun L hL => ?_
              have hLf : L ∈ varianceLinesMissing Γ u X := hL
              rw [varianceLinesMissing, Finset.mem_filter, mem_neighborFinset] at hLf
              exact card_erase_neighborFinset_of_line hdeg hLf.1
                (color_eq_one_of_adj_of_color_eq_zero
                  (color_eq_zero_of_mem_varianceTrace hP hx hu) hLf.1)
        _ = (varianceLinesMissing Γ u X).card • s := Finset.sum_const s
        _ = (t + 1 - X.card) * s := by
              rw [varianceLinesMissing_card hP hT c hdeg hx hxy hX hu, smul_eq_mul]
        _ = s * (t + 1 - X.card) := by rw [Nat.mul_comm]
    · intro L hL L' hL' hne
      have hLmem : L ∈ Γ.neighborFinset u := by
        have hLf : L ∈ varianceLinesMissing Γ u X := hL
        rw [varianceLinesMissing, Finset.mem_filter] at hLf
        exact hLf.1
      have hL'mem : L' ∈ Γ.neighborFinset u := by
        have hLf : L' ∈ varianceLinesMissing Γ u X := hL'
        rw [varianceLinesMissing, Finset.mem_filter] at hLf
        exact hLf.1
      exact disjoint_erase_neighborFinset hP hLmem hL'mem hne
  rw [Finset.sum_congr rfl hinner, Finset.sum_const,
    varianceTrace_card hP c hdeg hx hxy, smul_eq_mul]
  ring

theorem sum_ite_pair_ne [DecidableEq V] (T : Finset V) (p : V → Prop) [DecidablePred p] :
    (∑ u ∈ T, ∑ u' ∈ T, if u' ≠ u ∧ p u ∧ p u' then 1 else 0)
      = (T.filter p).card * ((T.filter p).card - 1) := by
  classical
  let S := T.filter p
  have hinner : ∀ u, (∑ u' ∈ T, if u' ≠ u ∧ p u ∧ p u' then 1 else 0)
      = if p u then (S.erase u).card else 0 := by
    intro u
    by_cases hu : p u
    · rw [if_pos hu]
      have hS : (S.erase u).card = (T.filter fun u' => p u' ∧ u' ≠ u).card := by
        congr 1
        ext u'
        simp [S, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
      rw [hS, Finset.card_filter]
      refine Finset.sum_congr rfl fun u' _ => ?_
      by_cases h1 : p u' <;> by_cases h2 : u' ≠ u <;> simp [h1, h2, hu]
    · rw [if_neg hu]
      refine Finset.sum_eq_zero fun u' _ => ?_
      simp [hu]
  calc
    (∑ u ∈ T, ∑ u' ∈ T, if u' ≠ u ∧ p u ∧ p u' then 1 else 0)
        = ∑ u ∈ T, if p u then (S.erase u).card else 0 :=
          Finset.sum_congr rfl fun u _ => hinner u
    _ = ∑ u ∈ S, (S.erase u).card := by
          rw [← Finset.sum_filter]
    _ = ∑ u ∈ S, (S.card - 1) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [Finset.card_erase_of_mem hu]
    _ = S.card * (S.card - 1) := by
          rw [Finset.sum_const, smul_eq_mul]

theorem varianceZ_filter_eq_trace_sdiff [DecidableEq V]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {u u' : V}
    (hu : u ∈ varianceTrace Γ x y) (hu' : u' ∈ varianceTrace Γ x y) (hne : u ≠ u') :
    (varianceZ Γ c X).filter (fun z => Γ.dist z u = 2 ∧ Γ.dist z u' = 2)
      = varianceTrace Γ u u' \ X := by
  classical
  ext z
  constructor
  · intro hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzZ, hzu, hzu'⟩ := hz
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [mem_varianceTrace]
      exact ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩
    · intro hzX
      rw [mem_varianceZ] at hzZ
      have hlt := hzZ.2 z hzX
      simp at hlt
  · intro hz
    rw [Finset.mem_sdiff] at hz
    obtain ⟨hzT, hzX⟩ := hz
    rw [mem_varianceTrace] at hzT
    have hzu : Γ.dist z u = 2 := by
      rw [SimpleGraph.dist_comm]; exact hzT.1
    have hzu' : Γ.dist z u' = 2 := by
      rw [SimpleGraph.dist_comm]; exact hzT.2
    have hcu : c u = 0 := color_eq_zero_of_mem_varianceTrace hP hx hu
    have hcz : c z = 0 := by
      rw [← hcu]
      exact (hP.eq_iff_even_dist c z u).2 (by rw [hzu]; norm_num)
    have huu' : Γ.dist u u' = 4 :=
      dist_eq_four_of_mem_varianceTrace hP hxy hu hu' hne
    have hzfar : ∀ a ∈ X, 2 < Γ.dist z a := by
      intro a haX
      have haT : a ∈ traceSet Γ u u' := by
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu
        · rw [SimpleGraph.dist_comm]
          exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu'
      have hzTset : z ∈ traceSet Γ u u' := by
        simpa [mem_varianceTrace] using hzT
      have hza : z ≠ a := by
        intro h
        exact hzX (by simpa [h] using haX)
      have h4 : Γ.dist z a = 4 :=
        dist_eq_four_of_mem_trace hP huu' hzTset haT hza
      omega
    rw [Finset.mem_filter]
    exact ⟨mem_varianceZ_of_forall hcz hzfar, hzu, hzu'⟩

theorem card_varianceZ_filter_trace [DecidableEq V]
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {x y : V} (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) {u u' : V}
    (hu : u ∈ varianceTrace Γ x y) (hu' : u' ∈ varianceTrace Γ x y) (hne : u ≠ u') :
    ((varianceZ Γ c X).filter (fun z => Γ.dist z u = 2 ∧ Γ.dist z u' = 2)).card
      = t + 1 - X.card := by
  classical
  rw [varianceZ_filter_eq_trace_sdiff hP hT c hdeg hx hxy hX hu hu' hne]
  have hXsub : X ⊆ varianceTrace Γ u u' := by
    intro a haX
    rw [mem_varianceTrace]
    exact ⟨by rw [SimpleGraph.dist_comm];
              exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu,
           by rw [SimpleGraph.dist_comm];
              exact dist_eq_two_of_mem_span_of_mem_varianceTrace hP hT hxy (hX haX) hu'⟩
  rw [Finset.card_sdiff_of_subset hXsub]
  have huu' : Γ.dist u u' = 4 :=
    dist_eq_four_of_mem_varianceTrace hP hxy hu hu' hne
  rw [varianceTrace_card hP c hdeg (color_eq_zero_of_mem_varianceTrace hP hx hu) huu']

theorem sum_centres_choose_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {x y : V}
    (hx : c x = 0) (hxy : Γ.dist x y = 4) {X : Finset V}
    (hX : (X : Set V) ⊆ spanSet Γ x y) (hm : 2 ≤ X.card) :
    ∑ z ∈ varianceZ Γ c X,
        varianceTz Γ (varianceTrace Γ x y) z * (varianceTz Γ (varianceTrace Γ x y) z - 1)
      = (t + 1) * t * (t + 1 - X.card) := by
  classical
  have hstep : ∀ z ∈ varianceZ Γ c X,
      varianceTz Γ (varianceTrace Γ x y) z * (varianceTz Γ (varianceTrace Γ x y) z - 1)
        = ∑ u ∈ varianceTrace Γ x y, ∑ u' ∈ varianceTrace Γ x y,
            (if u' ≠ u ∧ Γ.dist z u = 2 ∧ Γ.dist z u' = 2 then 1 else 0) := by
    intro z hz
    have hTz : (varianceTrace Γ x y).filter (fun u => Γ.dist z u ≤ 2)
        = (varianceTrace Γ x y).filter (fun u => Γ.dist z u = 2) := by
      ext u
      by_cases hu : u ∈ varianceTrace Γ x y
      · have hiff := dist_eq_two_of_le_two_of_mem_varianceZ_of_mem_varianceTrace
          hP hT c hdeg hx hxy hX hm hz hu
        simp only [Finset.mem_filter, hu, true_and]
        exact ⟨hiff, fun h => le_of_eq h⟩
      · simp [hu]
    rw [varianceTz, hTz]
    exact (sum_ite_pair_ne (varianceTrace Γ x y) (fun u => Γ.dist z u = 2)).symm
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  have hpair : ∀ u ∈ varianceTrace Γ x y, ∀ u' ∈ varianceTrace Γ x y,
      (∑ z ∈ varianceZ Γ c X,
          (if u' ≠ u ∧ Γ.dist z u = 2 ∧ Γ.dist z u' = 2 then 1 else 0))
        = if u' = u then 0 else t + 1 - X.card := by
    intro u hu u' hu'
    by_cases heq : u' = u
    · rw [if_pos heq]
      refine Finset.sum_eq_zero fun z _ => ?_
      simp [heq]
    · rw [if_neg heq]
      have hne : u ≠ u' := fun h => heq h.symm
      rw [← Finset.card_filter]
      have hfilter : (varianceZ Γ c X).filter
            (fun z => u' ≠ u ∧ Γ.dist z u = 2 ∧ Γ.dist z u' = 2)
          = (varianceZ Γ c X).filter (fun z => Γ.dist z u = 2 ∧ Γ.dist z u' = 2) := by
        ext z
        simp [heq]
      rw [hfilter]
      exact card_varianceZ_filter_trace hP hT c hdeg hx hxy hX hu hu' hne
  rw [Finset.sum_congr rfl (fun u hu =>
    Finset.sum_congr rfl (fun u' hu' => hpair u hu u' hu'))]
  have houter : ∀ u ∈ varianceTrace Γ x y,
      (∑ u' ∈ varianceTrace Γ x y, if u' = u then 0 else t + 1 - X.card)
        = t * (t + 1 - X.card) := by
    intro u hu
    rw [← Finset.sum_erase_add (varianceTrace Γ x y)
      (fun u' => if u' = u then 0 else t + 1 - X.card) hu]
    simp only [if_true, add_zero]
    rw [Finset.sum_congr rfl (fun x hx => by
      rw [if_neg]
      exact (Finset.mem_erase.mp hx).1)]
    rw [Finset.sum_const, Finset.card_erase_of_mem hu,
      varianceTrace_card hP c hdeg hx hxy, smul_eq_mul]
    congr 1
  rw [Finset.sum_congr rfl houter, Finset.sum_const,
    varianceTrace_card hP c hdeg hx hxy, smul_eq_mul]
  ring

end Basic

end CFSG.Geometry.GeneralizedQuadrangles

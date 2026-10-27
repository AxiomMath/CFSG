module

public import CFSG.Combinatorics.PeriodicHexagonIsomorphismSupport
public import CFSG.Combinatorics.OuterLayerExtensionLines

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.HexagonPeriodicPropagation
  CFSG.Combinatorics.AperiodicOppositeComponents

namespace CFSG.Combinatorics.OuterLayer

universe u u'

variable {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
  {col : G.Coloring Bool} {col' : G'.Coloring Bool} {w : {v : V // col v = false}}
  {w' : {v : V' // col' v = false}} {ℓ : Fin 3 → V} {ℓ' : Fin 3 → V'}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}} {p' : Fin 3 → Fin 2 → {v : V' // col' v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {z' q' : {v : V' // col' v = false} → {v : V' // col' v = false} → {v : V' // col' v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {c' : {v : V' // col' v = false} → {v : V' // col' v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {ε' : {v : V' // col' v = false} → {v : V' // col' v = false} → Fin 2}

theorem third_eq_map (F : IsFrame G col w ℓ p z q c ε)
    (F' : IsFrame G' col' w' ℓ' p' z' q' c' ε')
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x)
    (hper' : ∃ x, IsHex G' col' w' x ∧ IsPeriodic c' x)
    (φ : oppGraph G col w ≃g oppGraph G' col' w')
    (hφ : ∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b)
    {x y x' y' : oppSet G col w} (hxy : (oppGraph G col w).Adj x y)
    (hxy' : (oppGraph G col w).Adj x' y') (h : z x' y' = z x y) :
    z' (φ x') (φ y') = z' (φ x) (φ y) := by
  obtain ⟨i, j, hij, hjk, hik⟩ : ∃ i j : Fin 3, i ≠ j ∧ j ≠ c x y ∧ i ≠ c x y := by
    have key : ∀ k : Fin 3, ∃ i j : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k := by decide
    exact key _
  have step : ∀ (a : oppSet G col w) (l : Fin 3), ∃ b : oppSet G col w,
      (oppGraph G col w).Adj a b ∧ c a b = l := fun a l => by
    obtain ⟨b, hb, hab, hc⟩ := F.exists_colour a.2 l
    exact ⟨⟨b, hb⟩, hab, hc⟩
  obtain ⟨x₂, a₁, c₁⟩ := step y i
  obtain ⟨x₃, a₂, c₂⟩ := step x₂ j
  obtain ⟨x₄, a₃, c₃⟩ := step x₃ i
  obtain ⟨x₅, a₄, c₄⟩ := step x₄ j
  obtain ⟨x₆, a₅, c₅⟩ := step x₅ (c x y)
  have hsymm' : ∀ a b : oppSet G' col' w', (oppGraph G' col' w').Adj a b → z' b a = z' a b :=
    fun a b hab => (frame_symm F'.moore col' F'.inj F'.root F'.line F'.ne F'.label F'.data a.2 b.2
      hab).1
  have hφa : ∀ {a b : oppSet G col w}, (oppGraph G col w).Adj a b →
      (oppGraph G' col' w').Adj (φ a) (φ b) := fun hab => φ.map_adj_iff.mpr hab
  rcases eq_of_third_eq F hper hij hjk hik x.2 y.2 x₂.2 x₃.2 x₄.2 x₅.2 x₆.2 hxy a₁ a₂ a₃ a₄ a₅ rfl
    c₁ c₂ c₃ c₄ c₅ x'.2 y'.2 hxy' h with (⟨e1, e2⟩ | ⟨e1, e2⟩) | (⟨e1, e2⟩ | ⟨e1, e2⟩)
  · rw [Subtype.ext e1, Subtype.ext e2]
  · rw [Subtype.ext e1, Subtype.ext e2]
    exact hsymm' _ _ (hφa hxy)
  ·
    rw [Subtype.ext e1, Subtype.ext e2]
    exact ((third_eq_of_walk F' hper' hij hjk hik (φ x).2 (φ y).2 (φ x₂).2 (φ x₃).2 (φ x₄).2
      (φ x₅).2 (φ x₆).2 (hφa hxy) (hφa a₁) (hφa a₂) (hφa a₃) (hφa a₄) (hφa a₅)
      ((hφ _ _ hxy).trans rfl) ((hφ _ _ a₁).trans c₁) ((hφ _ _ a₂).trans c₂)
      ((hφ _ _ a₃).trans c₃) ((hφ _ _ a₄).trans c₄) ((hφ _ _ a₅).trans c₅)).2).symm
  · rw [Subtype.ext e1, Subtype.ext e2, hsymm' _ _ (hφa a₅)]
    exact ((third_eq_of_walk F' hper' hij hjk hik (φ x).2 (φ y).2 (φ x₂).2 (φ x₃).2 (φ x₄).2
      (φ x₅).2 (φ x₆).2 (hφa hxy) (hφa a₁) (hφa a₂) (hφa a₃) (hφa a₄) (hφa a₅)
      ((hφ _ _ hxy).trans rfl) ((hφ _ _ a₁).trans c₁) ((hφ _ _ a₂).trans c₂)
      ((hφ _ _ a₃).trans c₃) ((hφ _ _ a₄).trans c₄) ((hφ _ _ a₅).trans c₅)).2).symm

theorem exists_third_map (F : IsFrame G col w ℓ p z q c ε)
    (F' : IsFrame G' col' w' ℓ' p' z' q' c' ε')
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x)
    (hper' : ∃ x, IsHex G' col' w' x ∧ IsPeriodic c' x)
    (φ : oppGraph G col w ≃g oppGraph G' col' w')
    (hφ : ∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b) :
    ∃ ψ : {v : V // col v = false} → {v : V' // col' v = false}, ∀ x y : oppSet G col w,
      (oppGraph G col w).Adj x y → ψ (z x y) = z' (φ x) (φ y) := by
  have key : ∀ t : {v : V // col v = false}, ∃ t' : {v : V' // col' v = false},
      ∀ x y : oppSet G col w, (oppGraph G col w).Adj x y → z x y = t →
        t' = z' (φ x) (φ y) := by
    intro t
    by_cases h : ∃ x y : oppSet G col w, (oppGraph G col w).Adj x y ∧ z x y = t
    · obtain ⟨x₀, y₀, h₀, ht⟩ := h
      exact ⟨z' (φ x₀) (φ y₀), fun x y hxy hz =>
        (third_eq_map F F' hper hper' φ hφ h₀ hxy (hz.trans ht.symm)).symm⟩
    · exact ⟨w', fun x y hxy hz => absurd ⟨x, y, hxy, hz⟩ h⟩
  choose ψ hψ using key
  exact ⟨ψ, fun x y hxy => hψ _ x y hxy rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype V'] [DecidableEq V']
  [DecidableRel G'.Adj] in
theorem colour_symm (φ : oppGraph G col w ≃g oppGraph G' col' w')
    (hφ : ∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b) :
    ∀ a b, (oppGraph G' col' w').Adj a b → c (φ.symm a) (φ.symm b) = c' a b := by
  intro a b hab
  have h := hφ (φ.symm a) (φ.symm b) (φ.symm.map_adj_iff.mpr hab)
  rw [RelIso.apply_symm_apply, RelIso.apply_symm_apply] at h
  exact h.symm

theorem exists_outer_iso (F : IsFrame G col w ℓ p z q c ε)
    (F' : IsFrame G' col' w' ℓ' p' z' q' c' ε')
    (hper : ∃ x, IsHex G col w x ∧ IsPeriodic c x)
    (hper' : ∃ x, IsHex G' col' w' x ∧ IsPeriodic c' x)
    (φ : oppGraph G col w ≃g oppGraph G' col' w')
    (hφ : ∀ a b, (oppGraph G col w).Adj a b → c' (φ a) (φ b) = c a b) :
    ∃ χ : (outerSystem G col w 2).Iso (outerSystem G' col' w' 2),
      ∀ (x : (outerSystem G col w 2).Pt) (hx : (pointGraph G col).dist w x.1 = 3),
        (χ.pts x).1 = (φ ⟨x.1, hx⟩).1 := by
  obtain ⟨ψ, hψ⟩ := exists_third_map F F' hper hper' φ hφ
  obtain ⟨ψ', hψ'⟩ := exists_third_map F' F hper' hper φ.symm (colour_symm φ hφ)
  have hle : ∀ x : {v : V // col v = false}, (pointGraph G col).dist w x ≤ 3 := fun x => by
    rw [(point_dist F.moore.conn col w x).1]
    have := dist_le_six F.moore.cyc F.moore.conn col F.moore.deg F.moore.card (w : V) x
    omega
  have hle' : ∀ x : {v : V' // col' v = false}, (pointGraph G' col').dist w' x ≤ 3 := fun x => by
    rw [(point_dist F'.moore.conn col' w' x).1]
    have := dist_le_six F'.moore.cyc F'.moore.conn col' F'.moore.deg F'.moore.card (w' : V') x
    omega
  have hψ2 : ∀ t, (pointGraph G col).dist w t = 2 →
      (pointGraph G' col').dist w' (ψ t) = 2 ∧ ψ' (ψ t) = t := by
    intro t ht
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := exists_edge_of_dist_two F ht
    have e : ψ (z x y) = z' (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) := hψ ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : (oppGraph G' col' w').Adj (φ ⟨x, hx⟩) (φ ⟨y, hy⟩) := φ.map_adj_iff.mpr hxy
    rw [e]
    obtain ⟨-, -, -, -, -, h2⟩ := edge_line F' (φ ⟨x, hx⟩).2 (φ ⟨y, hy⟩).2 hxy'
    refine ⟨h2, ?_⟩
    rw [hψ' _ _ hxy', RelIso.symm_apply_apply, RelIso.symm_apply_apply]
  have hψ2' : ∀ t, (pointGraph G' col').dist w' t = 2 →
      (pointGraph G col).dist w (ψ' t) = 2 ∧ ψ (ψ' t) = t := by
    intro t ht
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := exists_edge_of_dist_two F' ht
    have e : ψ' (z' x y) = z (φ.symm ⟨x, hx⟩) (φ.symm ⟨y, hy⟩) := hψ' ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : (oppGraph G col w).Adj (φ.symm ⟨x, hx⟩) (φ.symm ⟨y, hy⟩) :=
      φ.symm.map_adj_iff.mpr hxy
    rw [e]
    obtain ⟨-, -, -, -, -, h2⟩ := edge_line F (φ.symm ⟨x, hx⟩).2 (φ.symm ⟨y, hy⟩).2 hxy'
    refine ⟨h2, ?_⟩
    rw [hψ _ _ hxy', RelIso.apply_symm_apply, RelIso.apply_symm_apply]
  have hΦex : ∀ x : {v : V // col v = false}, ∃ x' : {v : V' // col' v = false},
      (∀ h : (pointGraph G col).dist w x = 3, x' = (φ ⟨x, h⟩).1) ∧
        ((pointGraph G col).dist w x ≠ 3 → x' = ψ x) := by
    intro x
    by_cases h : (pointGraph G col).dist w x = 3
    · exact ⟨(φ ⟨x, h⟩).1, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨ψ x, fun h' => absurd h' h, fun _ => rfl⟩
  choose Φ hΦ using hΦex
  have hΦex' : ∀ x : {v : V' // col' v = false}, ∃ x' : {v : V // col v = false},
      (∀ h : (pointGraph G' col').dist w' x = 3, x' = (φ.symm ⟨x, h⟩).1) ∧
        ((pointGraph G' col').dist w' x ≠ 3 → x' = ψ' x) := by
    intro x
    by_cases h : (pointGraph G' col').dist w' x = 3
    · exact ⟨(φ.symm ⟨x, h⟩).1, fun _ => rfl, fun h' => absurd h h'⟩
    · exact ⟨ψ' x, fun h' => absurd h' h, fun _ => rfl⟩
  choose Φ' hΦ' using hΦex'
  have hΦ2 : ∀ x, (pointGraph G col).dist w x = 2 → Φ x = ψ x := fun x hx =>
    (hΦ x).2 (by omega)
  have hΦ2' : ∀ x, (pointGraph G' col').dist w' x = 2 → Φ' x = ψ' x := fun x hx =>
    (hΦ' x).2 (by omega)
  have hdist : ∀ x, 2 ≤ (pointGraph G col).dist w x →
      (pointGraph G' col').dist w' (Φ x) = (pointGraph G col).dist w x := by
    intro x hx
    by_cases h3 : (pointGraph G col).dist w x = 3
    · rw [(hΦ x).1 h3, h3]
      exact (φ ⟨x, h3⟩).2
    · have h2 : (pointGraph G col).dist w x = 2 := by have := hle x; omega
      rw [hΦ2 x h2, h2]
      exact (hψ2 x h2).1
  have hdist' : ∀ x, 2 ≤ (pointGraph G' col').dist w' x →
      (pointGraph G col).dist w (Φ' x) = (pointGraph G' col').dist w' x := by
    intro x hx
    by_cases h3 : (pointGraph G' col').dist w' x = 3
    · rw [(hΦ' x).1 h3, h3]
      exact (φ.symm ⟨x, h3⟩).2
    · have h2 : (pointGraph G' col').dist w' x = 2 := by have := hle' x; omega
      rw [hΦ2' x h2, h2]
      exact (hψ2' x h2).1
  have hleft : ∀ x, 2 ≤ (pointGraph G col).dist w x → Φ' (Φ x) = x := by
    intro x hx
    by_cases h3 : (pointGraph G col).dist w x = 3
    · have h3' : (pointGraph G' col').dist w' (Φ x) = 3 := (hdist x hx).trans h3
      rw [(hΦ' _).1 h3']
      have e : (⟨Φ x, h3'⟩ : oppSet G' col' w') = φ ⟨x, h3⟩ := Subtype.ext ((hΦ x).1 h3)
      rw [e, RelIso.symm_apply_apply]
    · have h2 : (pointGraph G col).dist w x = 2 := by have := hle x; omega
      rw [hΦ2 x h2, hΦ2' _ (hψ2 x h2).1, (hψ2 x h2).2]
  have hright : ∀ x, 2 ≤ (pointGraph G' col').dist w' x → Φ (Φ' x) = x := by
    intro x hx
    by_cases h3 : (pointGraph G' col').dist w' x = 3
    · have h3' : (pointGraph G col).dist w (Φ' x) = 3 := (hdist' x hx).trans h3
      rw [(hΦ _).1 h3']
      have e : (⟨Φ' x, h3'⟩ : oppSet G col w) = φ.symm ⟨x, h3⟩ := Subtype.ext ((hΦ' x).1 h3)
      rw [e, RelIso.apply_symm_apply]
    · have h2 : (pointGraph G' col').dist w' x = 2 := by have := hle' x; omega
      rw [hΦ2' x h2, hΦ2 _ (hψ2' x h2).1, (hψ2' x h2).2]
  let φe : (outerSystem G col w 2).Pt ≃ (outerSystem G' col' w' 2).Pt :=
    { toFun := fun x => ⟨Φ x.1, by rw [hdist x.1 x.2]; exact x.2⟩
      invFun := fun x => ⟨Φ' x.1, by rw [hdist' x.1 x.2]; exact x.2⟩
      left_inv := fun x => Subtype.ext (hleft x.1 x.2)
      right_inv := fun x => Subtype.ext (hright x.1 x.2) }
  have mixed : ∀ a t, (pointGraph G col).dist w a = 3 → (pointGraph G col).dist w t = 2 →
      ((outerGraph G' col' w' 2).Adj (Φ a) (Φ t) ↔ (outerGraph G col w 2).Adj a t) := by
    intro a t ha ht
    have ha' : (pointGraph G' col').dist w' (Φ a) = 3 := (hdist a (by omega)).trans ha
    have ht' : (pointGraph G' col').dist w' (Φ t) = 2 := (hdist t (by omega)).trans ht
    rw [outerGraph_two_adj_iff_mixed F' ha' ht', outerGraph_two_adj_iff_mixed F ha ht,
      (hΦ a).1 ha, hΦ2 t ht]
    constructor
    · rintro ⟨y', hy', hay', hz⟩
      refine ⟨(φ.symm ⟨y', hy'⟩).1, (φ.symm ⟨y', hy'⟩).2, ?_, ?_⟩
      · have h1 : (oppGraph G col w).Adj (φ.symm (φ ⟨a, ha⟩)) (φ.symm ⟨y', hy'⟩) :=
          φ.symm.map_adj_iff.mpr hay'
        rw [RelIso.symm_apply_apply] at h1
        exact h1
      · have hadj : (oppGraph G col w).Adj ⟨a, ha⟩ (φ.symm ⟨y', hy'⟩) := by
          have h1 : (oppGraph G col w).Adj (φ.symm (φ ⟨a, ha⟩)) (φ.symm ⟨y', hy'⟩) :=
            φ.symm.map_adj_iff.mpr hay'
          rwa [RelIso.symm_apply_apply] at h1
        have e := hψ ⟨a, ha⟩ (φ.symm ⟨y', hy'⟩) hadj
        rw [RelIso.apply_symm_apply] at e
        obtain ⟨-, -, -, -, -, h2⟩ := edge_line F ha (φ.symm ⟨y', hy'⟩).2 hadj
        rw [← (hψ2 _ h2).2, ← (hψ2 t ht).2]
        exact congrArg ψ' (e.trans hz)
    · rintro ⟨y, hy, hay, hz⟩
      refine ⟨(φ ⟨y, hy⟩).1, (φ ⟨y, hy⟩).2, φ.map_adj_iff.mpr hay, ?_⟩
      rw [← hz]
      exact (hψ ⟨a, ha⟩ ⟨y, hy⟩ hay).symm
  have hφadj : ∀ x y : (outerSystem G col w 2).Pt,
      (outerGraph G' col' w' 2).Adj (φe x).1 (φe y).1 ↔ (outerGraph G col w 2).Adj x.1 y.1 := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    change (outerGraph G' col' w' 2).Adj (Φ x) (Φ y) ↔ (outerGraph G col w 2).Adj x y
    have hx3 := hle x
    have hy3 := hle y
    by_cases h1 : (pointGraph G col).dist w x = 3 <;> by_cases h2 : (pointGraph G col).dist w y = 3
    · have h1' : (pointGraph G' col').dist w' (Φ x) = 3 := (hdist x hx).trans h1
      have h2' : (pointGraph G' col').dist w' (Φ y) = 3 := (hdist y hy).trans h2
      rw [outerGraph_two_adj_iff F' h1' h2', outerGraph_two_adj_iff F h1 h2, (hΦ x).1 h1,
        (hΦ y).1 h2]
      exact φ.map_adj_iff
    · exact mixed x y h1 (by omega)
    · rw [(outerGraph G' col' w' 2).adj_comm, (outerGraph G col w 2).adj_comm]
      exact mixed y x h2 (by omega)
    · have h1' : (pointGraph G' col').dist w' (Φ x) = 2 := (hdist x hx).trans (by omega)
      have h2' : (pointGraph G' col').dist w' (Φ y) = 2 := (hdist y hy).trans (by omega)
      exact iff_of_false (not_outerGraph_two_adj F'.moore h1' h2')
        (not_outerGraph_two_adj F.moore (by omega) (by omega))
  have hφmk : ∀ x, x ∈ (outerSystem G col w 2).marked ↔
      φe x ∈ (outerSystem G' col' w' 2).marked := by
    rintro ⟨x, hx⟩
    change (pointGraph G col).dist w x = 2 ↔ (pointGraph G' col').dist w' (Φ x) = 2
    rw [hdist x hx]
  obtain ⟨χ, hχ⟩ := exists_iso_of_pts F.moore F'.moore φe hφadj hφmk
  refine ⟨χ, fun x hx => ?_⟩
  rw [hχ]
  exact (hΦ x.1).1 hx

end CFSG.Combinatorics.OuterLayer

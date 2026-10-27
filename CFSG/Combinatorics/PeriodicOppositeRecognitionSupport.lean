module

public import CFSG.Combinatorics.AperiodicOppositeComponentsSupport
public import CFSG.Combinatorics.FourByFourRecognition
public import CFSG.Combinatorics.HexagonLayers

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath

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

theorem rel_of_periodic {S : Set {v : V // col v = false}}
    (hSO : ∀ x ∈ S, (pointGraph G col).dist w x = 3)
    (hSadj : ∀ x ∈ S, ∀ y, (pointGraph G col).dist w y = 3 → (pointGraph G col).Adj x y → y ∈ S)
    (hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → (∀ n, x n ∈ S) →
      IsPeriodic c x)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {x : {v : V // col v = false}}
    (hxS : x ∈ S) : r k (r j (r i (r k (r j (r i x))))) = x := by
  have hx := hSO x hxS
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
    rw [hv₁, hv₂, hv₃, hv₄, F.r_eq hr h₄ hu h4u c4u, F.r_eq hr hu hx h0u.symm cu0]
  ·
    exfalso
    have hS₁ : v₁ ∈ S := hSadj x hxS v₁ h₁ a01
    have hS₂ : v₂ ∈ S := hSadj v₁ hS₁ v₂ h₂ a12
    have hS₃ : v₃ ∈ S := hSadj v₂ hS₂ v₃ h₃ a23
    have hS₄ : v₄ ∈ S := hSadj v₃ hS₃ v₄ h₄ a34
    have hSu : u ∈ S := hSadj x hxS u hu h0u
    have hE : IsHex G col w ![x, v₁, v₂, v₃, v₄, u] := by
      refine ⟨List.nodup_ofFn.mp (by simpa [List.ofFn_succ] using hnd6), fun m => ?_,
        fun m => ?_⟩
      · fin_cases m
        exacts [hx, h₁, h₂, h₃, h₄, hu]
      · fin_cases m
        exacts [a01, a12, a23, a34, h4u, h0u.symm]
    have hES : ∀ m, ![x, v₁, v₂, v₃, v₄, u] m ∈ S := by
      intro m
      fin_cases m
      exacts [hxS, hS₁, hS₂, hS₃, hS₄, hSu]
    obtain ⟨a, b, d, -, -, -, hpat⟩ := hall _ hE hES
    have e1 : c v₁ v₂ = b := hpat 1
    have e4 : c v₄ u = b := hpat 4
    exact hjk ((c12.symm.trans e1).trans (c4u.symm.trans e4).symm)

end CFSG.Combinatorics.HexagonPeriodicPropagation.IsFrame

namespace CFSG.Combinatorics.PeriodicOppositeRecognition

open CFSG.Combinatorics.HexagonPeriodicPropagation CFSG.Combinatorics.AperiodicOppositeComponents
  CFSG.Combinatorics.FourByFourPeriodicGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)

include F hr in
theorem component_recognition (Q : (oppGraph G col w).ConnectedComponent)
    (hall : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → (∀ n, x n ∈ compSet Q) →
      IsPeriodic c x)
    (hpow : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → ∀ x ∈ compSet Q, (r i ∘ r j)^[4] x = x) :
    (∀ x₀ : compSet Q, ∃! φ : Vertex ≃ compSet Q, φ o = x₀ ∧
      ∀ u i, (φ (nbr u i) : {v : V // col v = false}) = r i (φ u)) ∧
      Nat.card (compSet Q) = 32 := by
  have hSO : ∀ x ∈ compSet Q, (pointGraph G col).dist w x = 3 := fun x hx => hx.1
  have hSadj : ∀ x ∈ compSet Q, ∀ y, (pointGraph G col).dist w y = 3 →
      (pointGraph G col).Adj x y → y ∈ compSet Q := fun x hx y hy hxy =>
    mem_compSet_of_adj hx hy hxy
  obtain ⟨hex, hiff, -, -, hcard, -⟩ :=
    periodic_three_involution_relations_recognize_four_by_four_graph (compR hr Q)
      (compR_inv F hr Q) (compR_fix hr Q) (compR_dist hr Q) (compR_conn F hr Q)
      (fun x cy hcy => ⟨(compR_cyc F hr Q x cy hcy).1, (compR_cyc F hr Q x cy hcy).2.1⟩)
      (fun x => Subtype.ext (F.rel_of_periodic hr hSO hSadj hall (by decide) (by decide)
        (by decide) x.2))
      (fun x => Subtype.ext (hpow 1 0 2 (by decide) (by decide) (by decide) x x.2))
      (fun x => Subtype.ext (hpow 2 0 1 (by decide) (by decide) (by decide) x x.2))
  refine ⟨fun x₀ => ?_, hcard⟩
  obtain ⟨φ, ⟨hφo, hφ⟩, huniq⟩ := hex x₀
  refine ⟨φ, ⟨hφo, fun u i => congrArg Subtype.val ((hiff φ).mp hφ u i)⟩, ?_⟩
  rintro ψ ⟨hψo, hψ⟩
  exact huniq ψ ⟨hψo, (hiff ψ).mpr fun u i => Subtype.ext (hψ u i)⟩

include F hr in
theorem isColouredIso_iff (φ : Vertex ≃ oppSet G col w) :
    IsColouredIso (fun i (a b : oppSet G col w) => (oppGraph G col w).Adj a b ∧ c a b = i) φ ↔
      ∀ u i, (φ (nbr u i) : {v : V // col v = false}) = r i (φ u) := by
  constructor
  · intro h u i
    obtain ⟨hadj, hc⟩ := (h i u (nbr u i)).mp ((colourAdj_iff_eq_nbr i u (nbr u i)).mpr rfl)
    exact (F.r_eq hr (φ u).2 (φ (nbr u i)).2 hadj hc).symm
  · intro h i u v
    rw [colourAdj_iff_eq_nbr]
    constructor
    · rintro rfl
      have h' := h u i
      refine ⟨?_, ?_⟩
      · change (pointGraph G col).Adj (φ u) (φ (nbr u i))
        rw [h']
        exact (hr i _ (φ u).2).2.1
      · rw [h']
        exact (hr i _ (φ u).2).2.2
    · rintro ⟨hadj, hc⟩
      exact φ.injective (Subtype.ext ((h u i).trans (F.r_eq hr (φ u).2 (φ v).2 hadj hc)).symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem adj_iff_of_isColouredIso (φ : Vertex ≃ oppSet G col w)
    (hφ : IsColouredIso (fun i (a b : oppSet G col w) => (oppGraph G col w).Adj a b ∧ c a b = i)
      φ) (u v : Vertex) : P4.Adj u v ↔ (oppGraph G col w).Adj (φ u) (φ v) := by
  rw [adj_iff_exists_colourAdj]
  constructor
  · rintro ⟨i, h⟩
    exact ((hφ i u v).mp h).1
  · intro h
    exact ⟨c (φ u) (φ v), (hφ _ u v).mpr ⟨h, rfl⟩⟩

include F in
theorem ncard_oppSet_and_card_points :
    (oppSet G col w).ncard = 32 ∧ Fintype.card {v : V // col v = false} = 63 := by
  obtain ⟨⟨hlay, hle⟩, -⟩ := order_two_hexagon_layers_and_opposite_edge_coordinates G
    F.moore.card F.moore.conn F.moore.deg col F.moore.cyc w ℓ F.inj F.root p F.line F.ne F.label
  have h0 : (univ.filter fun x => (pointGraph G col).dist w x = 0).card = 1 := hlay 0
  have h1 : (univ.filter fun x => (pointGraph G col).dist w x = 1).card = 6 := hlay 1
  have h2 : (univ.filter fun x => (pointGraph G col).dist w x = 2).card = 24 := hlay 2
  have h3 : (univ.filter fun x => (pointGraph G col).dist w x = 3).card = 32 := hlay 3
  refine ⟨?_, ?_⟩
  · rw [show oppSet G col w = ↑(univ.filter fun x => (pointGraph G col).dist w x = 3) by
      ext x
      simp, Set.ncard_coe_finset, h3]
  · have hmaps : ((univ : Finset {v : V // col v = false}) : Set {v : V // col v = false}).MapsTo
        (fun x => (pointGraph G col).dist w x) (range 4 : Finset ℕ) := by
      intro x _
      rw [Finset.mem_coe, Finset.mem_range]
      have := hle x
      show (pointGraph G col).dist w x < 4
      omega
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise hmaps]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3]

end CFSG.Combinatorics.PeriodicOppositeRecognition

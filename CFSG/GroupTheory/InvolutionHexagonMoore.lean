module

public import CFSG.GroupTheory.InvolutionHexagonCycles
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonConnected
public import CFSG.Combinatorics.CubicBipartiteMoore

public section

namespace CFSG.GroupTheory.InvolutionHexagon

open CFSG.Combinatorics.CubicBipartiteMoore CFSG.LinearGroups.UnitaryThreeOverNine

variable {P L : Type*} {inc : P → L → Prop}

variable (inc) in
abbrev mooreGraph : SimpleGraph {v : P ⊕ L // incidenceColoring inc v = false} :=
  SimpleGraph.fromRel fun p q => ∃ ℓ : P ⊕ L, incidenceColoring inc ℓ = true ∧
    (incidenceGraph inc).Adj (p : P ⊕ L) ℓ ∧ (incidenceGraph inc).Adj (q : P ⊕ L) ℓ

variable (inc) in
@[expose] noncomputable def ptEquiv : P ≃ {v : P ⊕ L // incidenceColoring inc v = false} :=
  Equiv.ofBijective (fun p => ⟨Sum.inl p, rfl⟩) ⟨fun p q hpq => by
    have := congrArg Subtype.val hpq
    exact Sum.inl_injective this, by
    rintro ⟨p | ℓ, hv⟩
    · exact ⟨p, rfl⟩
    · exact absurd hv Bool.false_ne_true.symm⟩

theorem ptEquiv_apply (p : P) :
    ((ptEquiv inc p : {v : P ⊕ L // incidenceColoring inc v = false}) : P ⊕ L) = Sum.inl p :=
  rfl

theorem common_neighbour_iff (p q : P) :
    (∃ ℓ : P ⊕ L, incidenceColoring inc ℓ = true ∧
      (incidenceGraph inc).Adj (Sum.inl p) ℓ ∧ (incidenceGraph inc).Adj (Sum.inl q) ℓ) ↔
      Collinear inc p q := by
  constructor
  · rintro ⟨q' | ℓ, hℓ, hp, hq⟩
    · exact absurd hp (not_incidenceGraph_adj_inl_inl p q')
    · exact ⟨ℓ, (incidenceGraph_adj_inl_inr p ℓ).mp hp, (incidenceGraph_adj_inl_inr q ℓ).mp hq⟩
  · rintro ⟨ℓ, hp, hq⟩
    exact ⟨Sum.inr ℓ, rfl, (incidenceGraph_adj_inl_inr p ℓ).mpr hp,
      (incidenceGraph_adj_inl_inr q ℓ).mpr hq⟩

variable (inc) in
@[expose] noncomputable def ptIso : collinearityGraph inc ≃g mooreGraph inc where
  toEquiv := ptEquiv inc
  map_rel_iff' {p q} := by
    rw [mooreGraph, SimpleGraph.fromRel_adj, collinearityGraph, SimpleGraph.fromRel_adj]
    show (ptEquiv inc p ≠ ptEquiv inc q ∧ ((∃ ℓ : P ⊕ L, incidenceColoring inc ℓ = true ∧
      (incidenceGraph inc).Adj (Sum.inl p) ℓ ∧ (incidenceGraph inc).Adj (Sum.inl q) ℓ) ∨
      (∃ ℓ : P ⊕ L, incidenceColoring inc ℓ = true ∧
      (incidenceGraph inc).Adj (Sum.inl q) ℓ ∧ (incidenceGraph inc).Adj (Sum.inl p) ℓ))) ↔ _
    rw [common_neighbour_iff, common_neighbour_iff, (ptEquiv inc).injective.ne_iff]

theorem dist_ptEquiv (p q : P) :
    (mooreGraph inc).dist (ptEquiv inc p) (ptEquiv inc q) = (collinearityGraph inc).dist p q :=
  dist_iso (ptIso inc) p q

theorem HexagonData.hexagon (H : HexagonData inc) :
    Nat.card L = 63 ∧ (incidenceGraph inc).Connected ∧ (incidenceGraph inc).girth = 12 ∧
    (incidenceGraph inc).diam = 6 ∧ (collinearityGraph inc).Connected ∧
    (collinearityGraph inc).diam = 3 ∧
    (∀ (p : P) (k : Fin 4),
      {q : P | (collinearityGraph inc).dist p q = k}.ncard = ![1, 6, 24, 32] k) ∧
    (∀ (p : P) (ℓ : L), ∃! q : P, inc q ℓ ∧
      ∀ q', inc q' ℓ → (collinearityGraph inc).dist p q ≤ (collinearityGraph inc).dist p q') := by
  classical
  have := H.finite_points
  have := H.finite_lines
  have : Fintype (P ⊕ L) := Fintype.ofFinite _
  have : Nonempty (P ⊕ L) := (Nat.card_pos_iff.mp (by rw [H.card_vertices]; norm_num)).1
  have hcard : Fintype.card (P ⊕ L) = 126 := by
    rw [← Nat.card_eq_fintype_card, H.card_vertices]
  have hcyc : ∀ (v : P ⊕ L) (c : (incidenceGraph inc).Walk v v), c.IsCycle → 12 ≤ c.length :=
    fun v c hc => H.twelve_le_length c hc
  have hconn : (incidenceGraph inc).Connected :=
    connected_of_ncard_lt hcyc (incidenceColoring inc) H.ncard_neighborSet
      (by rw [H.card_vertices]; norm_num)
  have hdeg : ∀ v, (incidenceGraph inc).degree v = 3 := fun v => by
    rw [degree_eq_ncard, H.ncard_neighborSet]
  obtain ⟨hgirth, hdiam, -, -, -, -, -, hΓlayer, hΓconn, hΓdiam, hnear, -⟩ :=
    cubic_bipartite_moore_equality_and_nearest_point_property (incidenceGraph inc) hcard hconn
      hdeg (incidenceColoring inc) hcyc
  have hdist := dist_ptEquiv (inc := inc)
  refine ⟨H.card_lines, hconn, hgirth, hdiam,
    (SimpleGraph.Iso.connected_iff (ptIso inc)).mpr hΓconn,
    (diam_iso (ptIso inc)).symm.trans hΓdiam, fun p k => ?_, fun p ℓ => ?_⟩
  ·
    rw [← hΓlayer (ptEquiv inc p) k, ← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective _ (ptEquiv inc).injective]
    congr 1
    ext q'
    obtain ⟨q, rfl⟩ := (ptEquiv inc).surjective q'
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and,
      (ptEquiv inc).injective.eq_iff, exists_eq_right, hdist]
  ·
    obtain ⟨q', ⟨hq'ℓ, hq'min⟩, huniq⟩ := hnear (ptEquiv inc p) (Sum.inr ℓ) rfl
    obtain ⟨q₀, rfl⟩ := (ptEquiv inc).surjective q'
    rw [ptEquiv_apply, incidenceGraph_adj_inl_inr] at hq'ℓ
    have hmin : ∀ q₂, inc q₂ ℓ →
        (collinearityGraph inc).dist p q₀ ≤ (collinearityGraph inc).dist p q₂ := by
      intro q₂ hq₂
      have := hq'min (ptEquiv inc q₂) (by rw [ptEquiv_apply, incidenceGraph_adj_inl_inr]; exact hq₂)
      rwa [hdist, hdist] at this
    refine ⟨q₀, ⟨hq'ℓ, hmin⟩, fun q₁ ⟨hq₁ℓ, hq₁min⟩ =>
      (ptEquiv inc).injective (huniq _ ⟨?_, ?_⟩)⟩
    · rw [ptEquiv_apply, incidenceGraph_adj_inl_inr]
      exact hq₁ℓ
    · intro q'' hq''
      obtain ⟨q₂, rfl⟩ := (ptEquiv inc).surjective q''
      rw [ptEquiv_apply, incidenceGraph_adj_inl_inr] at hq''
      rw [hdist, hdist]
      exact hq₁min q₂ hq''

end CFSG.GroupTheory.InvolutionHexagon

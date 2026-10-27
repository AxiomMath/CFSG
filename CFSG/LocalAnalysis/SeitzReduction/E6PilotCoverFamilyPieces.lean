module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyTwist
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyNeighbour

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotCoverFamilyPiecesNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Pieces


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

variable {N : E6Neighbour} {c : FieldNeighbourCover σ e N}

@[expose] noncomputable def leviToPiece {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* leviPiece K N J where
  toFun y := ⟨⟨y, levi_le_neighbourLevi hJ y.2⟩, mem_leviPiece_iff_mem_levi.2 y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def pieceToLevi (N : E6Neighbour) (J : Finset (Fin (Tag.rank .E6))) :
    leviPiece K N J →* CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J where
  toFun y := ⟨(y : N.levi K), mem_leviPiece_iff_mem_levi.1 y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem IsCoverPiece.ofSection {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes)
    {s : leviPiece K N J →* neighbourCore e N} (hs : ∀ y, c.p (s y) = y) :
    IsCoverPiece c hJ (s.comp (leviToPiece hJ)) := fun y => by
  rw [MonoidHom.comp_apply, hs]
  rfl

variable {J : Finset (Fin (Tag.rank .E6))} {hJ : J ⊆ N.nodes}
  {s : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e N}

theorem IsCoverPiece.toSection (hs : IsCoverPiece c hJ s) (y : leviPiece K N J) :
    c.p (s.comp (pieceToLevi N J) y) = y := by
  rw [MonoidHom.comp_apply, hs]
  rfl

theorem IsCoverPiece.range_eq_pieceCore (hs : IsCoverPiece c hJ s)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) (hJ2 : J.card ≤ 2) :
    ((neighbourCore e N).subtype.comp s).range = pieceCore e J := by
  rw [← (c.range_section_eq_pieceCore hq hJ hJ2 _ hs.toSection).1]
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨leviToPiece hJ y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨pieceToLevi N J y, rfl⟩

@[expose] noncomputable def leviIncl {I J : Finset (Fin (Tag.rank .E6))} (hIJ : I ⊆ J) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I →*
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
  (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I).subtype.codRestrict _
    fun y => CFSG.LieType.CurtisTits.levi_mono (adjDatumE6 K).rootGroup hIJ y.2

theorem coe_leviIncl {I J : Finset (Fin (Tag.rank .E6))} (hIJ : I ⊆ J)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I) :
    ((leviIncl hIJ y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
      adjointGroup .E6 K) = y := by
  rw [leviIncl, MonoidHom.codRestrict_apply]
  rfl

theorem IsCoverPiece.restrict (hs : IsCoverPiece c hJ s) {I : Finset (Fin (Tag.rank .E6))}
    (hIJ : I ⊆ J) : IsCoverPiece c (hIJ.trans hJ) (s.comp (leviIncl hIJ)) := fun y => by
  rw [MonoidHom.comp_apply, hs]
  exact Subtype.ext (coe_leviIncl hIJ y)

theorem IsCoverPiece.eq_of_subset (hs : IsCoverPiece c hJ s) {J' : Finset (Fin (Tag.rank .E6))}
    {hJ' : J' ⊆ N.nodes}
    {s' : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J' →* neighbourCore e N}
    (hs' : IsCoverPiece c hJ' s') (hq : 4 ≤ Nat.card (fixSubfield σ))
    {I : Finset (Fin (Tag.rank .E6))} (hIJ : I ⊆ J) (hIJ' : I ⊆ J') (hI2 : I.card ≤ 2)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup I) :
    s (leviIncl hIJ y) = s' (leviIncl hIJ' y) := by
  have h₁ := hs.restrict hIJ
  have h₂ := hs'.restrict hIJ'
  have hI : I ⊆ N.nodes := hIJ.trans hJ
  have hm₁ : ((s (leviIncl hIJ y) : neighbourCore e N) : G) ∈ pieceCore e I := by
    rw [← h₁.range_eq_pieceCore hq hI2]
    exact ⟨y, rfl⟩
  have hm₂ : ((s' (leviIncl hIJ' y) : neighbourCore e N) : G) ∈ pieceCore e I := by
    rw [← h₂.range_eq_pieceCore hq hI2]
    exact ⟨y, rfl⟩
  refine c.eq_of_mem_pieceCore hq hI hI2 _ h₁.toSection hm₁ hm₂ ?_
  rw [hs, hs']
  exact Subtype.ext ((coe_leviIncl hIJ y).trans (coe_leviIncl hIJ' y).symm)

theorem exists_isCoverPiece_high (h : FieldNeighbourCover σ e .high) (hK : 5 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ E6Neighbour.high.nodes) (hJ2 : J.card ≤ 2) :
    ∃ s, IsCoverPiece h hJ s := by
  obtain ⟨s, hs⟩ := h.exists_section_high hK hJ hJ2
  exact ⟨_, IsCoverPiece.ofSection hJ hs⟩

theorem exists_isCoverPiece_toNeighbour (h : FieldNeighbourCover σ e .high) (hK : 5 ≤ Nat.card K)
    {N : E6Neighbour} (hN : N = .six ∨ N = .three) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) : ∃ s, IsCoverPiece (h.toNeighbour N) hJ s := by
  obtain ⟨s, hs⟩ := h.exists_section_toNeighbour_of_subset hK hN hJ
  exact ⟨_, IsCoverPiece.ofSection hJ hs⟩

theorem exists_isCoverPiece_a3 (h : FieldNeighbourCover σ e .high) (hK : 5 ≤ Nat.card K) :
    ∃ s, IsCoverPiece h a3Nodes_subset_high s := by
  obtain ⟨s, hs⟩ := h.exists_section_a3 hK a3Nodes_subset_high
  refine ⟨s.comp ⟨⟨fun y => ⟨⟨y, a3Levi_le_levi_high y.2⟩, y.2⟩, rfl⟩, fun _ _ => rfl⟩,
    fun y => ?_⟩
  rw [MonoidHom.comp_apply, hs]
  rfl

end Pieces

end CFSG.SeitzReduction.E6Pilot

module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldTriangle

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG)

local instance e7PilotAlignFieldFamilyNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem nodes_inter_subset {N N' : E7Neighbour} {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes)
    (hj' : j ∈ N'.nodes) :
    (N = .high → N' = .seven → j ∈ ({1, 2, 3, 4} : Finset (Fin (Tag.rank .E7)))) ∧
      (N = .high → N' = .four → j ∈ ({5, 6} : Finset (Fin (Tag.rank .E7)))) ∧
      (N = .seven → N' = .four → j ∈ ({0} : Finset (Fin (Tag.rank .E7)))) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl rfl <;> revert j hj hj' <;> decide

section Family


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

@[expose] def IsAlignedFamily (Φ : ∀ N : E7Neighbour, FieldNeighbourIso σ e N) : Prop :=
  ∀ (N N' : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))}, J ⊆ N.nodes → J ⊆ N'.nodes →
    ∀ (x : N.levi K) (x' : N'.levi K), (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K N J →
      (((Φ N).Φ x : neighbourCore e N) : G) = (Φ N').Φ x'

@[expose] def ofTriple (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .seven)
    (hZ : FieldNeighbourIso σ e .four) : ∀ N : E7Neighbour, FieldNeighbourIso σ e N
  | .high => hX
  | .seven => hY
  | .four => hZ

theorem isAlignedFamily_ofTriple {hX : FieldNeighbourIso σ e .high}
    {hY : FieldNeighbourIso σ e .seven} {hZ : FieldNeighbourIso σ e .four}
    (h1 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {1, 2, 3, 4} →
      ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.seven.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : neighbourCore e .high) : G) = hY.Φ x')
    (h2 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {5, 6} →
      ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.four.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : neighbourCore e .high) : G) = hZ.Φ x')
    (h3 : ∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {0} →
      ∀ (x : E7Neighbour.seven.levi K) (x' : E7Neighbour.four.levi K),
        (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .seven J →
          ((hY.Φ x : neighbourCore e .seven) : G) = hZ.Φ x') :
    IsAlignedFamily (ofTriple hX hY hZ) := by
  intro N N' J hJ hJ' x x' hxx' hx
  have hx' : x' ∈ leviPiece K N' J := mem_leviPiece.2 (hxx' ▸ mem_leviPiece.1 hx)
  have hS : ∀ {A B : E7Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .seven → J ⊆ {1, 2, 3, 4}) ∧ (A = .high → B = .four → J ⊆ {5, 6}) ∧
        (A = .seven → B = .four → J ⊆ {0}) := fun hA hB =>
    ⟨fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  cases N <;> cases N'
  · exact congrArg (fun z => (((ofTriple hX hY hZ .high).Φ z : neighbourCore e .high) : G))
      (Subtype.ext hxx')
  · exact h1 ((hS hJ hJ').1 rfl rfl) x x' hxx' hx
  · exact h2 ((hS hJ hJ').2.1 rfl rfl) x x' hxx' hx
  · exact (h1 ((hS hJ' hJ).1 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => (((ofTriple hX hY hZ .seven).Φ z : neighbourCore e .seven) : G))
      (Subtype.ext hxx')
  · exact h3 ((hS hJ hJ').2.2 rfl rfl) x x' hxx' hx
  · exact (h2 ((hS hJ' hJ).2.1 rfl rfl) x' x hxx'.symm hx').symm
  · exact (h3 ((hS hJ' hJ).2.2 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => (((ofTriple hX hY hZ .four).Φ z : neighbourCore e .four) : G))
      (Subtype.ext hxx')

end Family

section CT


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E7 (fixSubfield σ))

structure IsFieldRowFamily (φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE7 K).leviAmalgam φ
  range_eq : ∀ J, (φ J).range = pieceCore e J.1
  fix : ∀ J (x : adjointGroup .E7 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE7 K).leviAmalgam J, ((y : adjointGroup .E7 K) : ModGL .E7 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E7 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

@[expose] noncomputable def alignedFamily (Φ : ∀ N : E7Neighbour, FieldNeighbourIso σ e N)
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}) :
    (adjDatumE7 K).leviAmalgam J →* G :=
  (neighbourCore e (amalgamPlacement J.1)).subtype.comp
    ((Φ (amalgamPlacement J.1)).Φ.toMonoidHom.comp
      (Subgroup.inclusion (leviAmalgam_le_placementLevi J)))

theorem alignedFamily_apply (Φ : ∀ N : E7Neighbour, FieldNeighbourIso σ e N)
    (J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2})
    (x : (adjDatumE7 K).leviAmalgam J) :
    alignedFamily Φ J x =
      (((Φ (amalgamPlacement J.1)).Φ ⟨x, leviAmalgam_le_placementLevi J x.2⟩ :
        neighbourCore e (amalgamPlacement J.1)) : G) :=
  rfl

theorem mem_leviPiece_of_mem_leviAmalgam {N : E7Neighbour}
    {J : {J : Finset (Fin (adjDatumE7 K).rank) // J.card ≤ 2}} {x : N.levi K}
    (hx : (x : adjointGroup .E7 K) ∈ (adjDatumE7 K).leviAmalgam J) : x ∈ leviPiece K N J.1 := by
  rw [mem_leviPiece]
  have h : (x : adjointGroup .E7 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J.1 :=
    hx
  rw [levi_adjDatumE7_eq, mem_subgroupOf] at h
  exact h

theorem isFieldRowFamily_alignedFamily [Finite K] [CharP K 2] [Finite G]
    {Φ : ∀ N : E7Neighbour, FieldNeighbourIso σ e N} (hΦ : IsAlignedFamily Φ)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) : IsFieldRowFamily e (alignedFamily Φ) where
  compatible := by
    intro i j hij x y hxy
    have hsub : (i.1 : Finset (Fin (Tag.rank .E7))) ⊆ j.1 := hij
    rw [alignedFamily_apply, alignedFamily_apply]
    exact hΦ _ _ (subset_nodes_amalgamPlacement i.2)
      (hsub.trans (subset_nodes_amalgamPlacement j.2)) _ _ hxy
      (mem_leviPiece_of_mem_leviAmalgam (N := amalgamPlacement i.1) x.2)
  range_eq J := by
    rw [← (Φ (amalgamPlacement J.1)).map_leviPiece hq (subset_nodes_amalgamPlacement J.2) J.2]
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, mem_leviPiece_of_mem_leviAmalgam x.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : (y : adjointGroup .E7 K) ∈ (adjDatumE7 K).leviAmalgam J := by
        change (y : adjointGroup .E7 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J.1
        rw [levi_adjDatumE7_eq, mem_subgroupOf]
        exact mem_leviPiece.1 hy
      exact ⟨⟨y, hy'⟩, rfl⟩
  fix J x hx y hxy := by
    rw [alignedFamily_apply]
    have hxN : x ∈ (amalgamPlacement J.1).levi (fixSubfield σ) :=
      levi_le_neighbourLevi (subset_nodes_amalgamPlacement J.2) hx
    have h1 : (⟨y, leviAmalgam_le_placementLevi J y.2⟩ : (amalgamPlacement J.1).levi K) =
        leviInclusion σ _ ⟨x, hxN⟩ :=
      Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
    rw [h1]
    exact (Φ (amalgamPlacement J.1)).fix ⟨x, hxN⟩

theorem exists_isAlignedFamily_of_fieldNeighbourIso [Finite K] [CharP K 2] [Finite G]
    (hX : FieldNeighbourIso σ e .high) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ Φ : ∀ N : E7Neighbour, FieldNeighbourIso σ e N, Φ .high = hX ∧ IsAlignedFamily Φ ∧
      ∀ (N : E7Neighbour) {J : Finset (Fin (Tag.rank .E7))}, J ⊆ N.nodes → J.card ≤ 2 →
        ((leviPiece K N J).map (Φ N).Φ.toMonoidHom).map (neighbourCore e N).subtype =
          pieceCore e J := by
  obtain ⟨hY, hZ, h1, h2, h3⟩ :=
    exists_aligned_fieldNeighbourIso_eq_on_leviPiece hX (hX.toNeighbour .seven)
      (hX.toNeighbour .four) hq
  exact ⟨ofTriple hX hY hZ, rfl, isAlignedFamily_ofTriple h1 h2 h3,
    fun N _ hJ hJ2 => (ofTriple hX hY hZ N).map_leviPiece hq hJ hJ2⟩

theorem exists_isFieldRowFamily_of_fieldNeighbourIso [Finite K] [CharP K 2] [Finite G]
    (hX : FieldNeighbourIso σ e .high) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G, IsFieldRowFamily e φ := by
  obtain ⟨Φ, -, hΦ, -⟩ := exists_isAlignedFamily_of_fieldNeighbourIso hX hq
  exact ⟨_, isFieldRowFamily_alignedFamily hΦ hq⟩

end CT

end CFSG.SeitzReduction.E7Pilot

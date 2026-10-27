module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalizeExists

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG)

local instance e8PilotAlignFieldFamilyNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

theorem nodes_inter_subset {N N' : E8Neighbour} {j : Fin (Tag.rank .E8)} (hj : j ∈ N.nodes)
    (hj' : j ∈ N'.nodes) :
    (N = .high → N' = .two → j ∈ ({0, 2, 4, 5, 6} : Finset (Fin (Tag.rank .E8)))) ∧
      (N = .high → N' = .six → j ∈ ({0, 1, 2, 3} : Finset (Fin (Tag.rank .E8)))) ∧
      (N = .two → N' = .six → j ∈ ({0, 2, 7} : Finset (Fin (Tag.rank .E8)))) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl rfl <;> revert j hj hj' <;> decide

section Family


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

@[expose] def IsAlignedFamily (Φ : ∀ N : E8Neighbour, FieldNeighbourIso σ e N) : Prop :=
  ∀ (N N' : E8Neighbour) {J : Finset (Fin (Tag.rank .E8))}, J ⊆ N.nodes → J ⊆ N'.nodes →
    ∀ (x : N.levi K) (x' : N'.levi K), (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K N J →
      (((Φ N).Φ x : neighbourCore e N) : G) = (Φ N').Φ x'

@[expose] def ofTriple (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .two)
    (hZ : FieldNeighbourIso σ e .six) : ∀ N : E8Neighbour, FieldNeighbourIso σ e N
  | .high => hX
  | .two => hY
  | .six => hZ

theorem isAlignedFamily_ofTriple {hX : FieldNeighbourIso σ e .high}
    {hY : FieldNeighbourIso σ e .two} {hZ : FieldNeighbourIso σ e .six}
    (h1 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 4, 5, 6} →
      ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.two.levi K),
        (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : neighbourCore e .high) : G) = hY.Φ x')
    (h2 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 1, 2, 3} →
      ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.six.levi K),
        (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
          ((hX.Φ x : neighbourCore e .high) : G) = hZ.Φ x')
    (h3 : ∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 7} →
      ∀ (x : E8Neighbour.two.levi K) (x' : E8Neighbour.six.levi K),
        (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .two J →
          ((hY.Φ x : neighbourCore e .two) : G) = hZ.Φ x') :
    IsAlignedFamily (ofTriple hX hY hZ) := by
  intro N N' J hJ hJ' x x' hxx' hx
  have hx' : x' ∈ leviPiece K N' J := mem_leviPiece.2 (hxx' ▸ mem_leviPiece.1 hx)
  have hS : ∀ {A B : E8Neighbour}, J ⊆ A.nodes → J ⊆ B.nodes →
      (A = .high → B = .two → J ⊆ {0, 2, 4, 5, 6}) ∧ (A = .high → B = .six → J ⊆ {0, 1, 2, 3}) ∧
        (A = .two → B = .six → J ⊆ {0, 2, 7}) := fun hA hB =>
    ⟨fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.1 ha hb,
      fun ha hb j hj => (nodes_inter_subset (hA hj) (hB hj)).2.2 ha hb⟩
  cases N <;> cases N'
  · exact congrArg (fun z => (((ofTriple hX hY hZ .high).Φ z : neighbourCore e .high) : G))
      (Subtype.ext hxx')
  · exact h1 ((hS hJ hJ').1 rfl rfl) x x' hxx' hx
  · exact h2 ((hS hJ hJ').2.1 rfl rfl) x x' hxx' hx
  · exact (h1 ((hS hJ' hJ).1 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => (((ofTriple hX hY hZ .two).Φ z : neighbourCore e .two) : G))
      (Subtype.ext hxx')
  · exact h3 ((hS hJ hJ').2.2 rfl rfl) x x' hxx' hx
  · exact (h2 ((hS hJ' hJ).2.1 rfl rfl) x' x hxx'.symm hx').symm
  · exact (h3 ((hS hJ' hJ).2.2 rfl rfl) x' x hxx'.symm hx').symm
  · exact congrArg (fun z => (((ofTriple hX hY hZ .six).Φ z : neighbourCore e .six) : G))
      (Subtype.ext hxx')

end Family

section CT


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}

variable (e : L ≃* adjointGroup .E8 (fixSubfield σ))

structure IsFieldRowFamily (φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (adjDatumE8 K).leviAmalgam φ
  range_eq : ∀ J, (φ J).range = pieceCore e J.1
  fix : ∀ J (x : adjointGroup .E8 (fixSubfield σ)),
    x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 (fixSubfield σ)).rootGroup J.1 →
    ∀ y : (adjDatumE8 K).leviAmalgam J, ((y : adjointGroup .E8 K) : ModGL .E8 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E8 (fixSubfield σ)) →
      φ J y = ((e.symm x : L) : G)

variable {e}

@[expose] noncomputable def alignedFamily (Φ : ∀ N : E8Neighbour, FieldNeighbourIso σ e N)
    (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2}) :
    (adjDatumE8 K).leviAmalgam J →* G :=
  (neighbourCore e (amalgamPlacement J.1)).subtype.comp
    ((Φ (amalgamPlacement J.1)).Φ.toMonoidHom.comp
      (Subgroup.inclusion (leviAmalgam_le_placementLevi J)))

theorem alignedFamily_apply (Φ : ∀ N : E8Neighbour, FieldNeighbourIso σ e N)
    (J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2})
    (x : (adjDatumE8 K).leviAmalgam J) :
    alignedFamily Φ J x =
      (((Φ (amalgamPlacement J.1)).Φ ⟨x, leviAmalgam_le_placementLevi J x.2⟩ :
        neighbourCore e (amalgamPlacement J.1)) : G) :=
  rfl

theorem mem_leviPiece_of_mem_leviAmalgam {N : E8Neighbour}
    {J : {J : Finset (Fin (adjDatumE8 K).rank) // J.card ≤ 2}} {x : N.levi K}
    (hx : (x : adjointGroup .E8 K) ∈ (adjDatumE8 K).leviAmalgam J) : x ∈ leviPiece K N J.1 := by
  rw [mem_leviPiece]
  have h : (x : adjointGroup .E8 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J.1 :=
    hx
  rw [levi_adjDatumE8_eq, mem_subgroupOf] at h
  exact h

theorem isFieldRowFamily_alignedFamily [Finite K] [CharP K 2] [Finite G]
    {Φ : ∀ N : E8Neighbour, FieldNeighbourIso σ e N} (hΦ : IsAlignedFamily Φ)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) : IsFieldRowFamily e (alignedFamily Φ) where
  compatible := by
    intro i j hij x y hxy
    have hsub : (i.1 : Finset (Fin (Tag.rank .E8))) ⊆ j.1 := hij
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
      have hy' : (y : adjointGroup .E8 K) ∈ (adjDatumE8 K).leviAmalgam J := by
        change (y : adjointGroup .E8 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J.1
        rw [levi_adjDatumE8_eq, mem_subgroupOf]
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


theorem exists_isFieldRowFamily [Finite K] [CharP K 2] [Finite G]
    (hψ : Nonempty (E8Neighbour.high.levi K ≃* neighbourCore e .high)) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hσ : orderOf σ = 2)
    (hfix : perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E8Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E8 (fixSubfield σ)).subtype))
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ φ : ∀ J, (adjDatumE8 K).leviAmalgam J →* G, IsFieldRowFamily e φ := by
  obtain ⟨hX, hY, hZ, -, -, -, h1, h2, h3⟩ :=
    exists_aligned_normalized_fieldNeighbourIso hψ htL ht2 hσ hfix hq
  exact ⟨_, isFieldRowFamily_alignedFamily (isAlignedFamily_ofTriple h1 h2 h3) hq⟩

end CT

end CFSG.SeitzReduction.E8Pilot

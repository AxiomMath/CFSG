module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilySection

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance e6PilotCoverFamilyTwistNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Piece


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

@[expose] def IsCoverPiece {N : E6Neighbour} (c : FieldNeighbourCover σ e N)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes)
    (s : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e N) : Prop :=
  ∀ y, c.p (s y) = ⟨y, levi_le_neighbourLevi hJ y.2⟩

variable {N : E6Neighbour} {c : FieldNeighbourCover σ e N} {J : Finset (Fin (Tag.rank .E6))}
  {hJ : J ⊆ N.nodes}
  {s : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* neighbourCore e N}

theorem mem_leviPiece_iff_mem_levi {y : N.levi K} :
    y ∈ leviPiece K N J ↔
      (y : adjointGroup .E6 K) ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J := by
  rw [levi_adjDatumE6_eq, mem_subgroupOf]
  exact Iff.rfl

theorem IsCoverPiece.injective (hs : IsCoverPiece c hJ s) : Function.Injective s := by
  intro y₁ y₂ h
  have h1 := hs y₁
  rw [h, hs y₂] at h1
  exact Subtype.ext (congrArg Subtype.val h1).symm

theorem IsCoverPiece.eq_of_mem_range (hs : IsCoverPiece c hJ s) {a b : neighbourCore e N}
    (ha : a ∈ s.range) (hb : b ∈ s.range) (hab : c.p a = c.p b) : a = b := by
  obtain ⟨y₁, rfl⟩ := ha
  obtain ⟨y₂, rfl⟩ := hb
  rw [hs, hs] at hab
  rw [show y₁ = y₂ from
    Subtype.ext (congrArg (fun z : N.levi K => (z : adjointGroup .E6 K)) hab)]

theorem IsCoverPiece.map_levi_singleton (hs : IsCoverPiece c hJ s)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {j : Fin (Tag.rank .E6)} (hj : j ∈ J) :
    ((CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}).subgroupOf
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)).map
      ((neighbourCore e N).subtype.comp s) = pieceCore e {j} := by
  have hjJ : ({j} : Finset (Fin (Tag.rank .E6))) ⊆ J := Finset.singleton_subset_iff.2 hj
  have hjN : ({j} : Finset (Fin (Tag.rank .E6))) ⊆ N.nodes := hjJ.trans hJ
  have hle := CFSG.LieType.CurtisTits.levi_mono (adjDatumE6 K).rootGroup hjJ
  set ι : leviPiece K N {j} →* CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
    { toFun := fun y => ⟨(y : N.levi K), hle (mem_leviPiece_iff_mem_levi.1 y.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  have hsι : ∀ y, c.p ((s.comp ι) y) = y := fun y => by
    rw [MonoidHom.comp_apply, hs]
    rfl
  have hr := c.pieceCore_subgroupOf_eq_range hq hjN (by simp) (s.comp ι) hsι
  have h1 : pieceCore e {j} = ((s.comp ι).range).map (neighbourCore e N).subtype := by
    rw [← hr, subgroupOf_map_subtype, inf_of_le_left (pieceCore_le_neighbourCore e N hjN)]
  rw [h1, ← Subgroup.map_map]
  congr 1
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨⟨y, levi_le_neighbourLevi hJ y.2⟩, mem_leviPiece_iff_mem_levi.2 hy⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨ι y, mem_leviPiece_iff_mem_levi.1 y.2, rfl⟩

theorem levi_eq_iSup_singleton (K : Type) [Field K] (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J =
      ⨆ j ∈ J, CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} := by
  simp only [CFSG.LieType.CurtisTits.levi_singleton]
  rfl

theorem IsCoverPiece.range_eq (hs : IsCoverPiece c hJ s) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ((neighbourCore e N).subtype.comp s).range = ⨆ j ∈ J, pieceCore e {j} := by
  have hle : ∀ j, j ∈ J → CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} ≤
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J :=
    fun j hj => CFSG.LieType.CurtisTits.levi_mono _ (Finset.singleton_subset_iff.2 hj)
  have htop : (⊤ : Subgroup (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)) =
      ⨆ j ∈ J, (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j}).subgroupOf
        (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) := by
    rw [← subgroupOf_iSup₂_of_le hle, ← levi_eq_iSup_singleton, subgroupOf_self]
  rw [MonoidHom.range_eq_map, htop, Subgroup.map_iSup]
  refine iSup_congr fun j => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hj => hs.map_levi_singleton hq hj

theorem symm_mem_iSup_pieceCore (hq : 4 ≤ Nat.card (fixSubfield σ))
    {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J) :
    ((e.symm x : L) : G) ∈ ⨆ j ∈ J, pieceCore e {j} := by
  set φ : adjointGroup .E6 (fixSubfield σ) →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  have hmap : (CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J).map φ ≤
      ⨆ j ∈ J, pieceCore e {j} := by
    rw [levi_eq_iSup_singleton, Subgroup.map_iSup]
    refine iSup_mono fun j => ?_
    rw [Subgroup.map_iSup]
    refine iSup_mono fun hj => ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : (z : ModGL .E6 (fixSubfield σ)) ∈
        rootSpan .E6 (fixSubfield σ) (amalgamRoots {j}) := by
      rw [levi_adjDatumE6_eq] at hz
      exact hz
    exact symm_mem_pieceCore_of_mem_rootSpan hq (by simp) hz'
  exact hmap ⟨x, hx, rfl⟩

theorem IsCoverPiece.fix (hs : IsCoverPiece c hJ s) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : x ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 (fixSubfield σ)).rootGroup J)
    (y : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    ((s y : neighbourCore e N) : G) = ((e.symm x : L) : G) := by
  have hxN : x ∈ N.levi (fixSubfield σ) := levi_le_neighbourLevi hJ hx
  obtain ⟨w, hw, hpw⟩ := c.fix ⟨x, hxN⟩
  have hwr : w ∈ s.range := by
    have h1 : (w : G) ∈ ((neighbourCore e N).subtype.comp s).range := by
      rw [hs.range_eq hq, hw]
      exact symm_mem_iSup_pieceCore hq hx
    obtain ⟨y', hy'⟩ := h1
    exact ⟨y', Subtype.ext hy'⟩
  have hp : c.p (s y) = c.p w := by
    rw [hs, hpw]
    exact Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
  rw [hs.eq_of_mem_range ⟨y, rfl⟩ hwr hp, hw]

theorem exists_twist_eq_on_a3_cover (hX : FieldNeighbourCover σ e .high)
    (hY : FieldNeighbourCover σ e .six) (hq : 4 ≤ Nat.card (fixSubfield σ))
    {sX : a3Levi K →* neighbourCore e .high} (hsX : IsCoverPiece hX a3Nodes_subset_high sX)
    {sY : a3Levi K →* neighbourCore e .six} (hsY : IsCoverPiece hY a3Nodes_subset_six sY) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ ∀ y y' : a3Levi K,
      ((y' : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (ρ : K →+* K) ((y : adjointGroup .E6 K) : ModGL .E6 K) →
      ((sX y : neighbourCore e .high) : G) = ((sY y' : neighbourCore e .six) : G) := by
  set f₁ := (neighbourCore e .high).subtype.comp sX with hf₁
  set f₂ := (neighbourCore e .six).subtype.comp sY with hf₂
  have h₁ : Function.Injective f₁ := Subtype.val_injective.comp hsX.injective
  have h₂ : Function.Injective f₂ := Subtype.val_injective.comp hsY.injective
  have hr : f₁.range = f₂.range := (hsX.range_eq hq).trans (hsY.range_eq hq).symm
  have hfix : ∀ (x : a3Levi (fixSubfield σ)) (y : a3Levi K),
      ((y : adjointGroup .E6 K) : ModGL .E6 K) = baseChangeGL (fixSubfield σ).subtype
        ((x : adjointGroup .E6 (fixSubfield σ)) : ModGL .E6 (fixSubfield σ)) → f₁ y = f₂ y := by
    intro x y hxy
    change ((sX y : neighbourCore e .high) : G) = ((sY y : neighbourCore e .six) : G)
    rw [hsX.fix hq x.2 y hxy, hsY.fix hq x.2 y hxy]
  set θ : MulAut (a3Levi K) := ((MonoidHom.ofInjective h₁).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective h₂).symm with hθdef
  have hθ : ∀ y, f₂ (θ y) = f₁ y := by
    intro y
    have h := (MonoidHom.ofInjective h₂).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective h₁ y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨ρ, hρ, hθρ⟩ := exists_ringEquiv_of_forall_a3 (fixSubfield σ).subtype θ
    fun x y hxy => h₂ ((hθ y).trans (hfix x y hxy))
  refine ⟨ρ, hρ, fun y y' hyy' => ?_⟩
  have hθy : θ y = y' := Subtype.ext (Subtype.ext ((hθρ y).trans hyy'.symm))
  change f₁ y = f₂ y'
  rw [← hθ y, hθy]

end Piece

end CFSG.SeitzReduction.E6Pilot

module

public import CFSG.LieType.Chevalley.C2E6NativeF4Panels
public import CFSG.Monster.B.Geometry.F4Census

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Pointwise

section Transport

variable {B B' : Type*} {M : CoxeterMatrix B} {M' : CoxeterMatrix B'} {W W' : Type*} [Group W]
  [Group W'] {cs : CoxeterSystem M W} {cs' : CoxeterSystem M' W'} {φ : W ≃* W'} {e : B ≃ B'}
  (hs : ∀ i, φ (cs.simple i) = cs'.simple (e i)) {C : Type*} {δ : C → C → W}

include hs

theorem simple_eq_map_simple (j : B') : cs'.simple j = φ (cs.simple (e.symm j)) := by
  rw [hs, Equiv.apply_symm_apply]

theorem isWeylDistanceBuilding_map (hδ : IsWeylDistanceBuilding cs δ) :
    IsWeylDistanceBuilding cs' fun x y => φ (δ x y) where
  nonempty := hδ.nonempty
  eq_one_iff x y := by
    rw [MulEquiv.map_eq_one_iff]
    exact hδ.eq_one_iff x y
  mul_simple x y z j h := by
    rw [simple_eq_map_simple hs] at h ⊢
    obtain ⟨h1, h2⟩ := hδ.mul_simple x y z (e.symm j) (φ.injective h)
    refine ⟨h1.imp (congrArg φ) fun h => by rw [h, map_mul], fun hl => ?_⟩
    rw [← map_mul, length_map_of_simple cs cs' φ e hs, length_map_of_simple cs cs' φ e hs] at hl
    rw [h2 hl, map_mul]
  exists_simple x y j := by
    obtain ⟨z, h1, h2⟩ := hδ.exists_simple x y (e.symm j)
    exact ⟨z, by rw [h1, simple_eq_map_simple hs], by rw [h2, map_mul, simple_eq_map_simple hs]⟩

theorem residue_map (J : Set B') (x : C) :
    residue cs' (fun x y => φ (δ x y)) J x = residue cs δ (e ⁻¹' J) x := by
  have hrel : (fun a b => ∃ j ∈ J, φ (δ a b) = cs'.simple j) =
      fun a b => ∃ i ∈ e ⁻¹' J, δ a b = cs.simple i := by
    funext a b
    refine propext ⟨fun ⟨j, hj, h⟩ => ?_, fun ⟨i, hi, h⟩ => ⟨e i, hi, by rw [h, hs]⟩⟩
    refine ⟨e.symm j, by rwa [Set.mem_preimage, Equiv.apply_symm_apply], φ.injective ?_⟩
    rw [h, simple_eq_map_simple hs]
  show {y | Relation.ReflTransGen _ x y} = {y | Relation.ReflTransGen _ x y}
  rw [hrel]

end Transport

abbrev stdChamber
    : Type := stdGroup ⧸ stdBorelG

@[expose] def stdDistance :
    stdChamber → stdChamber → relWeylTwist TwistTag.E6 :=
  cosetDistance stdBorelG stdCell

theorem stdBuilding :
    (∀ (g h : stdGroup) (w : relWeylTwist TwistTag.E6),
      stdDistance (g : stdChamber) (h : stdChamber) = w ↔ g⁻¹ * h ∈ stdCell w) ∧
    IsWeylDistanceBuilding nativeCoxeterSystem stdDistance ∧
    (∀ J : Set (Fin 4), ∃ P : Subgroup stdGroup,
      (P : Set stdGroup) = ⋃ w ∈ Subgroup.closure (nativeCoxeterSystem.simple '' J), stdCell w ∧
      ∀ g : stdGroup, residue nativeCoxeterSystem stdDistance J (g : stdChamber) =
        (fun x : stdGroup => (x : stdChamber)) '' (g • (P : Set stdGroup))) ∧
    ∀ i : Fin 4,
      ((fun x : stdGroup => (x : stdChamber)) '' stdCell (nativeCoxeterSystem.simple i)).Finite →
      ∀ y : stdChamber, (residue nativeCoxeterSystem stdDistance {i} y).ncard =
        ((fun x : stdGroup => (x : stdChamber)) '' stdCell (nativeCoxeterSystem.simple i)).ncard +
          1 := by
  obtain ⟨h1, h2, h3, -, -, h6, -⟩ := bruhat_double_cosets_give_building
    (cs := nativeCoxeterSystem) stdBorelG stdCell (fun w => ⟨stdRep w, stdCell_eq w⟩)
    existsUnique_mem_stdCell stdCell_one inv_stdCell stdCell_mul_of_length_add
    stdCell_mul_of_length_sub
  exact ⟨h1, h2, h3, h6⟩

theorem stdDistance_mk_eq_iff
    (g h : stdGroup) (w : relWeylTwist TwistTag.E6) :
    stdDistance (g : stdChamber) (h : stdChamber) = w ↔
      (g : ModGL Tag.E6 K)⁻¹ * h ∈ stdBruhatCell w :=
  stdBuilding.1 g h w

theorem isWeylDistanceBuilding_stdDistance :
    IsWeylDistanceBuilding nativeCoxeterSystem stdDistance :=
  stdBuilding.2.1

theorem coe_nativeParabolic
    (J : Set (Fin 4)) :
    (nativeParabolic J : Set (ModGL Tag.E6 K)) =
      ⋃ v : foldedParabolicWeylGroup TwistTag.E6 (foldedIndex '' J),
        graphFixedRootBruhatCell TwistTag.E6 K barHom v := by
  have h := (fixed_standard_parabolic_cells TwistTag.E6 K barEquiv).1 (foldedIndex '' J)
  rw [barEquiv_toRingHom] at h
  rw [nativeParabolic_eq]
  exact h

theorem foldedParabolicWeylGroup_le_relWeylTwist
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    foldedParabolicWeylGroup TwistTag.E6 J ≤ relWeylTwist TwistTag.E6 :=
  (Subgroup.closure_le _).2 (Set.image_subset_iff.2 fun a _ => TwistTag.E6.orbitReflection_mem a)

theorem mem_closure_nativeSimple_iff
    (J : Set (Fin 4)) (w : relWeylTwist TwistTag.E6) :
    w ∈ Subgroup.closure (nativeCoxeterSystem.simple '' J) ↔
      (w : WeylGroup TwistTag.E6.tag) ∈
        foldedParabolicWeylGroup TwistTag.E6 (foldedIndex '' J) := by
  have e : (Subgroup.closure (nativeCoxeterSystem.simple '' J)).map
      (relWeylTwist TwistTag.E6).subtype =
        foldedParabolicWeylGroup TwistTag.E6 (foldedIndex '' J) := by
    rw [MonoidHom.map_closure, foldedParabolicWeylGroup, Set.image_image, Set.image_image]
    exact congrArg Subgroup.closure
      (Set.image_congr fun i _ => by rw [nativeCoxeterSystem_simple]; rfl)
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).symm

theorem mem_nativeParabolic_iff_cells
    (J : Set (Fin 4)) (x : ModGL Tag.E6 K) :
    x ∈ nativeParabolic J ↔ ∃ v : foldedParabolicWeylGroup TwistTag.E6 (foldedIndex '' J),
      x ∈ graphFixedRootBruhatCell TwistTag.E6 K barHom v := by
  rw [← SetLike.mem_coe, coe_nativeParabolic]
  exact Set.mem_iUnion

theorem iUnion_stdCell_closure
    (J : Set (Fin 4)) :
    ⋃ w ∈ Subgroup.closure (nativeCoxeterSystem.simple '' J), stdCell w =
      ((nativeParabolic J).subgroupOf stdGroup : Set stdGroup) := by
  ext g
  simp only [Set.mem_iUnion, exists_prop, SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_stdCell]
  rw [mem_nativeParabolic_iff_cells]
  constructor
  · rintro ⟨w, hw, hg⟩
    exact ⟨⟨w, (mem_closure_nativeSimple_iff J w).1 hw⟩, hg⟩
  · rintro ⟨⟨v, hv⟩, hg⟩
    exact ⟨⟨v, foldedParabolicWeylGroup_le_relWeylTwist _ hv⟩,
      (mem_closure_nativeSimple_iff J _).2 hv, hg⟩

theorem residue_stdDistance
    (J : Set (Fin 4)) (g : stdGroup) :
    residue nativeCoxeterSystem stdDistance J (g : stdChamber) =
      (fun x : stdGroup => (x : stdChamber)) ''
        (g • ((nativeParabolic J).subgroupOf stdGroup : Set stdGroup)) := by
  obtain ⟨P, hP, hres⟩ := stdBuilding.2.2.1 J
  rw [hres g, hP, iUnion_stdCell_closure]

theorem ncard_panel_stdDistance
    (i : Fin 4) (x : stdChamber) :
    (panel nativeCoxeterSystem stdDistance i x).ncard = if (i : ℕ) < 2 then 3 else 5 := by
  have h := stdBuilding.2.2.2 i (Set.toFinite _) x
  rw [nativeCoxeterSystem_simple, ncard_image_stdCell_nativeSimple,
    card_stdInvUnipotent_nativeSimple] at h
  rw [panel, h]
  split_ifs <;> rfl

theorem encard_panel_stdDistance
    (i : Fin 4) (x : stdChamber) :
    (panel nativeCoxeterSystem stdDistance i x).encard = if (i : ℕ) < 2 then 3 else 5 := by
  rw [← (Set.toFinite _).cast_ncard_eq, ncard_panel_stdDistance]
  split_ifs <;> rfl

theorem isThick_stdDistance
    : IsThick nativeCoxeterSystem stdDistance := fun i x => by
  rw [encard_panel_stdDistance]
  split_ifs <;> decide

@[expose] def stdDistanceF4 :
    stdChamber → stdChamber → WeylGroup TwistTag.E6.foldedTag :=
  fun x y => nativeWeylEquiv (stdDistance x y)

theorem isWeylDistanceBuilding_stdDistanceF4 :
    IsWeylDistanceBuilding (coxeterSystem TwistTag.E6.foldedTag) stdDistanceF4 :=
  isWeylDistanceBuilding_map nativeWeylEquiv_simple isWeylDistanceBuilding_stdDistance

theorem residue_stdDistanceF4
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) (x : stdChamber) :
    residue (coxeterSystem TwistTag.E6.foldedTag) stdDistanceF4 J x =
      residue nativeCoxeterSystem stdDistance (nativeIdx ⁻¹' J) x :=
  residue_map nativeWeylEquiv_simple J x

theorem encard_panel_stdDistanceF4
    (a : Fin TwistTag.E6.foldedTag.rank) (x : stdChamber) :
    (panel (coxeterSystem TwistTag.E6.foldedTag) stdDistanceF4 a x).encard =
      if (a : ℕ) < 2 then 3 else 5 := by
  have e : nativeIdx ⁻¹' {a} = {nativeIdx.symm a} := by
    ext i
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, Equiv.eq_symm_apply]
  have h := residue_stdDistanceF4 {a} x
  rw [e] at h
  have h' := encard_panel_stdDistance (nativeIdx.symm a) x
  rw [panel, ← h] at h'
  exact h'

theorem card_stdChamber
    : Nat.card stdChamber = 371231385525 :=
  (F4_two_four_building_census.{0, 0} isWeylDistanceBuilding_stdDistanceF4
    encard_panel_stdDistanceF4).1

theorem ncard_residue_stdDistance
    (m : ℕ) (x : stdChamber) :
    (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ m} x).ncard =
      (residue (coxeterSystem .F4) stdDistanceF4 {a | (a : ℕ) ≠ m} x).ncard :=
  congrArg Set.ncard (residue_stdDistanceF4 {a | (a : ℕ) ≠ m} x).symm

theorem card_stdGroup
    : Nat.card stdGroup = 76532479683774853939200 := by
  rw [← stdBorelG.card_mul_index, Subgroup.index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe stdBorel_le_stdGroup).toEquiv, card_stdBorel,
    card_stdChamber]
  norm_num

theorem ncard_residue_compl_stdDistance :
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 0} x).ncard = 93555) ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 1} x).ncard = 315) ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 2} x).ncard = 105) ∧
    ∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 3} x).ncard = 16065 := by
  obtain ⟨-, h0, h1, h2, h3, -⟩ := F4_two_four_building_census.{0, 0}
    isWeylDistanceBuilding_stdDistanceF4 encard_panel_stdDistanceF4
  exact ⟨fun x => (ncard_residue_stdDistance 0 x).trans (h0 x),
    fun x => (ncard_residue_stdDistance 1 x).trans (h1 x),
    fun x => (ncard_residue_stdDistance 2 x).trans (h2 x),
    fun x => (ncard_residue_stdDistance 3 x).trans (h3 x)⟩

theorem standard_native_numbered_F4_building :
    (∀ (g h : stdGroup) (w : relWeylTwist TwistTag.E6),
      stdDistance (g : stdChamber) (h : stdChamber) = w ↔
        (g : ModGL Tag.E6 K)⁻¹ * h ∈ (stdBorel : Set (ModGL Tag.E6 K)) *
          {canonicalRep (coxeterSystem TwistTag.E6.tag) K w} * stdBorel) ∧
    (∀ i : Fin 4, (nativeCoxeterSystem.simple i : WeylGroup TwistTag.E6.tag) = nativeRefl i) ∧
    (∀ i j : Fin 4, orderOf (nativeRefl i * nativeRefl j) = CoxeterMatrix.F₄ i j) ∧
    (CoxeterMatrix.F₄ 0 1 = 3 ∧ CoxeterMatrix.F₄ 1 2 = 4 ∧ CoxeterMatrix.F₄ 2 3 = 3 ∧
      CoxeterMatrix.F₄ 0 2 = 2 ∧ CoxeterMatrix.F₄ 0 3 = 2 ∧ CoxeterMatrix.F₄ 1 3 = 2) ∧
    IsWeylDistanceBuilding nativeCoxeterSystem stdDistance ∧
    Nat.card (relWeylTwist TwistTag.E6) = 1152 ∧
    IsThick nativeCoxeterSystem stdDistance ∧
    (∀ (i : Fin 4) (x : stdChamber),
      (panel nativeCoxeterSystem stdDistance i x).ncard = if (i : ℕ) < 2 then 3 else 5) ∧
    (∀ (J : Set (Fin 4)) (g : stdGroup),
      residue nativeCoxeterSystem stdDistance J (g : stdChamber) =
        (fun x : stdGroup => (x : stdChamber)) ''
          (g • ((nativeParabolic J).subgroupOf stdGroup : Set stdGroup))) ∧
    Nat.card stdChamber = 371231385525 ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 0} x).ncard = 93555) ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 1} x).ncard = 315) ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 2} x).ncard = 105) ∧
    (∀ x : stdChamber,
      (residue nativeCoxeterSystem stdDistance {i | (i : ℕ) ≠ 3} x).ncard = 16065) ∧
    Nat.card stdGroup = 76532479683774853939200 := by
  obtain ⟨h0, h1, h2, h3⟩ := ncard_residue_compl_stdDistance
  refine ⟨fun g h w => stdDistance_mk_eq_iff g h w, fun i => ?_, orderOf_nativeRefl_mul,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, isWeylDistanceBuilding_stdDistance, card_relWeylTwist_E6,
    isThick_stdDistance, ncard_panel_stdDistance, residue_stdDistance, card_stdChamber, h0, h1,
    h2, h3, card_stdGroup⟩
  rw [nativeCoxeterSystem_simple]
  exact coe_nativeSimple_eq_nativeRefl i

end CFSG.LieType.Chevalley.C2E6Std

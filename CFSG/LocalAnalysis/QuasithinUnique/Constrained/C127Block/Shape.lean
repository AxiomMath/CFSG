module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Inputs
public import CFSG.Quasithin.Background.B69Done
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127MAut

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

namespace C127Block

open MAut

theorem shapeCtxK_of_component {V : Type} [CommGroup V] [Finite V]
    (hComp : B69.AsB69ComponentK) (hV : ∀ v : V, v ^ 2 = 1)
    {X T M : Subgroup (MulAut V)} (hK : CFSG.SectionRank.IsKGroupCat ↥X)
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X)
    (hns : ¬ Group.IsSolvable ↥X) : B69.ShapeCtx X T M :=
  fun A L hA hL hLA W hW => hComp V hV X T M A L ⟨hK, h, hO2, hFF, hns, hA, hL, hLA⟩ W hW

theorem exists_shape (hP4 : AsB15Part4) (hComp : B69.AsB69ComponentK) {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X T M : Subgroup (MulAut V)}
    (hK : CFSG.SectionRank.IsKGroupCat ↥X) (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥)
    (hFF : IsFFModule X) (hns : ¬ Group.IsSolvable ↥X) {L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) :
    ∃ A, IsFFStarMin X A ∧ ⁅L, A⁆ = L ∧ commV L ∈ IrrPlus L (⊤ : Subgroup V) ∧
      B69.CompShape T M A L (commV L) := by
  obtain ⟨A, hA, hLA⟩ := B69.exists_active hV hP4 h hO2 hFF hns L hL
  have hctx := shapeCtxK_of_component hComp hV hK h hO2 hFF hns
  have hW := B69.commV_mem_irrPlus hV hctx hA hL hLA
  exact ⟨A, hA, hLA, hW, hctx A L hA hL hLA (commV L) hW⟩

theorem commV_sup_eq {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X T M A L : Subgroup (MulAut V)} (hA : IsFFStarMin X A)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (hshape : B69.CompShape T M A L W) :
    commV (L ⊔ A) = commV L := by
  obtain ⟨hcL, -, -, hAc, hLc⟩ := B69.commV_eq_of_shape hV hA hL hLA hW hshape
  have hsup : L ⊔ A ≤ centQuot W := sup_le hLc hAc
  apply le_antisymm
  · rw [hcL]
    unfold commV
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, v, rfl⟩
    exact mem_centQuot.1 (hsup hx) v
  · exact commV_le_of_le le_sup_left

private theorem isSolvable_map_subgroup_aux {G G' : Type*} [Group G] [Group G']
    (H : Subgroup G) [Group.IsSolvable ↥H] (f : G →* G') :
    Group.IsSolvable ↥(H.map f) := by
  have hr : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Group.isSolvable_of_surjective (f.comp H.subtype).rangeRestrict_surjective

theorem two_le_of_altShapeK {V : Type} [CommGroup V] {M A L : Subgroup (MulAut V)}
    {W : Subgroup V} {k : ℕ} (hk : 1 ≤ k) (hq : CFSG.Open.IsQuasisimple ↥L)
    (h : B69.AltShapeK k M A L W) : 2 ≤ k := by
  by_contra hlt
  have hk1 : k = 1 := by omega
  subst hk1
  obtain ⟨π, -, -, hLeq, -, -⟩ := h
  have hsolv : Group.IsSolvable ↥L := by
    have h3 : Group.IsSolvable ↥(alternatingGroup (Fin (2 * 1 + 1))) :=
      alternatingGroup.isSolvable (by simp)
    have hmap := isSolvable_map_subgroup_aux (alternatingGroup (Fin (2 * 1 + 1)))
      ((L ⊔ A).subtype.comp π)
    rw [← hLeq] at hmap
    exact hmap
  have hnt : Nontrivial ↥L := by
    haveI := hq.2
    obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := ↥L ⧸ Subgroup.center ↥L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨a, b, fun h => hxy (by rw [h])⟩
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

end C127Block

end L246C127

end CFSG.QuasithinUnique

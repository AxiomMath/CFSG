module

public import CFSG.LocalAnalysis.ComponentClassification.BadComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBCentralQuotient

@[expose] def imageRestriction {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (L : Subgroup X) : L →* L.map f :=
  (f.domRestrict L).codRestrict (L.map f)
    (fun x => Subgroup.mem_map_of_mem f x.property)

theorem imageRestriction_apply {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (L : Subgroup X) (x : L) :
    (imageRestriction f L x).val = f x.val := rfl

theorem imageRestriction_surjective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (L : Subgroup X) : Function.Surjective (imageRestriction f L) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem imageRestriction_kernel_central {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X) (L : Subgroup X) :
    (imageRestriction f L).ker ≤ Subgroup.center L := by
  intro x hx
  have hfx : f x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  apply Subgroup.mem_center_iff.mpr
  intro z
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral hfx)) z.val)

@[expose] def preimageRestriction {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (M : Subgroup Y) : M.comap f →* M :=
  (f.domRestrict (M.comap f)).codRestrict M (fun x => x.property)

theorem preimageRestriction_apply {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (M : Subgroup Y) (x : M.comap f) :
    (preimageRestriction f M x).val = f x.val := rfl

theorem preimageRestriction_surjective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hsurjective : Function.Surjective f) (M : Subgroup Y) :
    Function.Surjective (preimageRestriction f M) := by
  intro y
  obtain ⟨x, hxy⟩ := hsurjective y.val
  have hx : x ∈ M.comap f := by
    change f x ∈ M
    rw [hxy]
    exact y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem preimageRestriction_kernel_central {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X) (M : Subgroup Y) :
    (preimageRestriction f M).ker ≤ Subgroup.center (M.comap f) := by
  intro x hx
  have hfx : f x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  apply Subgroup.mem_center_iff.mpr
  intro z
  exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral hfx)) z.val)

@[expose] def derivedPreimage {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (M : Subgroup Y) : Subgroup X :=
  (commutator (M.comap f)).map (M.comap f).subtype

theorem derivedPreimage_eq_commutator {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (M : Subgroup Y) :
    derivedPreimage f M = ⁅M.comap f, M.comap f⁆ :=
  Subgroup.map_subtype_commutator (M.comap f)

theorem derivedPreimage_map {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hsurjective : Function.Surjective f)
    (M : Subgroup Y) [Group.IsPerfect M] : (derivedPreimage f M).map f = M := by
  rw [derivedPreimage_eq_commutator, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective hsurjective, Subgroup.commutator_eq_self]

theorem derivedPreimage_subnormal {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (M : Subgroup Y) (hM : M.IsSubnormal) :
    (derivedPreimage f M).IsSubnormal := by
  have hderived : (commutator (M.comap f)).IsSubnormal :=
    (inferInstance : (commutator (M.comap f)).Normal).isSubnormal
  exact hderived.trans' (hM.comap f)

theorem derivedPreimage_perfect {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hsurjective : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (M : Subgroup Y) [Group.IsPerfect M] :
    Group.IsPerfect (derivedPreimage f M) := by
  let : Group.IsPerfect (commutator (M.comap f)) := CentralExtensions.derived_perfect
    (preimageRestriction f M) (preimageRestriction_surjective f hsurjective M)
    (preimageRestriction_kernel_central f hcentral M)
  exact Group.IsPerfect.ofSurjective
    (f := (commutator (M.comap f)).equivMapOfInjective (M.comap f).subtype
      (M.comap f).subtype_injective |>.toMonoidHom)
    ((commutator (M.comap f)).equivMapOfInjective (M.comap f).subtype
      (M.comap f).subtype_injective).surjective

theorem fullPreimage_image {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (L : Subgroup X) : (L.map f).comap f = L ⊔ f.ker :=
  Subgroup.comap_map_eq f L

theorem derivedPreimage_image_eq {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (L : Subgroup X) [Group.IsPerfect L] : derivedPreimage f (L.map f) = L := by
  rw [derivedPreimage_eq_commutator, fullPreimage_image,
    CentralExtensions.commutator_sup_central L f.ker hcentral,
    Subgroup.commutator_eq_self]

theorem perfect_le_of_map_le {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (L J : Subgroup X) [Group.IsPerfect L] (himage : L.map f ≤ J.map f) : L ≤ J :=
  BadComponents.perfect_containment_of_central_kernel f hcentral L J himage

theorem quasisimple_map_iff_of_perfect {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (L : Subgroup X) [Group.IsPerfect L] :
    CFSG.IsQuasisimple L ↔ CFSG.IsQuasisimple (L.map f) := by
  rw [CatalogueBAlternating.quasisimple_iff_native,
    CatalogueBAlternating.quasisimple_iff_native]
  exact ⟨fun hL => CentralTwoKernel.quasisimple_of_surjective hL
      (imageRestriction f L) (imageRestriction_surjective f L)
      (imageRestriction_kernel_central f hcentral L),
    fun hL => CentralExtensions.quasisimple_of_surjective hL
      (imageRestriction f L) (imageRestriction_surjective f L)
      (imageRestriction_kernel_central f hcentral L)⟩

theorem pComponent_quasisimple_iff {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hcentral : f.ker ≤ Subgroup.center X)
    (p : ℕ) (L : Subgroup X) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L ↔ CFSG.IsQuasisimple (L.map f) := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  exact quasisimple_map_iff_of_perfect f hcentral L

end CFSG.ComponentClassification.CatalogueBCentralQuotient

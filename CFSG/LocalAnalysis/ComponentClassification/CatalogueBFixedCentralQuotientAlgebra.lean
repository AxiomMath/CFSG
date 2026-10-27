module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public noncomputable section

open scoped commutatorElement

namespace CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

variable {X : Type*} [Group X] (Z : Subgroup X) [Z.Normal]
  (ψ : MulAut X) (hinvariant : Z.map ψ.toMonoidHom = Z)

@[expose] def onQuotient : MulAut (X ⧸ Z) :=
  QuotientGroup.congr Z Z ψ hinvariant

theorem onQuotient_mk (x : X) :
    onQuotient Z ψ hinvariant ((QuotientGroup.mk' Z) x) =
      (QuotientGroup.mk' Z) (ψ x) :=
  QuotientGroup.congr_mk' Z Z ψ hinvariant x

@[expose] def fixedPreimage : Subgroup X :=
  (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)).comap
    (QuotientGroup.mk' Z)

theorem mem_fixedPreimage_iff (x : X) :
    x ∈ fixedPreimage Z ψ hinvariant ↔ x⁻¹ * ψ x ∈ Z := by
  change onQuotient Z ψ hinvariant ((QuotientGroup.mk' Z) x) =
      (QuotientGroup.mk' Z) x ↔ x⁻¹ * ψ x ∈ Z
  rw [onQuotient_mk]
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' Z) (x⁻¹ * ψ x) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  · intro h
    have heq := (QuotientGroup.eq_one_iff _).mpr h
    change (QuotientGroup.mk' Z) (x⁻¹ * ψ x) = 1 at heq
    rw [map_mul, map_inv] at heq
    exact (inv_mul_eq_one.mp heq).symm

theorem fixed_le_fixedPreimage :
    FixedCommutingProduct.fixedSubgroup ψ ≤ fixedPreimage Z ψ hinvariant := by
  intro x hx
  apply (mem_fixedPreimage_iff Z ψ hinvariant x).mpr
  change ψ x = x at hx
  rw [hx, inv_mul_cancel]
  exact Z.one_mem

theorem central_le_fixedPreimage : Z ≤ fixedPreimage Z ψ hinvariant := by
  intro x hx
  change onQuotient Z ψ hinvariant ((QuotientGroup.mk' Z) x) =
    (QuotientGroup.mk' Z) x
  have hzero : (QuotientGroup.mk' Z) x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
  rw [hzero, map_one]

@[expose] def displacement (hcentral : Z ≤ Subgroup.center X) :
    fixedPreimage Z ψ hinvariant →* Z where
  toFun x := ⟨x.val⁻¹ * ψ x.val,
    (mem_fixedPreimage_iff Z ψ hinvariant x.val).mp x.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    have hz := hcentral ((mem_fixedPreimage_iff Z ψ hinvariant x.val).mp x.property)
    have hcomm := Subgroup.mem_center_iff.mp hz y.val⁻¹
    change (x.val * y.val)⁻¹ * ψ (x.val * y.val) =
      (x.val⁻¹ * ψ x.val) * (y.val⁻¹ * ψ y.val)
    rw [map_mul]
    calc
      (x.val * y.val)⁻¹ * (ψ x.val * ψ y.val) =
          y.val⁻¹ * (x.val⁻¹ * ψ x.val) * ψ y.val := by group
      _ = (x.val⁻¹ * ψ x.val) * y.val⁻¹ * ψ y.val := by rw [hcomm]
      _ = (x.val⁻¹ * ψ x.val) * (y.val⁻¹ * ψ y.val) := mul_assoc _ _ _

theorem displacement_eq_one_iff (hcentral : Z ≤ Subgroup.center X)
    (x : fixedPreimage Z ψ hinvariant) :
    displacement Z ψ hinvariant hcentral x = 1 ↔ ψ x.val = x.val := by
  constructor
  · intro h
    have heq : x.val⁻¹ * ψ x.val = 1 := congrArg Subtype.val h
    exact (inv_mul_eq_one.mp heq).symm
  · intro h
    apply Subtype.ext
    change x.val⁻¹ * ψ x.val = 1
    rw [h, inv_mul_cancel]

theorem displacement_kernel (hcentral : Z ≤ Subgroup.center X) :
    (displacement Z ψ hinvariant hcentral).ker =
      (FixedCommutingProduct.fixedSubgroup ψ).subgroupOf
        (fixedPreimage Z ψ hinvariant) := by
  ext x
  exact displacement_eq_one_iff Z ψ hinvariant hcentral x

@[expose] def fixedProjection :
    FixedCommutingProduct.fixedSubgroup ψ →*
      FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant) where
  toFun x := ⟨(QuotientGroup.mk' Z) x.val,
    fixed_le_fixedPreimage Z ψ hinvariant x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

@[expose] def fixedImage :
    Subgroup (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) :=
  (fixedProjection Z ψ hinvariant).range

@[expose] def preimageProjection :
    fixedPreimage Z ψ hinvariant →*
      FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant) where
  toFun x := ⟨(QuotientGroup.mk' Z) x.val, x.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' _ _ := by apply Subtype.ext; exact map_mul _ _ _

theorem preimageProjection_surjective :
    Function.Surjective (preimageProjection Z ψ hinvariant) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z y.val
  have hmem : x ∈ fixedPreimage Z ψ hinvariant := by
    change (QuotientGroup.mk' Z) x ∈
      FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)
    rw [hx]
    exact y.property
  exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩

theorem fixedImage_eq_kernel_map (hcentral : Z ≤ Subgroup.center X) :
    fixedImage Z ψ hinvariant =
      (displacement Z ψ hinvariant hcentral).ker.map
        (preimageProjection Z ψ hinvariant) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.val, fixed_le_fixedPreimage Z ψ hinvariant x.property⟩, ?_, rfl⟩
    exact (displacement_eq_one_iff Z ψ hinvariant hcentral _).mpr x.property
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, (displacement_eq_one_iff Z ψ hinvariant hcentral x).mp hx⟩, rfl⟩

theorem fixedImage_normal (hcentral : Z ≤ Subgroup.center X) :
    (fixedImage Z ψ hinvariant).Normal := by
  rw [fixedImage_eq_kernel_map Z ψ hinvariant hcentral]
  exact Subgroup.Normal.map inferInstance (preimageProjection Z ψ hinvariant)
    (preimageProjection_surjective Z ψ hinvariant)

theorem preimage_commutator_le_kernel (hcentral : Z ≤ Subgroup.center X) :
    commutator (fixedPreimage Z ψ hinvariant) ≤
      (displacement Z ψ hinvariant hcentral).ker := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  change displacement Z ψ hinvariant hcentral ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (hcentral (displacement Z ψ hinvariant hcentral x).property)
      (displacement Z ψ hinvariant hcentral y).val).symm

theorem fixed_commutator_le_image (hcentral : Z ≤ Subgroup.center X) :
    commutator (FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) ≤
      fixedImage Z ψ hinvariant := by
  rw [fixedImage_eq_kernel_map Z ψ hinvariant hcentral]
  have hmap := Subgroup.map_mono (f := preimageProjection Z ψ hinvariant)
    (preimage_commutator_le_kernel Z ψ hinvariant hcentral)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
    (preimageProjection_surjective Z ψ hinvariant)] at hmap
  exact hmap

theorem fixed_quotient_abelian (hcentral : Z ≤ Subgroup.center X) :
    letI := fixedImage_normal Z ψ hinvariant hcentral
    IsMulCommutative
      ((FixedCommutingProduct.fixedSubgroup (onQuotient Z ψ hinvariant)) ⧸
        fixedImage Z ψ hinvariant) := by
  let := fixedImage_normal Z ψ hinvariant hcentral
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (fixed_commutator_le_image Z ψ hinvariant hcentral)

theorem fixedProjection_kernel :
    (fixedProjection Z ψ hinvariant).ker =
      Z.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) := by
  ext x
  change fixedProjection Z ψ hinvariant x = 1 ↔ x.val ∈ Z
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

theorem fixedProjection_kernel_central (hcentral : Z ≤ Subgroup.center X) :
    (fixedProjection Z ψ hinvariant).ker ≤
      Subgroup.center (FixedCommutingProduct.fixedSubgroup ψ) := by
  rw [fixedProjection_kernel]
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hcentral hx) y.val

@[expose] def fixedImageProjection :
    FixedCommutingProduct.fixedSubgroup ψ →* fixedImage Z ψ hinvariant :=
  (fixedProjection Z ψ hinvariant).rangeRestrict

theorem fixedImageProjection_surjective :
    Function.Surjective (fixedImageProjection Z ψ hinvariant) :=
  MonoidHom.rangeRestrict_surjective _

theorem fixedImageProjection_kernel :
    (fixedImageProjection Z ψ hinvariant).ker =
      Z.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) := by
  ext x
  change fixedImageProjection Z ψ hinvariant x = 1 ↔ x.val ∈ Z
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun y : fixedImage Z ψ hinvariant => y.val.val) h)
  · intro h
    apply Subtype.ext
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

theorem fixedImageProjection_kernel_central (hcentral : Z ≤ Subgroup.center X) :
    (fixedImageProjection Z ψ hinvariant).ker ≤
      Subgroup.center (FixedCommutingProduct.fixedSubgroup ψ) := by
  simpa only [fixedImageProjection_kernel, fixedProjection_kernel] using
    fixedProjection_kernel_central Z ψ hinvariant hcentral

theorem commutator_fixedPreimage_le_fixedSubgroup
    (hcentral : Z ≤ Subgroup.center X) :
    ⁅fixedPreimage Z ψ hinvariant, fixedPreimage Z ψ hinvariant⁆ ≤
      FixedCommutingProduct.fixedSubgroup ψ := by
  let H := fixedPreimage Z ψ hinvariant
  have hmap : (commutator H).map H.subtype ≤
      (displacement Z ψ hinvariant hcentral).ker.map H.subtype :=
    Subgroup.map_mono (preimage_commutator_le_kernel Z ψ hinvariant hcentral)
  rw [Subgroup.map_subtype_commutator, displacement_kernel,
    Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (fixed_le_fixedPreimage Z ψ hinvariant)] at hmap
  exact hmap

end CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

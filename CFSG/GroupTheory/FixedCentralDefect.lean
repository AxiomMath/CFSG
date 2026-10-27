module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.CoprimeAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra

public noncomputable section

namespace CFSG.FixedCentralDefect

open CFSG.ClassicalInvolution.GlaubermanAut
open scoped IsMulCommutative

section Abstract

variable {A : Type*} [CommGroup A] (φ : MulAut A)

abbrev defectNormKer : Subgroup A := (normHom φ 3).ker

abbrev defectCommutator : Subgroup A := commutatorSubgroup φ

abbrev defectGroup : Type _ :=
  (defectNormKer φ) ⧸ (defectCommutator φ).subgroupOf (defectNormKer φ)

theorem pow_three_mem_defectCommutator {c : A} (hc : c ∈ defectNormKer φ) :
    c ^ 3 ∈ defectCommutator φ := by
  have hc' : (normHom φ 3) c = 1 := hc
  have h := pow_mul_inv_normHom_mem_commutatorSubgroup (φ := φ) 3 c
  simpa [defectCommutator, hc'] using h

theorem defectGroup_pow_three (d : defectGroup φ) : d ^ 3 = 1 := by
  induction d using QuotientGroup.induction_on with
  | H c =>
      change (QuotientGroup.mk c : defectGroup φ) ^ 3 = 1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_subgroupOf).mpr (pow_three_mem_defectCommutator φ c.property)

end Abstract

section Extension

variable {X G : Type*} [Group X] [Group G]
variable (f : X →* G) (α : MulAut X) (β : MulAut G)

theorem comp_apply (hcomp : f.comp α.toMonoidHom = β.toMonoidHom.comp f) (x : X) :
    f (α x) = β (f x) :=
  DFunLike.congr_fun hcomp x

theorem map_alpha_ker (hcomp : f.comp α.toMonoidHom = β.toMonoidHom.comp f)
    (hα : α ^ 3 = 1) :
    (f.ker).map α.toMonoidHom = f.ker := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change f x = 1 at hx
    change f (α x) = 1
    rw [comp_apply f α β hcomp x, hx, map_one]
  · intro x hx
    refine ⟨α (α x), ?_, ?_⟩
    · change f (α (α x)) = 1
      rw [comp_apply f α β hcomp (α x), comp_apply f α β hcomp x, hx, map_one, map_one]
    · change α (α (α x)) = x
      have h := congrFun (congrArg (fun e : MulAut X => (e : X → X)) hα) x
      simpa [pow_succ, MulAut.mul_apply] using h

end Extension

section Central

variable {X G : Type*} [Group X] [Group G]
variable (f : X →* G) (hf : Function.Surjective f)
variable (α : MulAut X) (β : MulAut G)
variable (hα : α ^ 3 = 1)
variable (hcomp : f.comp α.toMonoidHom = β.toMonoidHom.comp f)

theorem ker_isMulCommutative (hcentral : f.ker ≤ Subgroup.center X) :
    IsMulCommutative f.ker := by
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  exact hcentral.trans (Subgroup.center_le_centralizer (f.ker : Set X))

noncomputable abbrev kerCommGroup (hcentral : f.ker ≤ Subgroup.center X) :
    CommGroup f.ker :=
  letI : IsMulCommutative f.ker := ker_isMulCommutative f hcentral
  { toGroup := inferInstance
    mul_comm := fun a b => (IsMulCommutative.is_comm (M := f.ker)).comm a b }

variable (hcentral : f.ker ≤ Subgroup.center X)

@[expose] noncomputable def fFixed :
    TauCeti.fixedSubgroup α.toMonoidHom →* TauCeti.fixedSubgroup β.toMonoidHom :=
  ((f.comp (TauCeti.fixedSubgroup α.toMonoidHom).subtype).codRestrict
    (TauCeti.fixedSubgroup β.toMonoidHom) fun x =>
      TauCeti.map_fixedSubgroup_le f hcomp ⟨x, x.property, rfl⟩)

@[simp]
theorem fFixed_apply_coe (x : TauCeti.fixedSubgroup α.toMonoidHom) :
    ((fFixed f α β hcomp x : TauCeti.fixedSubgroup β.toMonoidHom) : G) = f x := rfl

@[expose] noncomputable def lift (x : TauCeti.fixedSubgroup β.toMonoidHom) : X :=
  Classical.choose (hf (x : G))

theorem lift_spec (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    f (lift f hf β x) = (x : G) :=
  Classical.choose_spec (hf (x : G))

@[expose] noncomputable def defectElem (x : TauCeti.fixedSubgroup β.toMonoidHom) : f.ker :=
  ⟨(lift f hf β x)⁻¹ * α (lift f hf β x), by
    change f ((lift f hf β x)⁻¹ * α (lift f hf β x)) = 1
    rw [map_mul, map_inv, comp_apply f α β hcomp, lift_spec f hf β x]
    have hxβ : β (x : G) = (x : G) := TauCeti.mem_fixedSubgroup.mp x.property
    rw [hxβ, inv_mul_cancel]⟩

theorem defectElem_coe (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    ((defectElem f hf α β hcomp x : f.ker) : X) =
      (lift f hf β x)⁻¹ * α (lift f hf β x) := rfl

theorem normHom_three_apply {A : Type*} [CommGroup A] (φ : MulAut A) (a : A) :
    normHom φ 3 a = a * φ a * φ (φ a) := by
  rw [CFSG.ClassicalInvolution.GlaubermanAut.normHom_apply]
  simp [Finset.prod_range_succ, pow_succ, mul_assoc]

theorem alpha_three_apply (hα : α ^ 3 = 1) (x : X) : α (α (α x)) = x := by
  have h := congrFun (congrArg (fun e : MulAut X => (e : X → X)) hα) x
  simpa [pow_succ, MulAut.mul_apply] using h

@[expose] def alphaKer : MulAut f.ker :=
  (α.subgroupMap f.ker).trans
    (MulEquiv.subgroupCongr (map_alpha_ker f α β hcomp hα))

@[simp]
theorem alphaKer_apply_coe (c : f.ker) :
    ((alphaKer f α β hα hcomp c : f.ker) : X) = α c := by
  rfl

abbrev kerNormKer : Subgroup f.ker :=
  @defectNormKer (f.ker) (kerCommGroup f hcentral)
    (alphaKer f α β hα hcomp)

abbrev kerCommutator : Subgroup f.ker :=
  @defectCommutator (f.ker) (kerCommGroup f hcentral)
    (alphaKer f α β hα hcomp)

abbrev kerDefectGroup : Type _ :=
  @defectGroup (f.ker) (kerCommGroup f hcentral)
    (alphaKer f α β hα hcomp)

theorem defectElem_mem_norm (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    defectElem f hf α β hcomp x ∈ kerNormKer f α β hα hcomp hcentral := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  change normHom (alphaKer f α β hα hcomp) 3
      (defectElem f hf α β hcomp x) = 1
  apply Subtype.ext
  rw [normHom_three_apply]
  simp only [Subgroup.coe_mul, alphaKer_apply_coe,
    defectElem_coe, map_mul, map_inv]
  rw [alpha_three_apply α hα (lift f hf β x)]
  group
  simp

theorem lift_mem_fixedPreimage (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    lift f hf β x ∈ CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) := by
  rw [CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.mem_fixedPreimage_iff]
  exact (defectElem f hf α β hcomp x).property

@[expose] noncomputable def preimageElem (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) :=
  ⟨lift f hf β x, lift_mem_fixedPreimage f hf α β hα hcomp x⟩

@[expose] noncomputable def disp (x : TauCeti.fixedSubgroup β.toMonoidHom) : f.ker :=
  CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
    f.ker α (map_alpha_ker f α β hcomp hα) hcentral (preimageElem f hf α β hα hcomp x)

theorem disp_eq_defectElem (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    disp f hf α β hα hcomp hcentral x = defectElem f hf α β hcomp x := rfl

theorem displacement_z_mem_commutator (zX : X) (hzX : zX ∈ f.ker) :
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
        f.ker α (map_alpha_ker f α β hcomp hα) hcentral
        ⟨zX, CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.central_le_fixedPreimage
          f.ker α (map_alpha_ker f α β hcomp hα) hzX⟩ ∈
      kerCommutator f α β hα hcomp hcentral := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  have hdispz : CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
        f.ker α (map_alpha_ker f α β hcomp hα) hcentral
        ⟨zX, CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.central_le_fixedPreimage
          f.ker α (map_alpha_ker f α β hcomp hα) hzX⟩ =
      (⟨zX, hzX⟩ : f.ker)⁻¹ * alphaKer f α β hα hcomp ⟨zX, hzX⟩ := rfl
  rw [hdispz]
  have hz : (⟨zX, hzX⟩ : f.ker)⁻¹ * alphaKer f α β hα hcomp ⟨zX, hzX⟩ =
      (commutatorHom (alphaKer f α β hα hcomp) ⟨zX, hzX⟩)⁻¹ := by
    change (⟨zX, hzX⟩ : f.ker)⁻¹ * alphaKer f α β hα hcomp ⟨zX, hzX⟩ =
      ((⟨zX, hzX⟩ : f.ker) * (alphaKer f α β hα hcomp ⟨zX, hzX⟩)⁻¹)⁻¹
    rw [mul_inv_rev, inv_inv]
    exact mul_comm ((⟨zX, hzX⟩ : f.ker)⁻¹)
      (alphaKer f α β hα hcomp ⟨zX, hzX⟩)
  rw [hz]
  exact Subgroup.inv_mem _
    ((mem_commutatorSubgroup (alphaKer f α β hα hcomp)).2
      ⟨⟨zX, hzX⟩, rfl⟩)

theorem disp_mul_mem_commutator (x y : TauCeti.fixedSubgroup β.toMonoidHom) :
    disp f hf α β hα hcomp hcentral (x * y) *
        (disp f hf α β hα hcomp hcentral x *
          disp f hf α β hα hcomp hcentral y)⁻¹ ∈
      kerCommutator f α β hα hcomp hcentral := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  let zX : X := (lift f hf β x * lift f hf β y)⁻¹ * lift f hf β (x * y)
  have hzX : zX ∈ f.ker := by
    change f ((lift f hf β x * lift f hf β y)⁻¹ * lift f hf β (x * y)) = 1
    rw [map_mul, map_inv, map_mul, lift_spec, lift_spec, lift_spec]
    simp only [Subgroup.coe_mul]
    group
  let zPre : CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) :=
    ⟨zX, CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.central_le_fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) hzX⟩
  have hpre : preimageElem f hf α β hα hcomp (x * y) =
      (preimageElem f hf α β hα hcomp x *
        preimageElem f hf α β hα hcomp y) * zPre := by
    apply Subtype.ext
    change lift f hf β (x * y) =
      lift f hf β x * lift f hf β y *
        ((lift f hf β x * lift f hf β y)⁻¹ * lift f hf β (x * y))
    group
  have hdisp : disp f hf α β hα hcomp hcentral (x * y) =
      disp f hf α β hα hcomp hcentral x *
        disp f hf α β hα hcomp hcentral y *
          CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
            f.ker α (map_alpha_ker f α β hcomp hα) hcentral zPre := by
    simp only [disp, hpre, map_mul]
  have hratio : disp f hf α β hα hcomp hcentral (x * y) *
        (disp f hf α β hα hcomp hcentral x *
          disp f hf α β hα hcomp hcentral y)⁻¹ =
      CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
        f.ker α (map_alpha_ker f α β hcomp hα) hcentral zPre := by
    rw [hdisp]
    rw [mul_comm (disp f hf α β hα hcomp hcentral x *
      disp f hf α β hα hcomp hcentral y)
      (CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
        f.ker α (map_alpha_ker f α β hcomp hα) hcentral zPre)]
    group
  rw [hratio]
  exact displacement_z_mem_commutator f α β hα hcomp hcentral zX hzX

theorem disp_mem_norm (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    disp f hf α β hα hcomp hcentral x ∈ kerNormKer f α β hα hcomp hcentral := by
  rw [disp_eq_defectElem]
  exact defectElem_mem_norm f hf α β hα hcomp hcentral x

@[expose] noncomputable def defectNormElem (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    kerNormKer f α β hα hcomp hcentral :=
  ⟨disp f hf α β hα hcomp hcentral x,
    disp_mem_norm f hf α β hα hcomp hcentral x⟩

@[expose] noncomputable def defectHom :
    TauCeti.fixedSubgroup β.toMonoidHom →* kerDefectGroup f α β hα hcomp hcentral :=
  MonoidHom.mk' (fun x => QuotientGroup.mk (defectNormElem f hf α β hα hcomp hcentral x))
    (by
      let : CommGroup f.ker := kerCommGroup f hcentral
      intro x y
      change (QuotientGroup.mk (defectNormElem f hf α β hα hcomp hcentral (x * y)) :
          (kerNormKer f α β hα hcomp hcentral) ⧸
            (kerCommutator f α β hα hcomp hcentral).subgroupOf
              (kerNormKer f α β hα hcomp hcentral)) =
        QuotientGroup.mk (defectNormElem f hf α β hα hcomp hcentral x) *
          QuotientGroup.mk (defectNormElem f hf α β hα hcomp hcentral y)
      rw [← QuotientGroup.mk_mul]
      rw [QuotientGroup.eq_iff_div_mem]
      apply Subgroup.mem_subgroupOf.mpr
      simpa [defectNormElem, div_eq_mul_inv] using
        disp_mul_mem_commutator f hf α β hα hcomp hcentral x y)

@[simp]
theorem defectHom_apply (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    defectHom f hf α β hα hcomp hcentral x =
      QuotientGroup.mk (defectNormElem f hf α β hα hcomp hcentral x) := by
  rw [defectHom, MonoidHom.mk'_apply]

theorem disp_fixed_mem_commutator (w : TauCeti.fixedSubgroup α.toMonoidHom) :
    disp f hf α β hα hcomp hcentral (fFixed f α β hcomp w) ∈
      kerCommutator f α β hα hcomp hcentral := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  have hwPre : (w : X) ∈ CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) := by
    rw [CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.mem_fixedPreimage_iff]
    have hw : α (w : X) = (w : X) := by
      simpa using TauCeti.mem_fixedSubgroup.mp w.property
    change (w : X)⁻¹ * α (w : X) ∈ f.ker
    rw [hw, inv_mul_cancel]
    exact f.ker.one_mem
  let wPre : CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) := ⟨w, hwPre⟩
  let zX : X := (w : X)⁻¹ * lift f hf β (fFixed f α β hcomp w)
  have hzX : zX ∈ f.ker := by
    change f ((w : X)⁻¹ * lift f hf β (fFixed f α β hcomp w)) = 1
    rw [map_mul, map_inv, lift_spec, fFixed_apply_coe]
    exact inv_mul_cancel (f (w : X))
  let zPre : CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) :=
    ⟨zX, CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.central_le_fixedPreimage
      f.ker α (map_alpha_ker f α β hcomp hα) hzX⟩
  have hpre : preimageElem f hf α β hα hcomp (fFixed f α β hcomp w) =
      wPre * zPre := by
    apply Subtype.ext
    change lift f hf β (fFixed f α β hcomp w) =
      (w : X) * ((w : X)⁻¹ * lift f hf β (fFixed f α β hcomp w))
    group
  have hdisp : disp f hf α β hα hcomp hcentral (fFixed f α β hcomp w) =
      CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
          f.ker α (map_alpha_ker f α β hcomp hα) hcentral wPre *
        CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
          f.ker α (map_alpha_ker f α β hcomp hα) hcentral zPre := by
    simp only [disp, hpre, map_mul]
  have hw1 : CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.displacement
        f.ker α (map_alpha_ker f α β hcomp hα) hcentral wPre = 1 := by
    apply Subtype.ext
    change (w : X)⁻¹ * α.toMonoidHom (w : X) = (1 : X)
    rw [TauCeti.mem_fixedSubgroup.mp w.property, inv_mul_cancel]
  rw [hdisp, hw1, one_mul]
  exact displacement_z_mem_commutator f α β hα hcomp hcentral zX hzX

theorem defectHom_fixed (w : TauCeti.fixedSubgroup α.toMonoidHom) :
    defectHom f hf α β hα hcomp hcentral (fFixed f α β hcomp w) = 1 := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  rw [defectHom_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr
    (disp_fixed_mem_commutator f hf α β hα hcomp hcentral w)

theorem fFixed_range_le_defectHom_ker :
    (fFixed f α β hcomp).range ≤ (defectHom f hf α β hα hcomp hcentral).ker := by
  rintro x ⟨w, rfl⟩
  exact defectHom_fixed f hf α β hα hcomp hcentral w

theorem defectHom_ker_le_fFixed_range :
    (defectHom f hf α β hα hcomp hcentral).ker ≤ (fFixed f α β hcomp).range := by
  intro x hx
  let : CommGroup f.ker := kerCommGroup f hcentral
  have hxB : disp f hf α β hα hcomp hcentral x ∈
      kerCommutator f α β hα hcomp hcentral := by
    have hx1 : defectHom f hf α β hα hcomp hcentral x = 1 :=
      MonoidHom.mem_ker.mp hx
    rw [defectHom_apply] at hx1
    have hx' : defectNormElem f hf α β hα hcomp hcentral x ∈
        (kerCommutator f α β hα hcomp hcentral).subgroupOf
          (kerNormKer f α β hα hcomp hcentral) :=
      (QuotientGroup.eq_one_iff _).mp hx1
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨z, hz⟩ := (mem_commutatorSubgroup (alphaKer f α β hα hcomp)).mp hxB
  have hzX : (z : X) * (α (z : X))⁻¹ =
      (lift f hf β x)⁻¹ * α (lift f hf β x) := by
    have h := congrArg (fun c : f.ker => (c : X)) hz
    simpa [commutatorHom, alphaKer_apply_coe, disp_eq_defectElem, defectElem_coe] using h
  let w : X := lift f hf β x * (z : X)
  have hwfix : α w = w := by
    change α (lift f hf β x * (z : X)) = lift f hf β x * (z : X)
    rw [map_mul]
    have h : α (lift f hf β x) =
        lift f hf β x * ((z : X) * (α (z : X))⁻¹) := by
      rw [hzX]
      group
    rw [h]
    group
  refine ⟨⟨w, hwfix⟩, ?_⟩
  apply Subtype.ext
  change f (lift f hf β x * (z : X)) = (x : G)
  rw [map_mul, lift_spec]
  have hz1 : f (z : X) = 1 := z.property
  rw [hz1, mul_one]

theorem defectHom_ker_eq_fFixed_range :
    (defectHom f hf α β hα hcomp hcentral).ker = (fFixed f α β hcomp).range :=
  le_antisymm (defectHom_ker_le_fFixed_range f hf α β hα hcomp hcentral)
    (fFixed_range_le_defectHom_ker f hf α β hα hcomp hcentral)

instance kerDefectGroup_commGroup : CommGroup (kerDefectGroup f α β hα hcomp hcentral) := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  unfold kerDefectGroup
  infer_instance

theorem kerDefectGroup_pow_three (d : kerDefectGroup f α β hα hcomp hcentral) :
    d ^ 3 = 1 := by
  let : CommGroup f.ker := kerCommGroup f hcentral
  exact defectGroup_pow_three (alphaKer f α β hα hcomp) d

theorem pow_three_mem_fFixed_range (hf : Function.Surjective f) (hα : α ^ 3 = 1)
    (hcentral : f.ker ≤ Subgroup.center X) (x : TauCeti.fixedSubgroup β.toMonoidHom) :
    x ^ 3 ∈ (fFixed f α β hcomp).range := by
  rw [← defectHom_ker_eq_fFixed_range f hf α β hα hcomp hcentral]
  change defectHom f hf α β hα hcomp hcentral (x ^ 3) = 1
  rw [map_pow]
  exact kerDefectGroup_pow_three f α β hα hcomp hcentral _

theorem exists_fixed_lift_cube (hf : Function.Surjective f) (hα : α ^ 3 = 1)
    (hcentral : f.ker ≤ Subgroup.center X)
    (hcomp : f.comp α.toMonoidHom = β.toMonoidHom.comp f) {x : G} (hx : β x = x) :
    ∃ y : X, α y = y ∧ f y = x ^ 3 := by
  obtain ⟨y, hy⟩ := pow_three_mem_fFixed_range f α β hcomp hf hα hcentral ⟨x, hx⟩
  exact ⟨y, TauCeti.mem_fixedSubgroup.mp y.property, congrArg Subtype.val hy⟩

end Central

end CFSG.FixedCentralDefect

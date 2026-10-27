module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryTransvections
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXExtraspecialOddAction

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open scoped commutatorElement

namespace FourUnitary

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

variable (B) in
@[expose] def axisPerp (e : W) : Submodule F W :=
  LinearMap.ker (B e)

theorem mem_axisPerp {e x : W} : x ∈ axisPerp B e ↔ B e x = 0 :=
  LinearMap.mem_ker

variable (B) in
@[expose] def axisLineIn (e : W) : Submodule F (axisPerp B e) :=
  (F ∙ e).comap (axisPerp B e).subtype

variable (B) in
abbrev axisQuot (e : W) : Type _ :=
  axisPerp B e ⧸ axisLineIn B e

@[expose] def axisForm (hB : B.IsSymm) (e : W) :
    axisQuot B e →ₛₗ[hF.bar] axisQuot B e →ₗ[F] F :=
  (B.domRestrict₁₂ (axisPerp B e) (axisPerp B e)).liftQ₂ (axisLineIn B e) (axisLineIn B e)
    (fun x hx => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (Submodule.mem_comap.1 hx)
      rw [Submodule.subtype_apply] at hc
      refine LinearMap.mem_ker.2 (LinearMap.ext fun y => ?_)
      rw [LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply, ← hc, LinearMap.map_smulₛₗ₂,
        mem_axisPerp.1 y.2, smul_zero])
    (fun y hy => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (Submodule.mem_comap.1 hy)
      rw [Submodule.subtype_apply] at hc
      refine LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_)
      rw [LinearMap.flip_apply, LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply, ← hc,
        map_smul, ← hB.eq, mem_axisPerp.1 x.2, map_zero, smul_zero])

theorem axisForm_mk (hB : B.IsSymm) {e : W} (x y : axisPerp B e) :
    axisForm hB e (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y :=
  rfl

variable (B) in
@[expose] def axisStab (e : W) : Subgroup (LinearMap.GeneralLinearGroup F W) where
  carrier := {g | g ∈ sesqUnitaryGroup B ∧ (g : W →ₗ[F] W) e = e}
  one_mem' := ⟨one_mem _, rfl⟩
  mul_mem' {g g'} hg hg' := ⟨mul_mem hg.1 hg'.1, by
    rw [Units.val_mul, Module.End.mul_apply, hg'.2, hg.2]⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, by
    conv_lhs => rw [← hg.2]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]⟩

theorem apply_mem_axisPerp {e : W} {g : LinearMap.GeneralLinearGroup F W}
    (hg : g ∈ axisStab B e) {x : W} (hx : x ∈ axisPerp B e) :
    (g : W →ₗ[F] W) x ∈ axisPerp B e := by
  have h := hg.1 e x
  rw [hg.2] at h
  rw [mem_axisPerp, h]
  exact mem_axisPerp.1 hx

theorem sub_mem_axisPerp {e : W} {g : LinearMap.GeneralLinearGroup F W}
    (hg : g ∈ axisStab B e) (f : W) : (g : W →ₗ[F] W) f - f ∈ axisPerp B e := by
  have h := hg.1 e f
  rw [hg.2] at h
  rw [mem_axisPerp, map_sub, h, sub_self]

variable (B) in
@[expose] def axisKernel (e : W) : Subgroup (LinearMap.GeneralLinearGroup F W) where
  carrier := {g | g ∈ axisStab B e ∧ ∀ x ∈ axisPerp B e, (g : W →ₗ[F] W) x - x ∈ F ∙ e}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' {g g'} hg hg' := ⟨mul_mem hg.1 hg'.1, fun x hx => by
    have h : ((g * g' : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) x - x =
        (g : W →ₗ[F] W) ((g' : W →ₗ[F] W) x - x) + ((g : W →ₗ[F] W) x - x) := by
      rw [Units.val_mul, Module.End.mul_apply, map_sub]
      abel
    rw [h]
    refine Submodule.add_mem _ ?_ (hg.2 x hx)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hg'.2 x hx)
    rw [← hc, map_smul, hg.1.2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)⟩
  inv_mem' {g} hg := ⟨inv_mem hg.1, fun x hx => by
    have h := hg.2 _ (apply_mem_axisPerp (inv_mem hg.1) hx)
    rw [generalLinearGroup_apply_inv_apply] at h
    rw [← neg_sub]
    exact Submodule.neg_mem _ h⟩

theorem mem_axisKernel {e : W} {g : LinearMap.GeneralLinearGroup F W} :
    g ∈ axisKernel B e ↔ g ∈ sesqUnitaryGroup B ∧ (g : W →ₗ[F] W) e = e ∧
      ∀ x ∈ axisPerp B e, (g : W →ₗ[F] W) x - x ∈ F ∙ e :=
  and_assoc

variable (B) in
@[expose] def displacement (e f : W) (x : axisStab B e) : axisQuot B e :=
  Submodule.Quotient.mk
    ⟨((x : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f - f, sub_mem_axisPerp x.2 f⟩

variable (B) in
@[expose] def partnerPerp (e f : W) : Submodule F W :=
  (Submodule.span F {e, f}).orthogonalBilin B

theorem mem_partnerPerp {e f z : W} : z ∈ partnerPerp B e f ↔ B e z = 0 ∧ B f z = 0 := by
  rw [partnerPerp, Submodule.mem_orthogonalBilin]
  refine ⟨fun h => ⟨h e (Submodule.subset_span (by simp)), h f (Submodule.subset_span (by simp))⟩,
    fun h n hn => ?_⟩
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 hn
  rw [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂,
    LinearMap.map_smulₛₗ₂, h.1, h.2, smul_zero, smul_zero, add_zero]

variable (B) in
@[expose] def flagMap (e u : W) (a : F) : W →ₗ[F] W :=
  LinearMap.id + (B u + a • B e).smulRight e + (B e).smulRight u

theorem flagMap_apply (e u : W) (a : F) (x : W) :
    flagMap B e u a x = x + (B u x + a * B e x) • e + B e x • u := by
  simp [flagMap]

theorem flagMap_spec (hB : B.IsSymm) {e f u : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) (hu : u ∈ partnerPerp B e f) (a : F) :
    flagMap B e u a e = e ∧ (∀ z ∈ partnerPerp B e f, flagMap B e u a z = z + B u z • e) ∧
      flagMap B e u a f = f + u + a • e ∧
      ∀ r : W →ₗ[F] W, r e = e → (∀ z ∈ partnerPerp B e f, r z = z + B u z • e) →
        r f = f + u + a • e → r = flagMap B e u a := by
  obtain ⟨heu, hfu⟩ := mem_partnerPerp.1 hu
  have hue : B u e = 0 := by rw [← hB.eq, heu, map_zero]
  have huf : B u f = 0 := by rw [← hB.eq, hfu, map_zero]
  have hfe : B f e = 1 := by rw [← hB.eq, hef, map_one]
  have hr_e : flagMap B e u a e = e := by
    rw [flagMap_apply, hue, he, mul_zero, add_zero, zero_smul, zero_smul, add_zero, add_zero]
  have hr_z : ∀ z ∈ partnerPerp B e f, flagMap B e u a z = z + B u z • e := by
    intro z hz
    rw [flagMap_apply, (mem_partnerPerp.1 hz).1, mul_zero, add_zero, zero_smul, add_zero]
  have hr_f : flagMap B e u a f = f + u + a • e := by
    rw [flagMap_apply, huf, hef, mul_one, zero_add, one_smul]
    abel
  refine ⟨hr_e, hr_z, hr_f, fun r hre hrz hrf => LinearMap.ext fun x => ?_⟩
  set z := x - B f x • e - B e x • f with hz
  have hzD : z ∈ partnerPerp B e f := by
    rw [mem_partnerPerp, hz]
    simp [he, hf, hef, hfe]
  have hx : x = B f x • e + B e x • f + z := by
    rw [hz]
    abel
  rw [hx, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul, map_smul, hre, hrf,
    hrz z hzD, hr_e, hr_f, hr_z z hzD]

end FourUnitary

open FourUnitary Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups Subgroup in
theorem four_element_unitary_axis_flag_kernel_data {F : Type*} [Field F]
    (hF : UnitaryFieldData 2 1 F) {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {e : W} (he0 : e ≠ 0) (he : B e e = 0) :
    ((F ∙ e) ≤ axisPerp B e ∧
      (∀ x y : axisPerp B e,
        axisForm hB e (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y) ∧
      (axisForm hB e).IsSymm ∧ (axisForm hB e).SeparatingLeft ∧
      finrank F (axisQuot B e) = finrank F W - 2) ∧
    (axisKernel B e ≤ sesqUnitaryGroup B ∧
      (∀ g ∈ axisStab B e, ∀ x ∈ axisPerp B e, (g : W →ₗ[F] W) x ∈ axisPerp B e) ∧
      ∀ f : W, ∀ x ∈ axisStab B e, (x : W →ₗ[F] W) f - f ∈ axisPerp B e) ∧
    (∀ f : W, B f f = 0 → B e f = 1 → ∀ u ∈ partnerPerp B e f, ∀ a : F, hF.trace a = B u u →
      flagMap B e u a e = e ∧ (∀ z ∈ partnerPerp B e f, flagMap B e u a z = z + B u z • e) ∧
      flagMap B e u a f = f + u + a • e ∧
      ∀ r : W →ₗ[F] W, r e = e → (∀ z ∈ partnerPerp B e f, r z = z + B u z • e) →
        r f = f + u + a • e → r = flagMap B e u a) ∧
    ∀ P : Subgroup (LinearMap.GeneralLinearGroup F W), ∀ hT : hermTransvectionGL B he 1 ∈ P,
      IsExtraspecialPGroup 2 P → center P = zpowers ⟨_, hT⟩ →
      (∀ x y : P, x * y =
        y * x * ⟨_, hT⟩ ^ (commVal ⟨_, hT⟩ (x : P ⧸ center P) (y : P ⧸ center P)).val) ∧
      (∀ u : P ⧸ center P, commVal ⟨_, hT⟩ u u = 0) ∧
      (∀ u v : P ⧸ center P, commVal ⟨_, hT⟩ u v = commVal ⟨_, hT⟩ v u) ∧
      (∀ u u' v : P ⧸ center P,
        commVal ⟨_, hT⟩ (u * u') v = commVal ⟨_, hT⟩ u v + commVal ⟨_, hT⟩ u' v) ∧
      ∀ u : P ⧸ center P, (∀ v, commVal ⟨_, hT⟩ u v = 0) → u = 1 := by
  obtain ⟨f₀, hef₀, -⟩ := (hermitian_hyperbolic_splitting hF hB hBl he0 he).1
  have hle : (F ∙ e) ≤ axisPerp B e := by
    rw [Submodule.span_singleton_le_iff_mem, mem_axisPerp]
    exact he
  have hsymm : (axisForm hB e).IsSymm := ⟨fun q q' => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [axisForm_mk, axisForm_mk]
    exact hB.eq _ _⟩
  have hsep : (axisForm hB e).SeparatingLeft := by
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hx : ∀ y : axisPerp B e, B x y = 0 := fun y => hq (Submodule.Quotient.mk y)
    have hxw : ∀ w : W, B x w = B e w * B x f₀ := by
      intro w
      have hw : w - B e w • f₀ ∈ axisPerp B e := by
        rw [mem_axisPerp, map_sub, map_smul, hef₀, smul_eq_mul, mul_one, sub_self]
      have h := hx ⟨_, hw⟩
      simp only [map_sub, map_smul, smul_eq_mul] at h
      linear_combination h
    have hxe : (x : W) = hF.bar (B x f₀) • e := by
      refine sub_eq_zero.1 (hBl _ fun w => ?_)
      rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, hF.bar_bar, hxw w]
      ring
    rw [Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_comap.2 ?_
    rw [Submodule.subtype_apply, hxe]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
  have hdim : finrank F (axisQuot B e) = finrank F W - 2 := by
    have hrange : LinearMap.range (B e) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      exact ⟨c • f₀, by rw [map_smul, hef₀, smul_eq_mul, mul_one]⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (B e)
    rw [hrange, finrank_top, Module.finrank_self] at h1
    have h2 := Submodule.finrank_quotient_add_finrank (axisLineIn B e)
    have h3 : finrank F (axisLineIn B e) = 1 := by
      rw [axisLineIn, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
        finrank_span_singleton he0]
    have h4 : finrank F (axisPerp B e) = finrank F (LinearMap.ker (B e)) := rfl
    have h5 : finrank F (axisQuot B e) = finrank F (axisPerp B e ⧸ axisLineIn B e) := rfl
    omega
  refine ⟨⟨hle, fun x y => rfl, hsymm, hsep, hdim⟩,
    ⟨fun g hg => hg.1.1, fun g hg x hx => apply_mem_axisPerp hg hx,
      fun f x hx => sub_mem_axisPerp hx f⟩,
    fun f hf hef u hu a _ => flagMap_spec hB he hf hef hu a, ?_⟩
  intro P hT hext hZ
  have : Finite F := hF.finite
  have : Finite W := Module.finite_of_finite F
  have : Finite (W →ₗ[F] W) := Finite.of_injective _ DFunLike.coe_injective
  have H := commPairHyp_of_extraspecial hext hZ
  refine ⟨fun x y => ?_, H.commVal_self, H.commVal_comm, H.commVal_mul_left,
    fun u hu => H.eq_one_of_forall_commVal_eq_zero hu⟩
  rw [← H.commutatorElement_eq_zpow x y]
  have h : x * y = ⁅x, y⁆ * (y * x) := by
    rw [commutatorElement_def]
    group
  rw [h, (Subgroup.mem_center_iff.1 (H.comm_center x y) (y * x)).symm]

end CFSG.LocalAnalysis.GorensteinLyons

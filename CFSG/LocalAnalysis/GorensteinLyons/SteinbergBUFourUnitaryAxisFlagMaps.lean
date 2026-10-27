module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryAxisFlag

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace FourUnitary

namespace AxisFlag

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

section CharTwo

variable (hF)

include hF in
theorem add_self_vec (x : W) : x + x = 0 := by
  rw [← two_smul F x, two_eq_zero hF, zero_smul]

include hF in
theorem neg_vec (x : W) : -x = x :=
  neg_eq_of_add_eq_zero_right (add_self_vec hF x)

include hF in
theorem trace_eq (a : F) : hF.trace a = a + hF.bar a :=
  rfl

end CharTwo

theorem flagMap_comp {e : W} (he : B e e = 0) {u v : W} (hue : B u e = 0) (hev : B e v = 0)
    (a b : F) :
    flagMap B e u a ∘ₗ flagMap B e v b = flagMap B e (u + v) (a + b + B u v) := by
  ext x
  simp only [LinearMap.comp_apply, flagMap_apply, map_add, map_smul, LinearMap.add_apply, he,
    hev, hue, mul_zero, add_zero]
  module

theorem flagMap_zero_zero (e : W) : flagMap B e 0 0 = LinearMap.id := by
  ext x
  simp [flagMap_apply]

theorem flagMap_zero_one (e : W) : flagMap B e 0 1 = hermTransvection B e 1 := by
  ext x
  rw [flagMap_apply, transvection_one_apply]
  simp

theorem flagMap_isometry (hB : B.IsSymm) {e : W} (he : B e e = 0) {u : W} (heu : B e u = 0)
    {a : F} (htr : hF.trace a = B u u) (x y : W) :
    B (flagMap B e u a x) (flagMap B e u a y) = B x y := by
  have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
  have htr' : a + hF.bar a = B u u := htr
  simp only [flagMap_apply, map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply,
    LinearMap.smul_apply, map_smul, smul_eq_mul, he, heu, hue, mul_zero, add_zero, map_mul]
  rw [← hB.eq e x, ← hB.eq u x]
  linear_combination (hF.bar (B e x) * B e y) * htr' +
    (B u y * hF.bar (B e x) + B e y * hF.bar (B u x) + hF.bar (B e x) * B e y * B u u) *
      two_eq_zero hF

variable (B) in
@[expose] def flagGL (hB : B.IsSymm) {e : W} (he : B e e = 0) {u : W} (heu : B e u = 0) {a : F}
    (htr : hF.trace a = B u u) : LinearMap.GeneralLinearGroup F W where
  val := flagMap B e u a
  inv := flagMap B e u (hF.bar a)
  val_inv := by
    have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
    have htr' : a + hF.bar a = B u u := htr
    rw [Module.End.mul_eq_comp, flagMap_comp he hue heu, add_self_vec hF, htr',
      ← two_mul, two_eq_zero hF, zero_mul, flagMap_zero_zero]
    rfl
  inv_val := by
    have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
    have htr' : hF.bar a + a = B u u := by rw [add_comm]; exact htr
    rw [Module.End.mul_eq_comp, flagMap_comp he hue heu, add_self_vec hF, htr',
      ← two_mul, two_eq_zero hF, zero_mul, flagMap_zero_zero]
    rfl

theorem coe_flagGL (hB : B.IsSymm) {e : W} (he : B e e = 0) {u : W} (heu : B e u = 0) {a : F}
    (htr : hF.trace a = B u u) :
    (flagGL B hB he heu htr : W →ₗ[F] W) = flagMap B e u a :=
  rfl

theorem flagGL_mem (hB : B.IsSymm) {e : W} (he : B e e = 0) {u : W} (heu : B e u = 0) {a : F}
    (htr : hF.trace a = B u u) : flagGL B hB he heu htr ∈ axisKernel B e := by
  have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
  refine mem_axisKernel.2 ⟨mem_sesqUnitaryGroup.2 (flagMap_isometry hB he heu htr), ?_,
    fun x hx => ?_⟩
  · rw [coe_flagGL, flagMap_apply, hue, he, mul_zero, add_zero, zero_smul, zero_smul, add_zero,
      add_zero]
  · rw [coe_flagGL, flagMap_apply, mem_axisPerp.1 hx, mul_zero, add_zero, zero_smul, add_zero,
      add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)

theorem B_f_e (hB : B.IsSymm) {e f : W} (hef : B e f = 1) : B f e = 1 := by
  rw [← hB.eq e f, hef, map_one]

theorem norm_decomp (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {u : W} (hu : u ∈ partnerPerp B e f) (a : F) :
    B (f + u + a • e) (f + u + a • e) = hF.trace a + B u u := by
  obtain ⟨heu, hfu⟩ := mem_partnerPerp.1 hu
  have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
  have huf : B u f = 0 := by rw [← hB.eq f u, hfu, map_zero]
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, he, hf, hef, heu, hfu, hue, huf, B_f_e hB hef, mul_zero, add_zero,
    zero_add, mul_one, trace_eq]
  ring

theorem exists_decomp (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {y : W} (hy : B y y = 0) (hey : B e y = 1) :
    ∃ u ∈ partnerPerp B e f, ∃ a : F, hF.trace a = B u u ∧ y = f + u + a • e := by
  have huD : y - f - B f (y - f) • e ∈ partnerPerp B e f := by
    rw [mem_partnerPerp]
    constructor
    · rw [map_sub, map_sub, map_smul, hey, hef, he, smul_zero, sub_self, sub_zero]
    · rw [map_sub, map_smul, B_f_e hB hef, smul_eq_mul, mul_one, sub_self]
  have hyu : y = f + (y - f - B f (y - f) • e) + B f (y - f) • e := by abel
  refine ⟨_, huD, B f (y - f), ?_, hyu⟩
  have h := norm_decomp hB he hf hef huD (B f (y - f))
  rw [← hyu, hy] at h
  rw [eq_neg_of_add_eq_zero_left h.symm, neg_eq_self hF]

theorem decomp_unique (hB : B.IsSymm) {e f : W} (hf : B f f = 0) (hef : B e f = 1) {u u' : W}
    (hu : u ∈ partnerPerp B e f) (hu' : u' ∈ partnerPerp B e f) {a a' : F}
    (h : f + u + a • e = f + u' + a' • e) : u = u' ∧ a = a' := by
  have hB' := congrArg (B f) h
  simp only [map_add, map_smul, smul_eq_mul, hf, (mem_partnerPerp.1 hu).2,
    (mem_partnerPerp.1 hu').2, B_f_e hB hef, mul_one, zero_add] at hB'
  subst hB'
  exact ⟨add_left_cancel (add_right_cancel h), rfl⟩

theorem eq_flagMap_of_mem (hB : B.IsSymm) {e f : W} (he : B e e = 0) (hf : B f f = 0)
    (hef : B e f = 1) {g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ axisKernel B e) :
    ∃ u ∈ partnerPerp B e f, ∃ a : F, hF.trace a = B u u ∧
      (g : W →ₗ[F] W) = flagMap B e u a ∧ (g : W →ₗ[F] W) f = f + u + a • e := by
  obtain ⟨hgU, hge, hgz⟩ := mem_axisKernel.1 hg
  have hiso := mem_sesqUnitaryGroup.1 hgU
  have hgf : B ((g : W →ₗ[F] W) f) ((g : W →ₗ[F] W) f) = 0 := by rw [hiso, hf]
  have hegf : B e ((g : W →ₗ[F] W) f) = 1 := by rw [← hge, hiso, hef]
  obtain ⟨u, hu, a, htr, hy⟩ := exists_decomp hB he hf hef hgf hegf
  refine ⟨u, hu, a, htr, ?_, hy⟩
  refine ((flagMap_spec hB he hf hef hu a).2.2.2 (g : W →ₗ[F] W) hge (fun z hz => ?_) hy)
  obtain ⟨hez, hfz⟩ := mem_partnerPerp.1 hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hgz z (mem_axisPerp.2 hez))
  have hgz' : (g : W →ₗ[F] W) z = z + c • e := by rw [hc]; abel
  have h := hiso f z
  rw [hy, hgz', hfz] at h
  obtain ⟨heu, hfu⟩ := mem_partnerPerp.1 hu
  have hue : B u e = 0 := by rw [← hB.eq e u, heu, map_zero]
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, he, hez, hfz, hue, B_f_e hB hef, mul_zero, add_zero, zero_add,
    mul_one] at h
  rw [hgz', eq_neg_of_add_eq_zero_left h, neg_eq_self hF]

end AxisFlag

end FourUnitary

end CFSG.LocalAnalysis.GorensteinLyons

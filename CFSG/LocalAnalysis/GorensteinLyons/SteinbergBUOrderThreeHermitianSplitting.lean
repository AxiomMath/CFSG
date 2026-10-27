module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLOrderThreeHermitian
public import CFSG.LinearAlgebra.BinaryReflectionNormalizer
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryScalarQuotient

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

namespace OrderThreeSplitting

open OrderThreeHermitian FourUnitary QuadraticMap CFSG.LinearAlgebra
  CFSG.LocalAnalysis.ComponentInitial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Projection

variable {c : Module.End (ZMod 2) V}

theorem neg_eq_self_binary (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_right (zmod2_vec_add_self v)

theorem sub_eq_add_binary (u v : V) : u - v = u + v := by
  rw [sub_eq_add_neg, neg_eq_self_binary]

theorem cube_apply (hc : c ^ 3 = 1) (v : V) : c (c (c v)) = v := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_two, ← pow_succ, hc,
    Module.End.one_apply]

theorem sq_apply (v : V) : (c ^ 2) v = c (c v) := by
  rw [pow_two, Module.End.mul_apply]

theorem traceEnd_apply (v : V) : traceEnd c v = v + c v + c (c v) := by
  rw [traceEnd, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, sq_apply]

theorem mem_fixedSpace_iff {v : V} : v ∈ fixedSpace c ↔ c v = v := by
  rw [fixedSpace, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem apply_add_mem_movedSpace (v : V) : c v + v ∈ movedSpace c :=
  ⟨v, by rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_binary]⟩

theorem sq_apply_of_mem_moved (hc : c ^ 3 = 1) {w : V} (hw : w ∈ movedSpace c) :
    c (c w) = c w + w := by
  have h := sq_add_self_add_one_on_moved hc hw
  rw [add_assoc] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_self_binary]

theorem traceEnd_mem_fixedSpace (hc : c ^ 3 = 1) (v : V) : traceEnd c v ∈ fixedSpace c := by
  rw [mem_fixedSpace_iff, traceEnd_apply, map_add, map_add, cube_apply hc]
  abel

theorem traceEnd_apply_of_mem_fixed {v : V} (hv : v ∈ fixedSpace c) : traceEnd c v = v := by
  rw [mem_fixedSpace_iff] at hv
  rw [traceEnd_apply, hv, hv, zmod2_vec_add_self, zero_add]

theorem traceEnd_apply_of_mem_moved (hc : c ^ 3 = 1) {w : V} (hw : w ∈ movedSpace c) :
    traceEnd c w = 0 := by
  rw [traceEnd_apply, ← sq_add_self_add_one_on_moved hc hw]
  abel

theorem mem_movedSpace_of_traceEnd {v : V} (hv : traceEnd c v = 0) : v ∈ movedSpace c := by
  rw [traceEnd_apply, add_assoc] at hv
  rw [eq_neg_of_add_eq_zero_left hv, neg_eq_self_binary, add_comm]
  exact apply_add_mem_movedSpace (c v)

theorem sub_traceEnd_mem_moved (hc : c ^ 3 = 1) (v : V) : v - traceEnd c v ∈ movedSpace c := by
  refine mem_movedSpace_of_traceEnd ?_
  rw [map_sub, traceEnd_apply_of_mem_fixed (traceEnd_mem_fixedSpace hc v), sub_self]

theorem ker_traceEnd (hc : c ^ 3 = 1) : LinearMap.ker (traceEnd c) = movedSpace c := by
  ext v
  exact ⟨mem_movedSpace_of_traceEnd, traceEnd_apply_of_mem_moved hc⟩

theorem range_traceEnd (hc : c ^ 3 = 1) : LinearMap.range (traceEnd c) = fixedSpace c := by
  ext v
  refine ⟨?_, fun hv => ⟨v, traceEnd_apply_of_mem_fixed hv⟩⟩
  rintro ⟨u, rfl⟩
  exact traceEnd_mem_fixedSpace hc u

theorem isCompl_fixed_moved (hc : c ^ 3 = 1) : IsCompl (fixedSpace c) (movedSpace c) := by
  refine ⟨Submodule.disjoint_def.2 fun v hv hw => ?_, ?_⟩
  · rw [← traceEnd_apply_of_mem_fixed hv]
    exact traceEnd_apply_of_mem_moved hc hw
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    exact Submodule.mem_sup.2 ⟨traceEnd c v, traceEnd_mem_fixedSpace hc v, v - traceEnd c v,
      sub_traceEnd_mem_moved hc v, by abel⟩

theorem traceEnd_sq (hc : c ^ 3 = 1) : traceEnd (c ^ 2) = traceEnd c := by
  have h4 : (c ^ 2) ^ 2 = c := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hc, one_mul]
  rw [traceEnd, traceEnd, h4]
  abel

theorem sq_cube (hc : c ^ 3 = 1) : (c ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hc, one_pow]

theorem fixedSpace_sq (hc : c ^ 3 = 1) : fixedSpace (c ^ 2) = fixedSpace c := by
  rw [← range_traceEnd (sq_cube hc), traceEnd_sq hc, range_traceEnd hc]

theorem movedSpace_sq (hc : c ^ 3 = 1) : movedSpace (c ^ 2) = movedSpace c := by
  rw [← ker_traceEnd (sq_cube hc), traceEnd_sq hc, ker_traceEnd hc]

end Projection

section Polar

variable {q : QuadraticForm (ZMod 2) V} {c : Module.End (ZMod 2) V}

theorem polar_map_map {F : Type*} [FunLike F V V] [AddHomClass F V V] {g : F}
    (hg : ∀ v, q (g v) = q v) (u v : V) : polar q (g u) (g v) = polar q u v := by
  rw [polar, polar, ← map_add, hg, hg, hg]

theorem polar_fixed_moved (hq : ∀ v, q (c v) = q v) {x y : V} (hx : x ∈ fixedSpace c)
    (hy : y ∈ movedSpace c) : polar q x y = 0 := by
  obtain ⟨u, rfl⟩ := hy
  rw [mem_fixedSpace_iff] at hx
  have h := polar_map_map hq x u
  rw [hx] at h
  rw [LinearMap.sub_apply, Module.End.one_apply, polar_sub_right, h, sub_self]

theorem eq_zero_of_orth (hb : (polarBilin q).Nondegenerate) (hc : c ^ 3 = 1) {z : V}
    (h₀ : ∀ x ∈ fixedSpace c, polar q z x = 0) (h₁ : ∀ y ∈ movedSpace c, polar q z y = 0) :
    z = 0 := by
  refine hb.1 z fun v => ?_
  rw [polarBilin_apply_apply, show v = traceEnd c v + (v - traceEnd c v) by abel,
    polar_add_right, h₀ _ (traceEnd_mem_fixedSpace hc v), h₁ _ (sub_traceEnd_mem_moved hc v),
    add_zero]

theorem moved_nondeg (hb : (polarBilin q).Nondegenerate) (hq : ∀ v, q (c v) = q v)
    (hc : c ^ 3 = 1) {x : V} (hx : x ∈ movedSpace c)
    (h : ∀ y ∈ movedSpace c, polar q x y = 0) : x = 0 :=
  eq_zero_of_orth hb hc (fun _ hy => by rw [polar_comm]; exact polar_fixed_moved hq hy hx) h

theorem polar_apply_left (hq : ∀ v, q (c v) = q v) (hc : c ^ 3 = 1) (x : V) {y : V}
    (hy : y ∈ movedSpace c) : polar q (c x) y = polar q x y + polar q x (c y) := by
  conv_lhs => rw [← cube_apply hc y]
  rw [polar_map_map hq, sq_apply_of_mem_moved hc hy, polar_add_right, add_comm]

end Polar

section Form

variable {q : QuadraticForm (ZMod 2) V} {c : Module.End (ZMod 2) V} {hc : c ^ 3 = 1}

theorem algebraMap_sq (a : ZMod 2) :
    algebraMap (ZMod 2) OmegaField a ^ 2 = algebraMap (ZMod 2) OmegaField a := by
  rw [← map_pow]
  congr 1
  revert a
  decide

theorem smul_eq_zsmul (a b : ZMod 2) (x : MovedSpace c hc) :
    (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) • x =
      a • x + b • (omega • x) := by
  rw [add_smul, mul_smul, algebraMap_smul', algebraMap_smul']

theorem toV_smul_eq (a b : ZMod 2) (x : MovedSpace c hc) :
    toV c hc ((algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) • x) =
      a • toV c hc x + b • c (toV c hc x) := by
  rw [smul_eq_zsmul, map_add, map_smul, map_smul, toV_omega_smul]

theorem toV_omega_sq_smul (x : MovedSpace c hc) :
    toV c hc (omega ^ 2 • x) = c (c (toV c hc x)) := by
  rw [pow_two, mul_smul, toV_omega_smul, toV_omega_smul]

theorem toV_smul_sq_eq (a b : ZMod 2) (x : MovedSpace c hc) :
    toV c hc ((algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) ^ 2 •
      x) = a • toV c hc x + b • c (c (toV c hc x)) := by
  rw [omegaField_sq, add_smul, mul_smul, algebraMap_smul', algebraMap_smul', map_add, map_smul,
    map_smul, toV_omega_sq_smul]

theorem orderThreeForm_eq (x y : MovedSpace c hc) :
    orderThreeForm q c hc x y =
      omega ^ 2 * algebraMap (ZMod 2) OmegaField (polar q (toV c hc x) (toV c hc y)) +
        algebraMap (ZMod 2) OmegaField (polar q (toV c hc x) (c (toV c hc y))) :=
  rfl

theorem form_add_left (x₁ x₂ y : MovedSpace c hc) :
    orderThreeForm q c hc (x₁ + x₂) y =
      orderThreeForm q c hc x₁ y + orderThreeForm q c hc x₂ y := by
  simp only [orderThreeForm_eq, map_add, polar_add_left]
  ring

theorem form_add_right (x y₁ y₂ : MovedSpace c hc) :
    orderThreeForm q c hc x (y₁ + y₂) =
      orderThreeForm q c hc x y₁ + orderThreeForm q c hc x y₂ := by
  simp only [orderThreeForm_eq, map_add, polar_add_right]
  ring

theorem form_zsmul_left (a : ZMod 2) (x y : MovedSpace c hc) :
    orderThreeForm q c hc (a • x) y =
      algebraMap (ZMod 2) OmegaField a * orderThreeForm q c hc x y := by
  simp only [orderThreeForm_eq, map_smul, polar_smul_left, smul_eq_mul, map_mul]
  ring

theorem form_zsmul_right (a : ZMod 2) (x y : MovedSpace c hc) :
    orderThreeForm q c hc x (a • y) =
      algebraMap (ZMod 2) OmegaField a * orderThreeForm q c hc x y := by
  simp only [orderThreeForm_eq, map_smul, polar_smul_right, smul_eq_mul, map_mul]
  ring

theorem form_omega_left (hq : ∀ v, q (c v) = q v) (x y : MovedSpace c hc) :
    orderThreeForm q c hc (omega • x) y = omega ^ 2 * orderThreeForm q c hc x y := by
  rw [orderThreeForm_eq, orderThreeForm_eq, toV_omega_smul, polar_apply_left hq hc _ (toV_mem y),
    polar_map_map hq, map_add]
  have h1 := omega_sq
  have h2 := omegaField_two_eq_zero
  grind

theorem form_omega_right (x y : MovedSpace c hc) :
    orderThreeForm q c hc x (omega • y) = omega * orderThreeForm q c hc x y := by
  rw [orderThreeForm_eq, orderThreeForm_eq, toV_omega_smul, sq_apply_of_mem_moved hc (toV_mem y),
    polar_add_right, map_add]
  have h1 := omega_sq
  have h2 := omegaField_two_eq_zero
  grind

theorem form_smul_left (hq : ∀ v, q (c v) = q v) (a : OmegaField) (x y : MovedSpace c hc) :
    orderThreeForm q c hc (a • x) y = a ^ 2 * orderThreeForm q c hc x y := by
  obtain ⟨α, β, rfl⟩ := omegaField_eq a
  rw [smul_eq_zsmul, form_add_left, form_zsmul_left, form_zsmul_left, form_omega_left hq,
    omegaField_sq]
  ring

theorem form_smul_right (a : OmegaField) (x y : MovedSpace c hc) :
    orderThreeForm q c hc x (a • y) = a * orderThreeForm q c hc x y := by
  obtain ⟨α, β, rfl⟩ := omegaField_eq a
  rw [smul_eq_zsmul, form_add_right, form_zsmul_right, form_zsmul_right, form_omega_right]
  ring

theorem form_symm (hq : ∀ v, q (c v) = q v) (x y : MovedSpace c hc) :
    orderThreeForm q c hc y x = orderThreeForm q c hc x y ^ 2 := by
  have hb0 := algebraMap_sq (polar q (toV c hc x) (toV c hc y))
  have hb1 := algebraMap_sq (polar q (toV c hc x) (c (toV c hc y)))
  rw [orderThreeForm_eq, orderThreeForm_eq, polar_comm q (toV c hc y) (toV c hc x),
    polar_comm q (toV c hc y) (c (toV c hc x)), polar_apply_left hq hc _ (toV_mem y), map_add]
  have h1 := omega_sq
  have h2 := omegaField_two_eq_zero
  grind

theorem form_trace (x y : MovedSpace c hc) :
    orderThreeForm q c hc x y + orderThreeForm q c hc x y ^ 2 =
      algebraMap (ZMod 2) OmegaField (polar q (toV c hc x) (toV c hc y)) := by
  have hb0 := algebraMap_sq (polar q (toV c hc x) (toV c hc y))
  have hb1 := algebraMap_sq (polar q (toV c hc x) (c (toV c hc y)))
  rw [orderThreeForm_eq]
  have h1 := omega_sq
  have h2 := omegaField_two_eq_zero
  grind

variable (q c hc) in
@[expose] def hermForm (hq : ∀ v, q (c v) = q v) :
    MovedSpace c hc →ₛₗ[unitaryFieldData_omegaField.bar] MovedSpace c hc →ₗ[OmegaField]
      OmegaField :=
  LinearMap.mk₂'ₛₗ unitaryFieldData_omegaField.bar (RingHom.id OmegaField)
    (orderThreeForm q c hc) form_add_left
    (fun a x y => by rw [form_smul_left hq, smul_eq_mul, bar_eq_sq]) form_add_right
    (fun a x y => by rw [form_smul_right, smul_eq_mul, RingHom.id_apply])

theorem hermForm_apply (hq : ∀ v, q (c v) = q v) (x y : MovedSpace c hc) :
    hermForm q c hc hq x y = orderThreeForm q c hc x y :=
  rfl

theorem hermForm_separatingLeft (hb : (polarBilin q).Nondegenerate) (hq : ∀ v, q (c v) = q v) :
    (hermForm q c hc hq).SeparatingLeft := by
  intro x hx
  apply toV_injective
  rw [map_zero]
  refine moved_nondeg hb hq hc (toV_mem x) fun y hy => ?_
  have h := form_trace (q := q) (hc := hc) x (⟨y, hy⟩ : movedSpace c)
  have h0 : orderThreeForm q c hc x ⟨y, hy⟩ = 0 := hx _
  rw [h0, zero_pow two_ne_zero, add_zero] at h
  exact (algebraMap (ZMod 2) OmegaField).injective (h.symm.trans (map_zero _).symm)

end Form

section Normalizer

theorem apply_comm_of_conj_eq {c g : V ≃ₗ[ZMod 2] V} (h : g * c * g⁻¹ = c) (v : V) :
    g (c v) = c (g v) := by
  have h' := DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.1 h) v
  rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h'

theorem apply_sq_of_conj_eq_sq {c g : V ≃ₗ[ZMod 2] V} (h : g * c * g⁻¹ = c ^ 2) (v : V) :
    g (c v) = c (c (g v)) := by
  have h' := DFunLike.congr_fun (mul_inv_eq_iff_eq_mul.1 h) v
  rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, pow_two, LinearEquiv.mul_apply] at h'

theorem conj_cases {c g : V ≃ₗ[ZMod 2] V} (hc3 : orderOf c = 3)
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (V ≃ₗ[ZMod 2] V))) :
    (∀ v, g (c v) = c (g v)) ∨ ∀ v, g (c v) = c (c (g v)) :=
  (conj_eq_or_eq_sq_of_mem_normalizer hc3 hg).imp apply_comm_of_conj_eq apply_sq_of_conj_eq_sq

variable {c : Module.End (ZMod 2) V}

theorem map_fixedSpace_of_comm {g : V ≃ₗ[ZMod 2] V} {d : Module.End (ZMod 2) V}
    (hd : fixedSpace d = fixedSpace c) (hgd : ∀ v, g (c v) = d (g v)) {v : V}
    (hv : v ∈ fixedSpace c) : g v ∈ fixedSpace c := by
  rw [← hd, mem_fixedSpace_iff, ← hgd, mem_fixedSpace_iff.1 hv]

theorem map_movedSpace_of_comm {g : V ≃ₗ[ZMod 2] V} {d : Module.End (ZMod 2) V}
    (hd : movedSpace d = movedSpace c) (hgd : ∀ v, g (c v) = d (g v)) {w : V}
    (hw : w ∈ movedSpace c) : g w ∈ movedSpace c := by
  obtain ⟨u, rfl⟩ := hw
  rw [← hd]
  refine ⟨g u, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
    map_sub, hgd]

theorem maps_of_conj_cases (hc : c ^ 3 = 1) {g : V ≃ₗ[ZMod 2] V}
    (hg : (∀ v, g (c v) = c (g v)) ∨ ∀ v, g (c v) = c (c (g v))) :
    (∀ v ∈ fixedSpace c, g v ∈ fixedSpace c) ∧ ∀ w ∈ movedSpace c, g w ∈ movedSpace c := by
  rcases hg with hg | hg
  · exact ⟨fun v => map_fixedSpace_of_comm rfl hg, fun w => map_movedSpace_of_comm rfl hg⟩
  · have hgd : ∀ v, g (c v) = (c ^ 2) (g v) := fun v => by rw [sq_apply, hg]
    exact ⟨fun v => map_fixedSpace_of_comm (fixedSpace_sq hc) hgd,
      fun w => map_movedSpace_of_comm (movedSpace_sq hc) hgd⟩

variable {hc : c ^ 3 = 1} {q : QuadraticForm (ZMod 2) V}

variable (c hc) in
@[expose] def restrictMoved (g : V ≃ₗ[ZMod 2] V) (hg : ∀ w ∈ movedSpace c, g w ∈ movedSpace c)
    (hg' : ∀ w ∈ movedSpace c, g.symm w ∈ movedSpace c) : Equiv.Perm (MovedSpace c hc) where
  toFun x := (⟨g (toV c hc x), hg _ (toV_mem x)⟩ : movedSpace c)
  invFun x := (⟨g.symm (toV c hc x), hg' _ (toV_mem x)⟩ : movedSpace c)
  left_inv x := toV_injective (g.symm_apply_apply (toV c hc x))
  right_inv x := toV_injective (g.apply_symm_apply (toV c hc x))

variable {g : V ≃ₗ[ZMod 2] V} {gW : MovedSpace c hc → MovedSpace c hc}

theorem restrict_add (hgW : ∀ x, toV c hc (gW x) = g (toV c hc x)) (x y : MovedSpace c hc) :
    gW (x + y) = gW x + gW y :=
  toV_injective (by rw [hgW, map_add, map_add, map_add, hgW, hgW])

theorem restrict_smul_of_commute (hgc : ∀ v, g (c v) = c (g v))
    (hgW : ∀ x, toV c hc (gW x) = g (toV c hc x)) (a : OmegaField) (x : MovedSpace c hc) :
    gW (a • x) = a • gW x := by
  obtain ⟨α, β, rfl⟩ := omegaField_eq a
  apply toV_injective
  rw [hgW, toV_smul_eq, toV_smul_eq, map_add, map_smul, map_smul, hgc, hgW]

theorem restrict_smul_of_conj_sq (hgc : ∀ v, g (c v) = c (c (g v)))
    (hgW : ∀ x, toV c hc (gW x) = g (toV c hc x)) (a : OmegaField) (x : MovedSpace c hc) :
    gW (a • x) = a ^ 2 • gW x := by
  obtain ⟨α, β, rfl⟩ := omegaField_eq a
  apply toV_injective
  rw [hgW, toV_smul_eq, toV_smul_sq_eq, map_add, map_smul, map_smul, hgc, hgW]

theorem restrict_form_of_commute (hgq : ∀ v, q (g v) = q v) (hgc : ∀ v, g (c v) = c (g v))
    (hgW : ∀ x, toV c hc (gW x) = g (toV c hc x)) (x y : MovedSpace c hc) :
    orderThreeForm q c hc (gW x) (gW y) = orderThreeForm q c hc x y := by
  rw [orderThreeForm_eq, orderThreeForm_eq, hgW, hgW, ← hgc, polar_map_map hgq, polar_map_map hgq]

theorem restrict_form_of_conj_sq (hgq : ∀ v, q (g v) = q v)
    (hgc : ∀ v, g (c v) = c (c (g v))) (hgW : ∀ x, toV c hc (gW x) = g (toV c hc x))
    (x y : MovedSpace c hc) :
    orderThreeForm q c hc (gW x) (gW y) = orderThreeForm q c hc x y ^ 2 := by
  have hcg : ∀ v, c (g v) = g (c (c v)) := fun v => by rw [hgc, hgc, cube_apply hc]
  have hb0 := algebraMap_sq (polar q (toV c hc x) (toV c hc y))
  have hb1 := algebraMap_sq (polar q (toV c hc x) (c (toV c hc y)))
  rw [orderThreeForm_eq, orderThreeForm_eq, hgW, hgW, hcg, polar_map_map hgq, polar_map_map hgq,
    sq_apply_of_mem_moved hc (toV_mem y), polar_add_right, map_add]
  have h1 := omega_sq
  have h2 := omegaField_two_eq_zero
  grind

end Normalizer

section Assembly

variable {c : V ≃ₗ[ZMod 2] V} {hc : c.toLinearMap ^ 3 = 1} {q : QuadraticForm (ZMod 2) V}

theorem hermForm_isSymm (hq : ∀ v, q (c.toLinearMap v) = q v) :
    (hermForm q c.toLinearMap hc hq).IsSymm :=
  LinearMap.isSymm_def.2 fun x y => by
    rw [hermForm_apply, hermForm_apply, form_symm hq x y, bar_eq_sq]

theorem restrict_mem_semiUnitaryGroup (hq : ∀ v, q (c.toLinearMap v) = q v) {g : V ≃ₗ[ZMod 2] V}
    (hgq : ∀ v, q (g v) = q v) (hcases : (∀ v, g (c v) = c (g v)) ∨ ∀ v, g (c v) = c (c (g v)))
    {gW : Equiv.Perm (MovedSpace c.toLinearMap hc)}
    (hgW : ∀ x, toV _ hc (gW x) = g (toV _ hc x)) :
    gW ∈ semiUnitaryGroup (hermForm q c.toLinearMap hc hq) := by
  refine mem_semiUnitaryGroup.2 ⟨restrict_add hgW, ?_⟩
  rcases hcases with hgc | hgc
  · exact ⟨RingEquiv.refl _, restrict_smul_of_commute hgc hgW,
      restrict_form_of_commute hgq hgc hgW⟩
  · refine ⟨barEquiv unitaryFieldData_omegaField, fun a x => ?_, fun x y => ?_⟩
    · rw [barEquiv_apply, bar_eq_sq]
      exact restrict_smul_of_conj_sq hgc hgW a x
    · rw [barEquiv_apply, bar_eq_sq]
      exact restrict_form_of_conj_sq hgq hgc hgW x y

theorem exists_restrict_unitary (hq : ∀ v, q (c.toLinearMap v) = q v) {g : V ≃ₗ[ZMod 2] V}
    (hgq : ∀ v, q (g v) = q v) (hgc : ∀ v, g (c v) = c (g v))
    {gW : Equiv.Perm (MovedSpace c.toLinearMap hc)}
    (hgW : ∀ x, toV _ hc (gW x) = g (toV _ hc x)) :
    ∃ gL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc),
      (∀ x, (gL : Module.End OmegaField (MovedSpace c.toLinearMap hc)) x = gW x) ∧
      gL ∈ sesqUnitaryGroup (hermForm q c.toLinearMap hc hq) := by
  let e : MovedSpace c.toLinearMap hc ≃ₗ[OmegaField] MovedSpace c.toLinearMap hc :=
    { toFun := gW
      invFun := gW.symm
      left_inv := gW.left_inv
      right_inv := gW.right_inv
      map_add' := restrict_add hgW
      map_smul' := restrict_smul_of_commute hgc hgW }
  exact ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm e, fun x => rfl,
    mem_sesqUnitaryGroup.2 fun x y => restrict_form_of_commute hgq hgc hgW x y⟩

theorem restrict_normalizer (hc3 : orderOf c = 3) (hc : c.toLinearMap ^ 3 = 1)
    (hq : ∀ v, q (c.toLinearMap v) = q v) {g : V ≃ₗ[ZMod 2] V} (hgq : ∀ v, q (g v) = q v)
    (hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (V ≃ₗ[ZMod 2] V))) :
    (∀ v ∈ fixedSpace c.toLinearMap, g v ∈ fixedSpace c.toLinearMap) ∧
      (∀ w ∈ movedSpace c.toLinearMap, g w ∈ movedSpace c.toLinearMap) ∧
      ∃ gW : Equiv.Perm (MovedSpace c.toLinearMap hc),
        (∀ x, toV _ hc (gW x) = g (toV _ hc x)) ∧
        gW ∈ semiUnitaryGroup (hermForm q c.toLinearMap hc hq) ∧
        (g * c * g⁻¹ = c → (∀ (a : OmegaField) x, gW (a • x) = a • gW x) ∧
          ∃ gL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc),
            (∀ x, (gL : Module.End OmegaField (MovedSpace c.toLinearMap hc)) x = gW x) ∧
            gL ∈ sesqUnitaryGroup (hermForm q c.toLinearMap hc hq)) ∧
        (g * c * g⁻¹ = c ^ 2 → (∀ (a : OmegaField) x, gW (a • x) = a ^ 2 • gW x) ∧
          ∀ x y, hermForm q c.toLinearMap hc hq (gW x) (gW y) =
            hermForm q c.toLinearMap hc hq x y ^ 2) := by
  have hcases := conj_cases hc3 hgN
  have hmaps := maps_of_conj_cases (c := c.toLinearMap) hc hcases
  have hmaps' := maps_of_conj_cases (c := c.toLinearMap) (g := g⁻¹) hc
    (conj_cases hc3 (inv_mem hgN))
  have hgW : ∀ x, toV _ hc (restrictMoved c.toLinearMap hc g hmaps.2 hmaps'.2 x) =
      g (toV _ hc x) := fun x => rfl
  refine ⟨hmaps.1, hmaps.2, restrictMoved c.toLinearMap hc g hmaps.2 hmaps'.2, hgW,
    restrict_mem_semiUnitaryGroup hq hgq hcases hgW, fun h => ?_, fun h => ?_⟩
  · exact ⟨restrict_smul_of_commute (apply_comm_of_conj_eq h) hgW,
      exists_restrict_unitary hq hgq (apply_comm_of_conj_eq h) hgW⟩
  · exact ⟨restrict_smul_of_conj_sq (apply_sq_of_conj_eq_sq h) hgW,
      restrict_form_of_conj_sq hgq (apply_sq_of_conj_eq_sq h) hgW⟩

end Assembly

end OrderThreeSplitting

end CFSG.LocalAnalysis.GorensteinLyons

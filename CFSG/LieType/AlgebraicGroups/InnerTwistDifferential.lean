module

public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

theorem algHom_mul_eq_comp (φ ψ : A →ₐ[k] A) : φ * ψ = φ.comp ψ :=
  AlgHom.ext fun _ => rfl

theorem algHom_comp_ofId {B : Type} [Semiring B] [Algebra k B] (f : A →ₐ[k] B) :
    f.comp (Algebra.ofId k A) = Algebra.ofId k B :=
  Algebra.ext_id_iff.mpr trivial

theorem bialgHom_comp_antipode (σ : A →ₐc[k] A) :
    (σ : A →ₐ[k] A).comp (antipodeAlgHom k A) = (antipodeAlgHom k A).comp (σ : A →ₐ[k] A) := by
  have h1 : toConv ((antipodeAlgHom k A).comp (σ : A →ₐ[k] A)) * toConv (σ : A →ₐ[k] A) = 1 := by
    have h := AlgHom.convMul_comp_bialgHom_distrib (toConv (antipodeAlgHom k A))
      (toConv (AlgHom.id k A)) σ
    rw [AlgHom.antipode_id_cancel] at h
    have h2 : (1 : WithConv (A →ₐ[k] A)).ofConv.comp (σ : A →ₐ[k] A) =
        (1 : WithConv (A →ₐ[k] A)).ofConv := by
      rw [AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
    rw [h2] at h
    have h3 := congrArg toConv h
    simp only [toConv_ofConv] at h3
    rw [h3]
    rfl
  have h4 := inv_eq_of_mul_eq_one_left h1
  have h5 : (toConv (σ : A →ₐ[k] A))⁻¹ = toConv ((σ : A →ₐ[k] A).comp (antipodeAlgHom k A)) :=
    rfl
  rw [h5] at h4
  have h6 := congrArg ofConv h4
  simp only at h6
  exact h6

@[expose] def constPoint (a : WithConv (A →ₐ[k] k)) : WithConv (A →ₐ[k] A) :=
  toConv ((Algebra.ofId k A).comp a.ofConv)

theorem constPoint_mul (a b : WithConv (A →ₐ[k] k)) :
    constPoint (a * b) = constPoint a * constPoint b := by
  unfold constPoint
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv]

theorem constPoint_one : constPoint (1 : WithConv (A →ₐ[k] k)) = 1 := by
  unfold constPoint
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc,
    algHom_comp_ofId]

theorem comp_constPoint {B : Type} [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (a : WithConv (A →ₐ[k] k)) :
    f.comp (constPoint a).ofConv = (Algebra.ofId k B).comp a.ofConv := by
  unfold constPoint
  rw [ofConv_toConv, ← AlgHom.comp_assoc, algHom_comp_ofId]

theorem point_comp_constPoint (h a : WithConv (A →ₐ[k] k)) :
    h.ofConv.comp (constPoint a).ofConv = a.ofConv := by
  rw [comp_constPoint]
  ext x
  rfl

theorem comp_convInv {B : Type} [CommRing B] [Bialgebra k B] {C : Type} [CommRing C]
    [Bialgebra k C] (f : B →ₐ[k] C) (g : WithConv (A →ₐ[k] B)) :
    f.comp g⁻¹.ofConv = (toConv (f.comp g.ofConv))⁻¹.ofConv :=
  rfl

@[expose] def innerCo (a : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (constPoint a * toConv (AlgHom.id k A) * (constPoint a)⁻¹).ofConv

theorem point_comp_innerCo (h a : WithConv (A →ₐ[k] k)) :
    toConv (h.ofConv.comp (innerCo a)) = a * h * a⁻¹ := by
  unfold innerCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
    comp_convInv, point_comp_constPoint, ofConv_toConv, ofConv_toConv, AlgHom.comp_id]

theorem algHom_comp_innerCo (f : A →ₐ[k] A) (a : WithConv (A →ₐ[k] k)) :
    toConv (f.comp (innerCo a)) = constPoint a * toConv f * (constPoint a)⁻¹ := by
  unfold innerCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
    comp_convInv, comp_constPoint, AlgHom.comp_id]
  rfl

theorem innerCo_comp_innerCo (a b : WithConv (A →ₐ[k] k)) :
    (innerCo b).comp (innerCo a) = innerCo (a * b) := by
  have h1 := algHom_comp_innerCo (innerCo b) a
  have h2 : toConv (innerCo (a * b)) = constPoint a * toConv (innerCo b) * (constPoint a)⁻¹ := by
    unfold innerCo
    simp only [toConv_ofConv, constPoint_mul]
    group
  exact toConv_injective (h1.trans h2.symm)

theorem innerCo_one : innerCo (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  unfold innerCo
  rw [constPoint_one, one_mul, inv_one, mul_one, ofConv_toConv]

theorem counit_comp_innerCo (a : WithConv (A →ₐ[k] k)) :
    (counitAlgHom k A).comp (innerCo a) = counitAlgHom k A := by
  have h1 := point_comp_innerCo (1 : WithConv (A →ₐ[k] k)) a
  rw [mul_one, mul_inv_cancel] at h1
  have h2 : (1 : WithConv (A →ₐ[k] k)).ofConv = counitAlgHom k A := by
    rw [AlgHom.convOne_def, ofConv_toConv]
    ext x
    rfl
  have h3 := congrArg ofConv h1
  simp only at h3
  rw [h2] at h3
  exact h3

@[expose] def pointMap (σ : A →ₐc[k] A) : WithConv (A →ₐ[k] k) →* WithConv (A →ₐ[k] k) where
  toFun h := toConv (h.ofConv.comp (σ : A →ₐ[k] A))
  map_one' := by
    rw [AlgHom.convOne_def, ofConv_toConv, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' g h := by
    rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv]

theorem pointMap_apply (σ : A →ₐc[k] A) (h : WithConv (A →ₐ[k] k)) :
    pointMap σ h = toConv (h.ofConv.comp (σ : A →ₐ[k] A)) :=
  rfl

theorem innerCo_comp_bialgHom (σ : A →ₐc[k] A) (a : WithConv (A →ₐ[k] k)) :
    (innerCo a).comp (σ : A →ₐ[k] A) = (σ : A →ₐ[k] A).comp (innerCo (pointMap σ a)) := by
  apply toConv_injective
  rw [algHom_comp_innerCo]
  unfold innerCo
  rw [AlgHom.convMul_comp_bialgHom_distrib, toConv_ofConv, AlgHom.convMul_comp_bialgHom_distrib,
    toConv_ofConv]
  have e1 : (constPoint a).ofConv.comp (σ : A →ₐ[k] A) = (constPoint (pointMap σ a)).ofConv := rfl
  have e2 : ((constPoint a)⁻¹).ofConv.comp (σ : A →ₐ[k] A) =
      ((constPoint (pointMap σ a))⁻¹).ofConv := by
    change ((Algebra.ofId k A).comp a.ofConv).comp ((antipodeAlgHom k A).comp σ) =
      ((Algebra.ofId k A).comp (a.ofConv.comp σ)).comp (antipodeAlgHom k A)
    rw [← bialgHom_comp_antipode]
    rfl
  rw [e1, e2, AlgHom.id_comp, toConv_ofConv, toConv_ofConv]

theorem point_comp_twist (σ : A →ₐc[k] A) (x h : WithConv (A →ₐ[k] k)) :
    toConv (h.ofConv.comp ((σ : A →ₐ[k] A).comp (innerCo x))) = x * pointMap σ h * x⁻¹ := by
  rw [← AlgHom.comp_assoc]
  exact point_comp_innerCo (pointMap σ h) x

theorem twistNorm_succ (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k)) (n : ℕ) :
    ((List.range (n + 1)).map fun i => (pointMap σ)^[i] x).prod =
      x * pointMap σ ((List.range n).map fun i => (pointMap σ)^[i] x).prod := by
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, map_list_prod,
    List.map_map]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Function.iterate_succ_apply']

theorem twist_pow (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k)) (n : ℕ) :
    ((σ : A →ₐ[k] A).comp (innerCo x)) ^ n =
      ((σ : A →ₐ[k] A) ^ n).comp
        (innerCo ((List.range n).map fun i => (pointMap σ)^[i] x).prod) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, List.range_zero, List.map_nil, List.prod_nil, innerCo_one,
      AlgHom.comp_id]
  | succ n ih =>
    set P := ((List.range n).map fun i => (pointMap σ)^[i] x).prod with hP
    rw [pow_succ ((σ : A →ₐ[k] A).comp (innerCo x)), ih, twistNorm_succ, ← hP,
      ← innerCo_comp_innerCo, pow_succ (σ : A →ₐ[k] A), algHom_mul_eq_comp, algHom_mul_eq_comp,
      AlgHom.comp_assoc ((σ : A →ₐ[k] A) ^ n) (innerCo P),
      ← AlgHom.comp_assoc (innerCo P) (σ : A →ₐ[k] A) (innerCo x), innerCo_comp_bialgHom,
      AlgHom.comp_assoc (σ : A →ₐ[k] A) (innerCo (pointMap σ P)) (innerCo x),
      AlgHom.comp_assoc ((σ : A →ₐ[k] A) ^ n) (σ : A →ₐ[k] A)]

@[expose] def twistOrbitCo (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (toConv (AlgHom.id k A) * constPoint x * (toConv (σ : A →ₐ[k] A))⁻¹).ofConv

@[expose] def rightTransCo (a : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (toConv (AlgHom.id k A) * constPoint a).ofConv

theorem point_comp_twistOrbitCo (σ : A →ₐc[k] A) (x h : WithConv (A →ₐ[k] k)) :
    toConv (h.ofConv.comp (twistOrbitCo σ x)) = h * x * (pointMap σ h)⁻¹ := by
  unfold twistOrbitCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv,
    comp_convInv, point_comp_constPoint, ofConv_toConv, ofConv_toConv, AlgHom.comp_id]
  simp only [toConv_ofConv]
  rfl

theorem point_comp_rightTransCo (a h : WithConv (A →ₐ[k] k)) :
    toConv (h.ofConv.comp (rightTransCo a)) = h * a := by
  unfold rightTransCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, point_comp_constPoint, ofConv_toConv,
    AlgHom.comp_id]

theorem twistOrbitCo_comp_rightTransCo (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k)) :
    (twistOrbitCo σ x).comp (rightTransCo x⁻¹) =
      (toConv (AlgHom.id k A) * (toConv ((σ : A →ₐ[k] A).comp (innerCo x)))⁻¹).ofConv := by
  apply toConv_injective
  unfold rightTransCo
  rw [AlgHom.comp_convMul_distrib, toConv_ofConv, AlgHom.comp_id, comp_constPoint,
    toConv_ofConv]
  have e1 : toConv ((Algebra.ofId k A).comp (x⁻¹).ofConv) = (constPoint x)⁻¹ := rfl
  have e2 : (toConv ((σ : A →ₐ[k] A).comp (innerCo x)))⁻¹ =
      constPoint x * (toConv (σ : A →ₐ[k] A))⁻¹ * (constPoint x)⁻¹ := by
    rw [algHom_comp_innerCo]
    group
  rw [e1, toConv_ofConv, e2]
  unfold twistOrbitCo
  rw [toConv_ofConv]
  group

theorem counit_comp_twist (σ : A →ₐc[k] A) (x : WithConv (A →ₐ[k] k)) :
    (counitAlgHom k A).comp ((σ : A →ₐ[k] A).comp (innerCo x)) = counitAlgHom k A := by
  rw [← AlgHom.comp_assoc, BialgHom.counitAlgHom_comp, counit_comp_innerCo]

theorem convOne_ofConv_eq_counit : (1 : WithConv (A →ₐ[k] k)).ofConv = counitAlgHom k A := by
  rw [AlgHom.convOne_def, ofConv_toConv]
  ext x
  rfl

theorem exceptional_Lang_inner_twist_nilpotent_differential (σ : A →ₐc[k] A) {m : ℕ}
    (_hm : 1 ≤ m)
    (hS : ∀ D ∈ tangentSpace k A (counitAlgHom k A),
      D ∘ₗ ((σ : A →ₐ[k] A) ^ m).toLinearMap = 0)
    (x : WithConv (A →ₐ[k] k)) :
    (∀ h : WithConv (A →ₐ[k] k),
      toConv (h.ofConv.comp ((σ : A →ₐ[k] A).comp (innerCo x))) = x * pointMap σ h * x⁻¹) ∧
    ((σ : A →ₐ[k] A).comp (innerCo x)) ^ m =
      ((σ : A →ₐ[k] A) ^ m).comp
        (innerCo ((List.range m).map fun i => (pointMap σ)^[i] x).prod) ∧
    tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x) ^ m = 0 ∧
    ((1 : Module.End k (TangentSpace k A (counitAlgHom k A))) -
        tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x)) *
        (∑ i ∈ Finset.range m,
          tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x) ^ i) = 1 ∧
    (∑ i ∈ Finset.range m,
        tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x) ^ i) *
      ((1 : Module.End k (TangentSpace k A (counitAlgHom k A))) -
        tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x)) = 1 ∧
    (∀ h : WithConv (A →ₐ[k] k),
      toConv (h.ofConv.comp (twistOrbitCo σ x)) = h * x * (pointMap σ h)⁻¹) ∧
    (∀ h : WithConv (A →ₐ[k] k), toConv (h.ofConv.comp (rightTransCo x⁻¹)) = h * x⁻¹) ∧
    ∃ hR : (counitAlgHom k A).comp ((twistOrbitCo σ x).comp (rightTransCo x⁻¹)) =
        counitAlgHom k A,
      tangentMap ((twistOrbitCo σ x).comp (rightTransCo x⁻¹)) hR =
        (1 : Module.End k (TangentSpace k A (counitAlgHom k A))) -
          tangentMap ((σ : A →ₐ[k] A).comp (innerCo x)) (counit_comp_twist σ x) := by
  set t := (σ : A →ₐ[k] A).comp (innerCo x) with ht
  set N := tangentMap t (counit_comp_twist σ x) with hNdef
  have hNm : N ^ m = 0 := by
    obtain ⟨hn, e⟩ := tangentMap_pow t (counit_comp_twist σ x) m
    rw [e]
    ext D a
    have h1 : ((tangentMap (t ^ m) hn D : tangentSpace k A (counitAlgHom k A)) :
        A →ₗ[k] k) = 0 := by
      rw [coe_tangentMap, ht, twist_pow, AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc,
        hS D D.2, LinearMap.zero_comp]
    rw [h1]
    rfl
  have hinv : (counitAlgHom k A).comp (toConv t)⁻¹.ofConv = counitAlgHom k A := by
    change (counitAlgHom k A).comp (t.comp (antipodeAlgHom k A)) = _
    rw [← AlgHom.comp_assoc, counit_comp_twist, AlgHom.counitAlgHom_comp_antipodeAlgHom]
  have hR : (counitAlgHom k A).comp ((twistOrbitCo σ x).comp (rightTransCo x⁻¹)) =
      counitAlgHom k A := by
    have h1 := point_comp_rightTransCo x⁻¹
      (toConv ((1 : WithConv (A →ₐ[k] k)).ofConv.comp (twistOrbitCo σ x)))
    rw [ofConv_toConv, point_comp_twistOrbitCo, map_one, inv_one, mul_one, one_mul,
      mul_inv_cancel] at h1
    rw [← convOne_ofConv_eq_counit, ← AlgHom.comp_assoc]
    have h2 := congrArg ofConv h1
    simpa only [ofConv_toConv] using h2
  refine ⟨point_comp_twist σ x, twist_pow σ x m, hNm, ?_, ?_, point_comp_twistOrbitCo σ x,
    point_comp_rightTransCo x⁻¹, hR, ?_⟩
  · have h := mul_neg_geom_sum N m
    rw [hNm, sub_zero] at h
    exact h
  · have h := geom_sum_mul_neg N m
    rw [hNm, sub_zero] at h
    exact h
  · ext D a
    have h1 := tangent_convMul D.2 (AlgHom.id k A) (toConv t)⁻¹.ofConv
      (AlgHom.comp_id _) hinv
    rw [toConv_ofConv, tangent_convInv D.2 t (counit_comp_twist σ x)] at h1
    change ((D : A →ₗ[k] k) ∘ₗ ((twistOrbitCo σ x).comp (rightTransCo x⁻¹)).toLinearMap) a =
      (D : A →ₗ[k] k) a - ((D : A →ₗ[k] k) ∘ₗ t.toLinearMap) a
    rw [twistOrbitCo_comp_rightTransCo, h1]
    simp [sub_eq_add_neg]

end CFSG.LieType.AlgebraicGroups

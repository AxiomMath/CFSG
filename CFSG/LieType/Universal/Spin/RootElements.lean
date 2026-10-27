module

public import CFSG.LieType.Universal.Spin.Action
import TauCeti.LinearAlgebra.CliffordAlgebra.PBW

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

theorem ι_mul_ι_mem_spinGroup {y z : V} (h : Q y * Q z = 1) : ι Q y * ι Q z ∈ spinGroup Q := by
  have hy : IsUnit (Q y) := IsUnit.of_mul_eq_one _ h
  have hz : IsUnit (Q z) := IsUnit.of_mul_eq_one_right _ h
  let _ : Invertible (Q y) := hy.invertible
  let _ : Invertible (Q z) := hz.invertible
  have hstar : star (ι Q y * ι Q z) = ι Q z * ι Q y := by
    rw [star_mul, star_ι, star_ι, neg_mul_neg]
  refine spinGroup.mem_iff.mpr ⟨pinGroup.mem_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · refine Submonoid.mem_map.mpr ⟨unitι Q y * unitι Q z,
      mul_mem (unitι_mem_lipschitzGroup y) (unitι_mem_lipschitzGroup z), ?_⟩
    rw [Units.coeHom_apply, Units.val_mul, coe_unitι, coe_unitι]
  · refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
    · rw [hstar, mul_assoc, ← mul_assoc (ι Q y), ι_sq_scalar, Algebra.commutes, ← mul_assoc,
        ι_sq_scalar, ← map_mul, mul_comm (Q z), h, map_one]
    · rw [hstar, mul_assoc, ← mul_assoc (ι Q z), ι_sq_scalar, Algebra.commutes, ← mul_assoc,
        ι_sq_scalar, ← map_mul, h, map_one]
  · exact (Subalgebra.mem_toSubmodule (even Q)).mp
      (by rw [even_toSubmodule]; exact ι_mul_ι_mem_evenOdd_zero Q y z)

theorem one_add_ι_mul_ι_mem_spinGroup {u y : V} (hu : Q u = 0) (huy : polar Q u y = 0)
    (hy : IsUnit (Q y)) : 1 + ι Q y * ι Q u ∈ spinGroup Q := by
  have hy0 : Q y ≠ 0 := hy.ne_zero
  have hnorm : Q ((Q y)⁻¹ • y + u) = (Q y)⁻¹ := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, polar_comm, huy, hu,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero, add_zero]
    field_simp
  have heq : ι Q y * ι Q ((Q y)⁻¹ • y + u) = 1 + ι Q y * ι Q u := by
    rw [map_add, map_smul, mul_add, mul_smul_comm, ι_sq_scalar, Algebra.smul_def, ← map_mul,
      inv_mul_cancel₀ hy0, map_one]
  rw [← heq]
  exact ι_mul_ι_mem_spinGroup Q (by rw [hnorm, mul_inv_cancel₀ hy0])

theorem ι_mul_ι_mul_ι_eq_zero {u z : V} (hu : Q u = 0) (huz : polar Q u z = 0) :
    ι Q u * ι Q z * ι Q u = 0 := by
  rw [ι_mul_ι_mul_ι, huz, hu, zero_smul, zero_smul, sub_zero, map_zero]

theorem one_add_ι_mul_ι_mul_one_add_ι_mul_ι {u y z : V} (hu : Q u = 0) (huz : polar Q u z = 0) :
    (1 + ι Q y * ι Q u) * (1 + ι Q z * ι Q u) = 1 + ι Q (y + z) * ι Q u := by
  have h : ι Q y * ι Q u * (ι Q z * ι Q u) = 0 := by
    rw [mul_assoc, ← mul_assoc (ι Q u), ι_mul_ι_mul_ι_eq_zero Q hu huz, mul_zero]
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, h, add_zero, map_add, add_mul]
  abel

theorem one_add_smul_ι_mul_ι_mem_spinGroup {u w a : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hua : polar Q u a = 0) (hwa : polar Q w a = 0) (ha : IsUnit (Q a)) (c : K) :
    1 + c • (ι Q w * ι Q u) ∈ spinGroup Q := by
  have hcw : c • (ι Q w * ι Q u) = ι Q (c • w) * ι Q u := by rw [map_smul, smul_mul_assoc]
  have hucw : polar Q u (c • w) = 0 := by rw [polar_smul_right, huw, smul_zero]
  rw [hcw]
  by_cases hQ : Q (c • w) = 0
  · have h1 : IsUnit (Q (a + c • w)) := by
      rwa [QuadraticMap.map_add Q, hQ, add_zero, polar_smul_right, polar_comm, hwa, smul_zero,
        add_zero]
    have h2 : IsUnit (Q (-a)) := by rwa [QuadraticMap.map_neg Q]
    have hu1 : polar Q u (a + c • w) = 0 := by rw [polar_add_right, hua, hucw, add_zero]
    have hu2 : polar Q u (-a) = 0 := by rw [polar_neg_right, hua, neg_zero]
    have hprod := one_add_ι_mul_ι_mul_one_add_ι_mul_ι Q (y := a + c • w) hu hu2
    rw [add_neg_cancel_comm] at hprod
    rw [← hprod]
    exact mul_mem (one_add_ι_mul_ι_mem_spinGroup Q hu hu1 h1)
      (one_add_ι_mul_ι_mem_spinGroup Q hu hu2 h2)
  · exact one_add_ι_mul_ι_mem_spinGroup Q hu hucw (isUnit_iff_ne_zero.mpr hQ)

theorem one_add_smul_ι_mul_ι_mem_spinGroup_of_isUnit {u w : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hw : IsUnit (Q w)) (c : K) :
    1 + c • (ι Q w * ι Q u) ∈ spinGroup Q := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, add_zero]
    exact one_mem _
  · have hcw : c • (ι Q w * ι Q u) = ι Q (c • w) * ι Q u := by rw [map_smul, smul_mul_assoc]
    rw [hcw]
    refine one_add_ι_mul_ι_mem_spinGroup Q hu (by rw [polar_smul_right, huw, smul_zero]) ?_
    rw [QuadraticMap.map_smul, smul_eq_mul]
    exact (IsUnit.mul (isUnit_iff_ne_zero.mpr (mul_ne_zero hc hc)) hw)

theorem ι_mul_ι_mul_ι_mul_ι_eq_zero {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) :
    ι Q w * ι Q u * (ι Q w * ι Q u) = 0 := by
  rw [mul_assoc, ← mul_assoc (ι Q u), ι_mul_ι_mul_ι_eq_zero Q hu huw, mul_zero]

noncomputable def rootHom {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) :
    Multiplicative K →* spinGroup Q where
  toFun c := ⟨1 + c.toAdd • (ι Q w * ι Q u), hmem _⟩
  map_one' := Subtype.ext (by
    change 1 + (1 : Multiplicative K).toAdd • (ι Q w * ι Q u) = 1
    rw [toAdd_one, zero_smul, add_zero])
  map_mul' c d := Subtype.ext (by
    rw [Submonoid.coe_mul]
    change 1 + (c.toAdd + d.toAdd) • (ι Q w * ι Q u) =
      (1 + c.toAdd • (ι Q w * ι Q u)) * (1 + d.toAdd • (ι Q w * ι Q u))
    rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, smul_mul_smul_comm,
      ι_mul_ι_mul_ι_mul_ι_eq_zero Q hu huw, smul_zero, add_zero, add_smul]
    abel)

theorem coe_rootHom {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) (c : K) :
    (rootHom Q hu huw hmem (Multiplicative.ofAdd c) : CliffordAlgebra Q) =
      1 + c • (ι Q w * ι Q u) := by
  rw [rootHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

theorem ι_mul_ι_ne_zero {u w : V} (h : LinearIndependent K ![w, u]) : ι Q w * ι Q u ≠ 0 := by
  simpa [List.ofFn_succ] using CliffordAlgebra.prod_map_ι_ofFn_ne_zero Q ![w, u] h

theorem rootHom_injective {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) (h : LinearIndependent K ![w, u]) :
    Function.Injective (rootHom Q hu huw hmem) := by
  intro c d hcd
  have h1 := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hcd
  rw [← ofAdd_toAdd c, ← ofAdd_toAdd d, coe_rootHom, coe_rootHom] at h1
  have h2 : (c.toAdd - d.toAdd) • (ι Q w * ι Q u) = 0 := by
    rw [sub_smul, add_left_cancel h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact Multiplicative.toAdd.injective (sub_eq_zero.mp h3)
  · exact absurd h3 (ι_mul_ι_ne_zero Q h)

theorem spinAction_apply_eq_iff' (x : spinGroup Q) (v w : V) :
    spinAction Q x v = w ↔ (x : CliffordAlgebra Q) * ι Q v = ι Q w * x := by
  rw [spinAction_apply_eq_iff]
  constructor
  · intro h
    rw [← h, mul_assoc _ (↑x⁻¹ : CliffordAlgebra Q), coe_inv_mul_coe, mul_one]
  · intro h
    rw [h, mul_assoc, coe_mul_coe_inv, mul_one]

private theorem ι_mul_ι_mul_ι_eq (u w v : V) :
    ι Q w * ι Q u * ι Q v =
      polar Q v u • ι Q w - polar Q v w • ι Q u + ι Q v * (ι Q w * ι Q u) := by
  have hBX : ι Q u * ι Q v = algebraMap K _ (polar Q v u) - ι Q v * ι Q u := by
    rw [ι_mul_ι_comm, polar_comm]
  have hAX : ι Q w * ι Q v = algebraMap K _ (polar Q v w) - ι Q v * ι Q w := by
    rw [ι_mul_ι_comm, polar_comm]
  rw [mul_assoc, hBX, mul_sub, ← mul_assoc (ι Q w) (ι Q v) (ι Q u), hAX, sub_mul,
    ← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, mul_assoc]
  abel

theorem spinAction_apply_of_coe_eq {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    {x : spinGroup Q} (hx : (x : CliffordAlgebra Q) = 1 + ι Q w * ι Q u) (v : V) :
    spinAction Q x v = v + polar Q v u • w - polar Q v w • u - (Q w * polar Q v u) • u := by
  rw [spinAction_apply_eq_iff', hx]
  have hA : ι Q w * (ι Q w * ι Q u) = Q w • ι Q u := by
    rw [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def]
  have hB : ι Q u * (ι Q w * ι Q u) = 0 := by
    rw [← mul_assoc, ι_mul_ι_mul_ι_eq_zero Q hu huw]
  simp only [map_add, map_sub, map_smul, add_mul, sub_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, ι_mul_ι_mul_ι_eq Q u w v, hA, hB, smul_zero]
  module

theorem spinAction_rootHom {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0)
    (hmem : ∀ c : K, 1 + c • (ι Q w * ι Q u) ∈ spinGroup Q) (c : K) (v : V) :
    spinAction Q (rootHom Q hu huw hmem (Multiplicative.ofAdd c)) v =
      v + polar Q v u • (c • w) - polar Q v (c • w) • u - (Q (c • w) * polar Q v u) • u := by
  refine spinAction_apply_of_coe_eq Q hu (by rw [polar_smul_right, huw, smul_zero]) ?_ v
  rw [coe_rootHom, map_smul, smul_mul_assoc]

end CFSG.LieType.Universal.Spin

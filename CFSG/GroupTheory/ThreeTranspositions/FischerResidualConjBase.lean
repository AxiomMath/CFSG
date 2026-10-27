module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual

public section

namespace CFSG.GroupTheory.ThreeTranspositions

variable {X : Type} [Group X]

theorem map_conj_eq_of_normal {N : Subgroup X} (hN : N.Normal) (g : X) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hN.conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · have := hN.conj_mem x hx g⁻¹
      simpa using this
    · simp [MulAut.conj_apply, mul_assoc]

theorem threeResidualJoin_conj (g d : X) :
    threeResidualJoin (g * d * g⁻¹) =
      (threeResidualJoin d).map (MulAut.conj g).toMonoidHom := by
  unfold threeResidualJoin
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    map_conj_eq_of_normal (CFSG.GroupTheory.pResidualOf_normal (A := commutator X) inferInstance)]
  rfl

theorem threeResidualQuot_conj (g d : X) :
    threeResidualQuot (g * d * g⁻¹) =
      (threeResidualQuot d).map
        (MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X)).toMonoidHom := by
  unfold threeResidualQuot
  rw [threeResidualJoin_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

@[expose] noncomputable def threeResidualQuotConjEquiv (g d : X) :
    ↥(threeResidualQuot d) ≃* ↥(threeResidualQuot (g * d * g⁻¹)) :=
  ((MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X)).subgroupMap
    (threeResidualQuot d)).trans (MulEquiv.subgroupCongr (threeResidualQuot_conj g d).symm)

theorem coe_threeResidualQuotConjEquiv (g d : X) (y : ↥(threeResidualQuot d)) :
    (threeResidualQuotConjEquiv g d y : X ⧸ Subgroup.center X) =
      (QuotientGroup.mk g : X ⧸ Subgroup.center X) * (y : X ⧸ Subgroup.center X) *
        (QuotientGroup.mk g)⁻¹ :=
  rfl

theorem mem_threeResidualClass_conj_iff (g d : X) (y : ↥(threeResidualQuot d)) :
    threeResidualQuotConjEquiv g d y ∈ threeResidualClass (g * d * g⁻¹) ↔
      y ∈ threeResidualClass d := by
  have hjoin := threeResidualJoin_conj g d
  constructor
  · rintro ⟨w', hw', hw'y⟩
    rw [hjoin] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    refine ⟨w, hw, ?_⟩
    show (QuotientGroup.mk (w * d * w⁻¹) : X ⧸ Subgroup.center X) = y
    simp only [coe_threeResidualQuotConjEquiv, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at hw'y
    have e1 : g * w * g⁻¹ * (g * d * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * d * w⁻¹) * g⁻¹ := by
      group
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hw'y
    exact mul_left_cancel (mul_right_cancel hw'y)
  · rintro ⟨w, hw, hwy⟩
    refine ⟨g * w * g⁻¹, ?_, ?_⟩
    · rw [hjoin]
      exact ⟨w, hw, rfl⟩
    · show (QuotientGroup.mk (g * w * g⁻¹ * (g * d * g⁻¹) * (g * w * g⁻¹)⁻¹) :
        X ⧸ Subgroup.center X) = threeResidualQuotConjEquiv g d y
      rw [coe_threeResidualQuotConjEquiv, ← hwy]
      show (QuotientGroup.mk (g * w * g⁻¹ * (g * d * g⁻¹) * (g * w * g⁻¹)⁻¹) :
        X ⧸ Subgroup.center X) = QuotientGroup.mk g * QuotientGroup.mk (w * d * w⁻¹) *
          (QuotientGroup.mk g)⁻¹
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      group

theorem fischerCentralQuotientModel_conj {g d : X} {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing F] {H : Subgroup (GL ι F)} {T : Set (GL ι F)}
    (h : CFSG.Open.fischerCentralQuotientModel (threeResidualClass d) H T) :
    CFSG.Open.fischerCentralQuotientModel (threeResidualClass (g * d * g⁻¹)) H T := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(threeResidualQuotConjEquiv g d).symm.trans φ, fun y => ?_⟩
  have := hφ ((threeResidualQuotConjEquiv g d).symm y)
  rw [← mem_threeResidualClass_conj_iff g d, MulEquiv.apply_symm_apply] at this
  rw [this]
  rfl

end CFSG.GroupTheory.ThreeTranspositions

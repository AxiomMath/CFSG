module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2Omega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

@[expose] def sl2f3NegOne : SL2F3 := ⟨-1, by rw [Matrix.det_neg, Matrix.det_one]; decide⟩

theorem coe_sl2f3NegOne : ((sl2f3NegOne : SL2F3) : Mat2) = -1 := rfl

theorem sl2f3NegOne_mul_self : sl2f3NegOne * sl2f3NegOne = 1 := by decide +kernel

@[expose] def q8SL : Subgroup SL2F3 where
  carrier := {A | A ^ 4 = 1}
  mul_mem' := by
    have key : ∀ a b : SL2F3, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by decide +kernel
    intro a b ha hb
    exact key a b ha hb
  one_mem' := one_pow 4
  inv_mem' := by
    intro a ha
    change a ^ 4 = 1 at ha
    change a⁻¹ ^ 4 = 1
    rw [inv_pow, ha, inv_one]

theorem mem_q8SL_iff (A : SL2F3) : A ∈ q8SL ↔ A ^ 4 = 1 := Iff.rfl

theorem q8SL_normal : q8SL.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_q8SL_iff] at hn ⊢
  rw [conj_pow, hn, mul_one, mul_inv_cancel]

theorem mem_q8SL_of_mul_self {A : SL2F3} (h : A * A = sl2f3NegOne) : A ∈ q8SL := by
  rw [mem_q8SL_iff, show A ^ 4 = (A * A) * (A * A) by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two], h, sl2f3NegOne_mul_self]

theorem rightMulHom_injective : Function.Injective rightMulHom := by
  intro A B h
  have h1 := rightMulHom_apply A 1
  rw [h, rightMulHom_apply B 1] at h1
  simp only [Matrix.one_mul] at h1
  exact inv_injective (Subtype.ext h1.symm)

theorem rightMulHom_sl2f3NegOne : rightMulHom sl2f3NegOne = piOrth detForm := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [coe_piOrth_apply]
  have hinv : ((sl2f3NegOne⁻¹ : SL2F3) : Mat2) = -1 := by
    rw [inv_eq_of_mul_eq_one_right sl2f3NegOne_mul_self]
    rfl
  change X * ((sl2f3NegOne⁻¹ : SL2F3) : Mat2) = -X
  rw [hinv, Matrix.mul_neg, Matrix.mul_one]

theorem rightMulHom_range_normal :
    (rightMulHom.range.subgroupOf (omegaGroup detForm_nondegenerate)).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨C, hC⟩ := hx
  have hg : (g : OGroup detForm) ∈ detPhi.range := by
    rw [range_detPhi]
    exact g.2
  obtain ⟨⟨A, B⟩, hAB⟩ := hg
  refine ⟨B * C * B⁻¹, ?_⟩
  have hc : leftMulHom A * (rightMulHom B * rightMulHom C * (rightMulHom B)⁻¹) =
      (rightMulHom B * rightMulHom C * (rightMulHom B)⁻¹) * leftMulHom A := by
    have := leftMulHom_mul_rightMulHom_comm A (B * C * B⁻¹)
    simpa only [map_mul, map_inv] using this
  change rightMulHom (B * C * B⁻¹) =
    (g : OGroup detForm) * (x : OGroup detForm) * (g : OGroup detForm)⁻¹
  rw [← hAB, ← hC, detPhi_apply]
  simp only [map_mul, map_inv]
  calc rightMulHom B * rightMulHom C * (rightMulHom B)⁻¹
      = leftMulHom A * (rightMulHom B * rightMulHom C * (rightMulHom B)⁻¹) *
          (leftMulHom A)⁻¹ := by rw [hc]; group
    _ = _ := by group

theorem leftRight_apply (A B : SL2F3) (X : Mat2) :
    ((leftMulHom A * rightMulHom B : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X =
      (A : Mat2) * (X * ((B⁻¹ : SL2F3) : Mat2)) := rfl

theorem exists_fixing_pair (X : Mat2) (hX : X.det ≠ 0) :
    ∃ A B : SL2F3, A * A = sl2f3NegOne ∧ B * B = sl2f3NegOne ∧
      (A : Mat2) * (X * ((B⁻¹ : SL2F3) : Mat2)) = X := by
  revert X
  decide +kernel

theorem exists_moving (A B : SL2F3) (hA : A * A = sl2f3NegOne) (hB : B * B = sl2f3NegOne) :
    (∃ X : Mat2, (A : Mat2) * (X * ((B⁻¹ : SL2F3) : Mat2)) ≠ X) ∧
      ∃ X : Mat2, (A : Mat2) * (X * ((B⁻¹ : SL2F3) : Mat2)) ≠ -X := by
  revert A B
  decide +kernel

theorem leftRight_ne_one {A B : SL2F3} (hA : A * A = sl2f3NegOne) (hB : B * B = sl2f3NegOne) :
    leftMulHom A * rightMulHom B ≠ 1 := by
  intro h
  obtain ⟨X, hX⟩ := (exists_moving A B hA hB).1
  apply hX
  have := congrArg (fun g : OGroup detForm => (g : Mat2 ≃ₗ[ZMod 3] Mat2) X) h
  exact this

theorem leftRight_ne_piOrth {A B : SL2F3} (hA : A * A = sl2f3NegOne)
    (hB : B * B = sl2f3NegOne) : leftMulHom A * rightMulHom B ≠ piOrth detForm := by
  intro h
  obtain ⟨X, hX⟩ := (exists_moving A B hA hB).2
  apply hX
  have := congrArg (fun g : OGroup detForm => (g : Mat2 ≃ₗ[ZMod 3] Mat2) X) h
  rw [coe_piOrth_apply] at this
  exact this

theorem exists_det_eq : ∀ c : ZMod 3, ∃ X : Mat2, detForm X = c := by
  intro c
  refine ⟨!![c, 0; 0, 1], ?_⟩
  rw [detForm_apply, Matrix.det_fin_two_of]
  ring

end CFSG.OddStandard.SmallF3.Omega

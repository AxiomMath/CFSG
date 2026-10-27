module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary

theorem σ9_σ9 (z : F9) : σ9 (σ9 z) = z := by
  apply QuadraticAlgebra.ext
  · rw [σ9_re, σ9_re]
  · rw [σ9_im, σ9_im, neg_neg]

theorem σ9_smul (c : ZMod 3) (z : F9) : σ9 (c • z) = c • σ9 z := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_smul, σ9_re]
  · simp only [QuadraticAlgebra.im_smul, σ9_im, smul_eq_mul, mul_neg]

@[expose] noncomputable def conjTwoLin : (Fin 4 → F9) →ₗ[ZMod 3] (Fin 4 → F9) where
  toFun x := fun i => if i.val < 2 then σ9 (x i) else x i
  map_add' x y := by
    funext i
    by_cases h : i.val < 2
    · simp only [Pi.add_apply, if_pos h, map_add]
    · simp only [Pi.add_apply, if_neg h]
  map_smul' c x := by
    funext i
    by_cases h : i.val < 2
    · simp only [Pi.smul_apply, if_pos h, σ9_smul, RingHom.id_apply]
    · simp only [Pi.smul_apply, if_neg h, RingHom.id_apply]

theorem conjTwoLin_apply (x : Fin 4 → F9) (i : Fin 4) :
    conjTwoLin x i = if i.val < 2 then σ9 (x i) else x i := rfl

theorem conjTwoLin_conjTwoLin (x : Fin 4 → F9) : conjTwoLin (conjTwoLin x) = x := by
  funext i
  by_cases h : i.val < 2
  · simp only [conjTwoLin_apply, if_pos h, σ9_σ9]
  · simp only [conjTwoLin_apply, if_neg h]

@[expose] noncomputable def conjTwoEquiv : (Fin 4 → F9) ≃ₗ[ZMod 3] (Fin 4 → F9) :=
  LinearEquiv.ofLinear conjTwoLin conjTwoLin (LinearMap.ext conjTwoLin_conjTwoLin)
    (LinearMap.ext conjTwoLin_conjTwoLin)

theorem conjTwoLin_isometry (x : Fin 4 → F9) : hermForm 4 (conjTwoLin x) = hermForm 4 x := by
  rw [hermForm_apply, hermForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.val < 2
  · simp only [conjTwoLin_apply, if_pos h, σ9_re, σ9_im]
    ring
  · simp only [conjTwoLin_apply, if_neg h]

@[expose] noncomputable def conjTwo : OGroup (hermForm 4) :=
  ⟨conjTwoEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr conjTwoLin_isometry⟩

theorem coe_conjTwo (x : Fin 4 → F9) (i : Fin 4) :
    ((conjTwo : OGroup (hermForm 4)) : (Fin 4 → F9) ≃ₗ[ZMod 3] (Fin 4 → F9)) x i =
      if i.val < 2 then σ9 (x i) else x i := rfl

theorem conjTwo_mul_self : conjTwo * conjTwo = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact conjTwoLin_conjTwoLin x

theorem conjTwo_inv : conjTwo⁻¹ = conjTwo := inv_eq_of_mul_eq_one_left conjTwo_mul_self

theorem conjTwo_mul_omega : conjTwo * omegaOrth 4 * conjTwo⁻¹ =
    suToOrth (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4)) * omegaOrth 4 := by
  rw [conjTwo_inv]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  have hu : suMat (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4)) = Matrix.diagonal
      (fun a : Fin 4 => if 0 ≤ a.val ∧ a.val < 0 + 2 then (-1 : F9) else 1) := by
    rw [suMat_rootInvSU, negBlock_eq_diagonal]
  change conjTwoLin (omega9 • conjTwoLin x) i =
    (suMat (rootInvSU F9 3 1 (by norm_num : 2 ≤ 4)) *ᵥ (omega9 • x)) i
  rw [hu, Matrix.mulVec_diagonal]
  by_cases h : i.val < 2
  · have hc : 0 ≤ i.val ∧ i.val < 0 + 2 := ⟨Nat.zero_le _, h⟩
    simp only [conjTwoLin_apply, if_pos h, if_pos hc, Pi.smul_apply, smul_eq_mul, map_mul, σ9_σ9,
      σ9_omega]
    ring
  · have hc : ¬ (0 ≤ i.val ∧ i.val < 0 + 2) := fun hh => h hh.2
    simp only [conjTwoLin_apply, if_neg h, if_neg hc, Pi.smul_apply, smul_eq_mul, one_mul]

theorem hermForm_single_omega (j : Fin 4) : hermForm 4 (Pi.single j omega9) = 1 := by
  rw [hermForm_apply, Finset.sum_eq_single j]
  · simp [omega9]
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem reflection_single_omega (j : Fin 4) [Invertible (hermForm 4 (Pi.single j omega9))]
    (x : Fin 4 → F9) :
    TauCeti.QuadraticMap.reflection (hermForm 4) (Pi.single j omega9) x =
      fun i => if i = j then σ9 (x i) else x i := by
  have hp : QuadraticMap.polar (hermForm 4) (Pi.single j omega9) x = -(x j).im := by
    rw [polar_hermForm, herm9_re, Finset.sum_eq_single j]
    · simp [omega9]
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · intro h
      exact absurd (Finset.mem_univ j) h
  rw [TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, hermForm_single_omega, inv_one,
    one_mul, hp]
  funext i
  by_cases hi : i = j
  · subst hi
    have h3 : (3 : ZMod 3) = 0 := by decide
    apply QuadraticAlgebra.ext
    · simp only [if_true, σ9_re, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
        QuadraticAlgebra.re_sub, QuadraticAlgebra.re_smul, smul_eq_mul, omega9,
        QuadraticAlgebra.re_omega]
      ring
    · simp only [if_true, σ9_im, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
        QuadraticAlgebra.im_sub, QuadraticAlgebra.im_smul, smul_eq_mul, omega9,
        QuadraticAlgebra.im_omega]
      linear_combination (x i).im * h3
  · simp only [if_neg hi, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero,
      sub_zero]

theorem conjTwo_eq_mul_reflections (h0 : Invertible (hermForm 4 (Pi.single (0 : Fin 4) omega9)))
    (h1 : Invertible (hermForm 4 (Pi.single (1 : Fin 4) omega9))) :
    conjTwo = TauCeti.QuadraticMap.reflectionOrthogonal (hermForm 4) (Pi.single 0 omega9) *
      TauCeti.QuadraticMap.reflectionOrthogonal (hermForm 4) (Pi.single 1 omega9) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  rw [coe_conjTwo, Subgroup.coe_mul, LinearEquiv.mul_apply,
    TauCeti.QuadraticMap.coe_reflectionOrthogonal, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    reflection_single_omega 0, reflection_single_omega 1]
  fin_cases i
  · simp
  · simp
  · simp
  · simp

theorem conjTwo_mem_omega : conjTwo ∈ omegaGroup (hermForm_nondegenerate 4) := by
  letI i0 : Invertible (hermForm 4 (Pi.single (0 : Fin 4) omega9)) :=
    invertibleOfNonzero (by rw [hermForm_single_omega]; exact one_ne_zero)
  letI i1 : Invertible (hermForm 4 (Pi.single (1 : Fin 4) omega9)) :=
    invertibleOfNonzero (by rw [hermForm_single_omega]; exact one_ne_zero)
  have hu : ∀ (j : Fin 4) (_ : Invertible (hermForm 4 (Pi.single j omega9))),
      unitOfInvertible (hermForm 4 (Pi.single j omega9)) = (1 : (ZMod 3)ˣ) := fun j _ =>
    Units.ext (by rw [val_unitOfInvertible, hermForm_single_omega]; rfl)
  rw [conjTwo_eq_mul_reflections i0 i1, mem_omegaGroup_iff, map_mul,
    CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
    CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal, hu 0 i0, hu 1 i1, map_one]
  exact Prod.ext (by decide) (mul_one 1)

end CFSG.OddStandard.SmallF3.Omega

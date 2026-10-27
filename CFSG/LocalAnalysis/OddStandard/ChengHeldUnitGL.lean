module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2GL

public section

namespace CFSG.OddStandard.ChengHeld

namespace GL32Inv

private abbrev RawV := Fin 3 → ZMod 2

private abbrev RawM := Matrix (Fin 3) (Fin 3) (ZMod 2)

private def rawVectors : List RawV :=
  [![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1],
    ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

private def rawApply (A : RawM) (x : RawV) : RawV :=
  fun i => A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2

private def rawMul (A B : RawM) : RawM :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

private def rawDet (A : RawM) : ZMod 2 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
    - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
    + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

private def rawN (A : RawM) (x : RawV) : RawV :=
  rawApply A x + x

private def rawW (A : RawM) : RawV :=
  (rawVectors.find? fun w => decide (rawN A w ≠ 0)).getD 0

private def rawU (A : RawM) : RawV :=
  rawN A (rawW A)

private def rawFixedVector (A : RawM) : RawV :=
  (rawVectors.find? fun v => decide (rawApply A v = v ∧ v ≠ 0 ∧ v ≠ rawU A)).getD 0

private def rawConjugator (A : RawM) : RawM :=
  fun i j => ![rawU A, rawW A, rawFixedVector A] j i

private def rawTransvection : RawM :=
  !![(1 : ZMod 2), 1, 0; 0, 1, 0; 0, 0, 1]

private abbrev RawProperty (A : RawM) : Prop :=
  A = 1 ∨ rawMul A A ≠ 1 ∨ rawDet A = 0 ∨
    rawDet (rawConjugator A) ≠ 0 ∧
      rawMul A (rawConjugator A) = rawMul (rawConjugator A) rawTransvection

private theorem raw_check_entries (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ZMod 2) :
    RawProperty !![a00, a01, a02; a10, a11, a12; a20, a21, a22] := by
  revert a00 a01 a02 a10 a11 a12 a20 a21 a22
  decide

private theorem raw_check (A : RawM) : RawProperty A := by
  have hA : A = !![A 0 0, A 0 1, A 0 2; A 1 0, A 1 1, A 1 2; A 2 0, A 2 1, A 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact hA.symm ▸ raw_check_entries (A 0 0) (A 0 1) (A 0 2) (A 1 0) (A 1 1) (A 1 2)
    (A 2 0) (A 2 1) (A 2 2)

private theorem rawMul_eq (A B : RawM) : rawMul A B = A * B := by
  ext i j
  simp [rawMul, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

private theorem rawDet_eq (A : RawM) : rawDet A = Matrix.det A := by
  rw [Matrix.det_fin_three]
  rfl

private def transvectionGL : GL (Fin 3) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero rawTransvection (by decide)

private theorem GL3_involution_conjugate_transvection (a : GL (Fin 3) (ZMod 2)) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : ∃ c : GL (Fin 3) (ZMod 2), c⁻¹ * a * c = transvectionGL := by
  let A : RawM := a
  have hA1 : A ≠ 1 := fun h => ha1 (Units.ext h)
  have hA2 : rawMul A A = 1 := by
    rw [rawMul_eq]
    simpa [A] using congrArg Units.val ha2
  have hAdet : rawDet A ≠ 0 := by
    rw [rawDet_eq]
    exact Matrix.GeneralLinearGroup.det_ne_zero a
  rcases raw_check A with h | h | h | ⟨hdetC, hAC⟩
  · exact (hA1 h).elim
  · exact (h hA2).elim
  · exact (hAdet h).elim
  let c : GL (Fin 3) (ZMod 2) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (rawConjugator A) (by
      simpa [← rawDet_eq] using hdetC)
  refine ⟨c, ?_⟩
  apply Units.ext
  change (↑(c⁻¹) : RawM) * A * rawConjugator A = rawTransvection
  rw [mul_assoc, ← rawMul_eq A (rawConjugator A), hAC, rawMul_eq]
  change (↑(c⁻¹) : RawM) * (rawConjugator A * rawTransvection) = rawTransvection
  rw [← mul_assoc]
  change (↑(c⁻¹) : RawM) * (c : RawM) * rawTransvection = rawTransvection
  rw [Units.inv_mul]
  simp

theorem GL3_involutions_conjugate (a b : GL (Fin 3) (ZMod 2)) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hb1 : b ≠ 1) (hb2 : b * b = 1) : ∃ c : GL (Fin 3) (ZMod 2), c⁻¹ * a * c = b := by
  obtain ⟨ca, hca⟩ := GL3_involution_conjugate_transvection a ha1 ha2
  obtain ⟨cb, hcb⟩ := GL3_involution_conjugate_transvection b hb1 hb2
  refine ⟨ca * cb⁻¹, ?_⟩
  calc (ca * cb⁻¹)⁻¹ * a * (ca * cb⁻¹) = cb * (ca⁻¹ * a * ca) * cb⁻¹ := by group
    _ = cb * transvectionGL * cb⁻¹ := by rw [hca]
    _ = cb * (cb⁻¹ * b * cb) * cb⁻¹ := by rw [hcb]
    _ = b := by group

theorem mulAut_mulEquiv_GL3 {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) : Nonempty (MulAut V ≃* GL (Fin 3) (ZMod 2)) := by
  classical
  let _ : CommGroup V := GL32Aux.commGroupOfMulSelf h2
  let Q := Additive V
  let _ : AddCommGroup Q := Additive.addCommGroup
  let _ : Module (ZMod 2) Q := AddCommGroup.zmodModule (GL32Aux.two_nsmul_eq_zero h2)
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : Finite Q := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) Q := Module.Finite.of_finite
  let eAdd : MulAut V ≃* Multiplicative (AddAut Q) :=
    (AddAutAdditive V).toMultiplicative.symm
  let eAddLin : Multiplicative (AddAut Q) ≃* (Q ≃ₗ[ZMod 2] Q) :=
    { toFun := fun a =>
        (a : AddAut Q).toLinearEquiv (fun c x => by
          change (a : AddAut Q).toAddMonoidHom (c • x) =
            c • (a : AddAut Q).toAddMonoidHom x
          exact ZMod.map_smul (a : AddAut Q).toAddMonoidHom c x)
      invFun := fun a => Multiplicative.ofAdd a.toAddEquiv
      left_inv := by
        intro a
        apply Multiplicative.toAdd.injective
        ext x
        rfl
      right_inv := by
        intro a
        ext x
        rfl
      map_mul' := by
        intro a b
        ext x
        rfl }
  let eLin : MulAut V ≃* LinearMap.GeneralLinearGroup (ZMod 2) Q :=
    (eAdd.trans eAddLin).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Q).symm
  have hfin : Module.finrank (ZMod 2) Q = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Q)
    rw [Nat.card_zmod, show Nat.card Q = 8 from hcard] at h
    have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    exact (Nat.pow_right_injective (le_refl 2) (h8.trans h)).symm
  let basis : Module.Basis (Fin 3) (ZMod 2) Q := Module.finBasisOfFinrankEq _ _ hfin
  exact ⟨eLin.trans (Matrix.GeneralLinearGroup.toLin' basis).symm⟩

end GL32Inv

theorem mulAut_involutions_conj {V : Type} [Group V] (hcard : Nat.card V = 8)
    (h2 : ∀ v : V, v * v = 1) {a b : MulAut V} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : IsConj a b := by
  obtain ⟨e⟩ := GL32Inv.mulAut_mulEquiv_GL3 hcard h2
  have hea1 : e a ≠ 1 := by simpa using ha1
  have hea2 : e a * e a = 1 := by rw [← map_mul, ha, map_one]
  have heb1 : e b ≠ 1 := by simpa using hb1
  have heb2 : e b * e b = 1 := by rw [← map_mul, hb, map_one]
  obtain ⟨c, hc⟩ := GL32Inv.GL3_involutions_conjugate (e a) (e b) hea1 hea2 heb1 heb2
  refine isConj_iff.2 ⟨e.symm c⁻¹, ?_⟩
  apply e.injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv]
  exact hc

end CFSG.OddStandard.ChengHeld

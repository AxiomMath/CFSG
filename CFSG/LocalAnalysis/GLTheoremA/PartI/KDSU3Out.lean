module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Open Matrix

variable {n : ℕ} {K : Type} [Field K]

private theorem caseB_two_pow_mod_nine (hodd : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5 := by
  obtain ⟨m, hm⟩ : ∃ m, n = 6 * m + 1 ∨ n = 6 * m + 5 := ⟨n / 6, by omega⟩
  have h64 : (2 ^ 6) ^ m % 9 = 1 := by
    rw [Nat.pow_mod]; norm_num
  rcases hm with rfl | rfl
  · left
    rw [pow_add, pow_mul, Nat.mul_mod, h64]
    norm_num
  · right
    rw [pow_add, pow_mul, Nat.mul_mod, h64]
    norm_num

private theorem caseB_not_nine_dvd_card_GL_three {q : ℕ} (hq : q % 9 = 2 ∨ q % 9 = 5) :
    ¬ 9 ∣ ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ)) := by
  have hq1 : 1 ≤ q := by omega
  have e1 : q ^ 0 ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  have e2 : q ^ 1 ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  have e3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  rw [Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [← ZMod.natCast_eq_zero_iff]
  have hx : (q : ZMod 9) = 2 ∨ (q : ZMod 9) = 5 := by
    have : (q : ZMod 9) = ((q % 9 : ℕ) : ZMod 9) := (ZMod.natCast_mod q 9).symm
    rcases hq with hq | hq <;> rw [this, hq] <;> simp
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub e1, Nat.cast_sub e2, Nat.cast_sub e3]
  push_cast
  rcases hx with hx | hx <;> rw [hx] <;> decide

private theorem caseB_sq_eq_one_charTwo [CharP K 2] {x : K} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (x - 1) ^ 2 = 0 := by
    linear_combination hx + (1 - x) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

private theorem caseB_exists_fixed_rep (h : UnitaryFieldData 2 n K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = h.bar x)
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hA : primeFormConjHom h _ (primeFormFieldU h isPrimeFormGram_one σ A) =
      primeFormConjHom h _ A) :
    ∃ A' : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      primeFormConjHom h _ A' = primeFormConjHom h _ A ∧
        primeFormFieldU h isPrimeFormGram_one σ A' = A' := by
  have : CharP K 2 := h.charP
  have := h.finite
  have h3 : primeFormPsi h isPrimeFormGram_one
      ⟨A⁻¹ * primeFormFieldU h isPrimeFormGram_one σ A, RingEquiv.refl K⟩ = 1 := by
    rw [primeFormPsi_apply, map_mul, hA, map_inv, inv_mul_cancel, one_mul]
    exact map_one (primeFormFieldHom h isPrimeFormGram_one)
  obtain ⟨-, c, hcN, hc⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (le_refl 3) _).mp h3
  have hAbar : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar =
      (c : K) • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e2 : (A : GL (Fin 3) K)⁻¹ * glAut σ (A : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c := hc
    have e1 : glAut σ (A : GL (Fin 3) K) =
        (A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← e2, mul_inv_cancel_left]
    have e3 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) e1
    simp only [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar] at e3
    have hmap : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar :=
      Matrix.ext fun i j => hσ _
    rw [← hmap, e3, Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c : K)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact Units.ne_zero _ hb
  have hbN : h.norm b = 1 := by
    refine caseB_sq_eq_one_charTwo ?_
    rw [sq, ← norm_mul_eq h, ← hb, hcN]
  have huU : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b hb0) ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul,
      Units.val_mk0, hbN, one_smul]
  refine ⟨⟨_, huU⟩ * A, ?_, ?_⟩
  · have hu1 : primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ⟨_, huU⟩ =
        1 := by
      have h5 := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (le_refl 3)
        ⟨⟨_, huU⟩, RingEquiv.refl K⟩).mpr ⟨rfl, Units.mk0 b hb0, hbN, rfl⟩
      rwa [primeFormPsi_apply, show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one,
        mul_one] at h5
    rw [map_mul, hu1, one_mul]
  · have hm : ((((⟨_, huU⟩ * A : primeFormUnitary h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
          b • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Subgroup.coe_mul, Units.val_mul]
      change ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b hb0) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * _ = _
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
        Matrix.smul_mul, Matrix.one_mul, Units.val_mk0]
    refine Subtype.ext (Units.ext ?_)
    change ((((⟨_, huU⟩ * A : primeFormUnitary h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).map σ = _
    rw [hm]
    ext i j
    have := congrFun (congrFun hAbar i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hσ] at this ⊢
    have hbN' : b * h.bar b = 1 := hbN
    rw [this, ← mul_assoc, hb]
    linear_combination (b * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) * hbN'

private theorem caseB_mem_range_map_subtype (h : UnitaryFieldData 2 n K) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = h.bar x) {A : GL (Fin 3) K} (hA : glAut σ A = A) :
    A ∈ (GeneralLinearGroup.map h.fixedField.subtype).range := by
  have hA' : glAut σ A⁻¹ = A⁻¹ := by rw [map_inv, hA]
  have hm : ∀ B : GL (Fin 3) K, glAut σ B = B →
      ∀ i j, (B : Matrix (Fin 3) (Fin 3) K) i j ∈ h.fixedField := by
    intro B hB i j
    have e := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) hB
    rw [UnitaryFieldData.mem_fixedField, ← hσ]
    exact e
  have hinj : Function.Injective fun N : Matrix (Fin 3) (Fin 3) h.fixedField =>
      N.map h.fixedField.subtype := Matrix.map_injective Subtype.val_injective
  let M : Matrix (Fin 3) (Fin 3) h.fixedField :=
    Matrix.of fun i j => ⟨(A : Matrix (Fin 3) (Fin 3) K) i j, hm A hA i j⟩
  let M' : Matrix (Fin 3) (Fin 3) h.fixedField :=
    Matrix.of fun i j => ⟨((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j, hm _ hA' i j⟩
  have hMA : M.map h.fixedField.subtype = (A : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.ext fun _ _ => rfl
  have hMA' : M'.map h.fixedField.subtype = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.ext fun _ _ => rfl
  refine ⟨⟨M, M', hinj ?_, hinj ?_⟩, Units.ext hMA⟩
  · simp only [Matrix.map_mul, hMA, hMA', Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · simp only [Matrix.map_mul, hMA, hMA', Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem caseB_core (h : UnitaryFieldData 2 n K) (hodd : n % 2 = 1) (h1 : 1 < n)
    (h3 : n % 3 ≠ 0) (E : Subgroup (MulAut (pI h))) (hE : IsPGroup 3 E)
    (hcomm : ∀ e ∈ E,
      e * primeFormFieldAut h isPrimeFormGram_one
          (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h).conj =
        primeFormFieldAut h isPrimeFormGram_one
          (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h).conj * e) :
    Nat.card E ≤ 3 := by
  have hKfin : Finite K := h.finite
  set σ := (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h).conj
    with hσdef
  have hσ : ∀ x, σ x = h.bar x :=
    CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm_conj h
  have hED := le_primeFormD_of_isPGroup_three h h1 h3 E hE
  let Fix : Subgroup (GL (Fin 3) K) :=
    MonoidHom.eqLocus (glAut σ).toMonoidHom (MonoidHom.id _)
  let O : Subgroup (primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Fix.subgroupOf _
  have hEO : E ≤ O.map (primeFormConjHom h _) := by
    intro e he
    obtain ⟨A, rfl⟩ := hED he
    have hc := hcomm _ he
    have hA : primeFormConjHom h _ (primeFormFieldU h isPrimeFormGram_one σ A) =
        primeFormConjHom h _ A := by
      rw [← primeFormField_conj_eq h isPrimeFormGram_one σ A]
      have : primeFormFieldHom h isPrimeFormGram_one σ * primeFormConjHom h _ A =
          primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one σ := hc.symm
      rw [this, mul_inv_cancel_right]
    obtain ⟨A', hA'1, hA'2⟩ := caseB_exists_fixed_rep h hσ A hA
    refine ⟨A', ?_, hA'1⟩
    show glAut σ (A' : GL (Fin 3) K) = A'
    exact congrArg Subtype.val hA'2
  have hFixR : Fix ≤ (GeneralLinearGroup.map h.fixedField.subtype).range :=
    fun A hA => caseB_mem_range_map_subtype h hσ hA
  have hinj : Function.Injective (GeneralLinearGroup.map h.fixedField.subtype
      : GL (Fin 3) h.fixedField →* GL (Fin 3) K) := fun g₁ g₂ hg =>
    Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val hg))
  have hdvd1 : Nat.card E ∣ Nat.card O :=
    (Subgroup.card_dvd_of_le hEO).trans (Subgroup.card_map_dvd _ _)
  have hdvd2 : Nat.card O ∣ Nat.card (GL (Fin 3) h.fixedField) := by
    have e1 : Nat.card O = Nat.card (O.map (primeFormUnitary h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)).subtype) :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
    have e2 : O.map (primeFormUnitary h ((1 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)).subtype ≤
        (GeneralLinearGroup.map h.fixedField.subtype).range := by
      rintro _ ⟨A, hA, rfl⟩
      exact hFixR hA
    have e3 : Nat.card ((GeneralLinearGroup.map h.fixedField.subtype :
        GL (Fin 3) h.fixedField →* GL (Fin 3) K).range) =
        Nat.card (GL (Fin 3) h.fixedField) :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [e1, ← e3]
    exact Subgroup.card_dvd_of_le e2
  have hFfin : Finite h.fixedField := inferInstance
  letI : Fintype h.fixedField := Fintype.ofFinite _
  have hq : Fintype.card h.fixedField = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, h.card_fixedField]
  have hGL : Nat.card (GL (Fin 3) h.fixedField) =
      ∏ i : Fin 3, ((2 ^ n) ^ 3 - (2 ^ n) ^ (i : ℕ)) := by
    rw [Matrix.card_GL_field, hq]
  have hN : ¬ 9 ∣ Nat.card (GL (Fin 3) h.fixedField) := by
    rw [hGL]
    exact caseB_not_nine_dvd_card_GL_three (caseB_two_pow_mod_nine hodd h3)
  exact card_le_three_of_isPGroup_dvd hE hN (hdvd1.trans hdvd2)

end CFSG.LocalAnalysis.GLTheoremA

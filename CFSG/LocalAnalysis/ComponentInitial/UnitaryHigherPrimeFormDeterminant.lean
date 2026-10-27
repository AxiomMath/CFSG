module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneUnitaryNorm
public import CFSG.GH74.Generic.BProg.B2.T4OutCore
public import CFSG.GroupTheory.CyclicSubgroup.PowerCriterion

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

variable {F : Type} [Field F] {n p f : ℕ}

theorem scalar_mul_mem_gramSU_of_det_eq_pow (h : UnitaryFieldData p f F)
    (y : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (b : F)
    (hb : b ≠ 0) (hN : h.norm b = 1)
    (hdet : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = b ^ n) :
    GeneralLinearGroup.scalar (Fin n) (Units.mk0 b⁻¹ (inv_ne_zero hb)) * (y : GL (Fin n) F) ∈
      gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  have hm : ((GeneralLinearGroup.scalar (Fin n) (Units.mk0 b⁻¹ (inv_ne_zero hb)) *
      (y : GL (Fin n) F) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      b⁻¹ • ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hy := mem_primeFormUnitary.mp y.2
  have hbb : h.bar b⁻¹ * b⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm]
    have : b * h.bar b = 1 := hN
    rw [this, inv_one]
  refine ⟨?_, ?_⟩
  · rw [hm, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm b⁻¹, hbb, one_smul]
    exact hy
  · rw [hm, Matrix.det_smul, hdet]
    simp [inv_mul_cancel₀ (pow_ne_zero n hb)]

theorem exists_normOne_pow_eq (h : UnitaryFieldData p f F) {σ : F ≃+* F}
    {Q j : ℕ} (hσ : ∀ x : F, σ x = x ^ (Q ^ j)) (hQ : 1 ≤ Q)
    (hd : (p ^ f + 1).gcd n ∣ Q ^ j - 1) (a : Fˣ) (ha : h.norm (a : F) = 1) :
    ∃ μ : Fˣ, h.norm (μ : F) = 1 ∧
      μ ^ n = a * (Units.map σ.toRingHom.toMonoidHom a)⁻¹ := by
  haveI : Finite F := h.finite
  haveI : Fintype F := Fintype.ofFinite F
  let U := (Units.map h.normHom).ker
  haveI : IsCyclic U := isCyclic_subgroup_units U
  let φU : U →* U :=
    { toFun := fun u => ⟨Units.map σ.toRingHom.toMonoidHom (u : Fˣ), by
        rw [UnitaryFieldData.mem_ker_normUnits h]
        have h1 : h.norm (((Units.map σ.toRingHom.toMonoidHom (u : Fˣ) : Fˣ) : F)) =
            σ (h.norm ((u : Fˣ) : F)) :=
          CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.unitary_norm_apply
            h σ ((u : Fˣ) : F)
        rw [h1, (UnitaryFieldData.mem_ker_normUnits h).mp u.2, map_one]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun u v => Subtype.ext (map_mul _ _ _) }
  have hf : ∀ u : U, φU u = u ^ (Q ^ j) := by
    intro u
    apply Subtype.ext
    apply Units.ext
    change σ ((u : Fˣ) : F) = ((u : Fˣ) : F) ^ (Q ^ j)
    exact hσ _
  have hcardU : Nat.card U = p ^ f + 1 := (unitary_field_norm h).2.2.1
  have hd' : (Nat.card U).gcd n ∣ Q ^ j - 1 := by rw [hcardU]; exact hd
  let aU : U := ⟨a, (UnitaryFieldData.mem_ker_normUnits h).mpr ha⟩
  obtain ⟨μ, hμ⟩ :=
    CFSG.GroupTheory.CyclicSubgroup.exists_pow_eq_mul_inv_of_pow_form φU hf hQ hd' aU
  refine ⟨(μ : Fˣ), ?_, ?_⟩
  · have := (UnitaryFieldData.mem_ker_normUnits h).mp μ.2
    simpa using this
  · have hfcoe : ((φU aU : U) : Fˣ) = Units.map σ.toRingHom.toMonoidHom (a : Fˣ) := rfl
    have := congrArg (fun x : U => (x : Fˣ)) hμ
    simpa [aU, hfcoe] using this

theorem commutator_primeFormConjHom_fieldHom (h : UnitaryFieldData p f F)
    {σ : F ≃+* F} (hC : IsPrimeFormGram (1 : GL (Fin n) F))
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    ⁅primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A,
        primeFormFieldHom h hC σ⁆ =
      primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        (A * ⟨glAut σ (A : GL (Fin n) F),
          glAut_mem_primeFormUnitary h hC σ A.2⟩⁻¹) := by
  have h2 := primeFormField_conj_eq h hC σ⁻¹ A
  rw [map_inv, inv_inv] at h2
  have hmul : primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A *
        primeFormFieldHom h hC σ =
      primeFormFieldHom h hC σ *
        primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
          (primeFormFieldU h hC σ⁻¹ A) := by
    calc primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A *
          primeFormFieldHom h hC σ =
        primeFormFieldHom h hC σ *
          ((primeFormFieldHom h hC σ)⁻¹ *
            primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A *
            primeFormFieldHom h hC σ) := by group
      _ = primeFormFieldHom h hC σ *
          primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
            (primeFormFieldU h hC σ⁻¹ A) := by rw [h2]
  calc ⁅primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A,
        primeFormFieldHom h hC σ⁆
      = primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A *
          primeFormFieldHom h hC σ *
          (primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A)⁻¹ *
          (primeFormFieldHom h hC σ)⁻¹ := rfl
    _ = primeFormFieldHom h hC σ *
          (primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
            (primeFormFieldU h hC σ⁻¹ A) *
            (primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A)⁻¹) *
          (primeFormFieldHom h hC σ)⁻¹ := by rw [hmul]; group
    _ = primeFormFieldHom h hC σ *
          primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
            (primeFormFieldU h hC σ⁻¹ A * A⁻¹) *
          (primeFormFieldHom h hC σ)⁻¹ := by simp only [map_mul, map_inv]
    _ = primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
          (primeFormFieldU h hC σ (primeFormFieldU h hC σ⁻¹ A * A⁻¹)) :=
        primeFormField_conj_eq h hC σ _
    _ = primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        (A * ⟨glAut σ (A : GL (Fin n) F),
          glAut_mem_primeFormUnitary h hC σ A.2⟩⁻¹) := by
      congr 1
      apply Subtype.ext
      change glAut σ (glAut σ⁻¹ (A : GL (Fin n) F) * (A : GL (Fin n) F)⁻¹) =
        (A : GL (Fin n) F) * (glAut σ (A : GL (Fin n) F))⁻¹
      simp only [map_mul, map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem primeFormConjHom_mul_glAut_inv_mem_inner (h : UnitaryFieldData p f F)
    {σ : F ≃+* F} {Q j : ℕ}
    (hσ : ∀ x : F, σ x = x ^ (Q ^ j)) (hQ : 1 ≤ Q)
    (hd : (p ^ f + 1).gcd n ∣ Q ^ j - 1)
    (A : primeFormUnitary h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      (A * ⟨glAut σ (A : GL (Fin n) F),
        glAut_mem_primeFormUnitary h (isPrimeFormGram_one (n := n)) σ A.2⟩⁻¹) ∈
      inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  let I : Matrix (Fin n) (Fin n) F := ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let hC : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  let M : primeFormUnitary h I :=
    A * ⟨glAut σ (A : GL (Fin n) F), glAut_mem_primeFormUnitary h hC σ A.2⟩⁻¹
  have ha : h.norm (((GeneralLinearGroup.det (A : GL (Fin n) F)) : Fˣ) : F) = 1 := by
    rw [GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h (1 : GL (Fin n) F) A.2
  obtain ⟨μ, hμnorm, hμ⟩ := exists_normOne_pow_eq (h := h) (n := n) (Q := Q) (j := j)
    hσ hQ hd (GeneralLinearGroup.det (A : GL (Fin n) F)) ha
  have hdetM : GeneralLinearGroup.det (M : GL (Fin n) F) =
      GeneralLinearGroup.det (A : GL (Fin n) F) *
        (Units.map σ.toRingHom.toMonoidHom
          (GeneralLinearGroup.det (A : GL (Fin n) F)))⁻¹ := by
    change GeneralLinearGroup.det ((A : GL (Fin n) F) * glAut σ (A : GL (Fin n) F)⁻¹) = _
    calc GeneralLinearGroup.det ((A : GL (Fin n) F) * glAut σ (A : GL (Fin n) F)⁻¹)
        = GeneralLinearGroup.det (A : GL (Fin n) F) *
            GeneralLinearGroup.det (glAut σ (A : GL (Fin n) F))⁻¹ := map_mul _ _ _
      _ = GeneralLinearGroup.det (A : GL (Fin n) F) *
            (GeneralLinearGroup.det (glAut σ (A : GL (Fin n) F)))⁻¹ := by rw [map_inv]
      _ = _ := by
        rw [CFSG.GH74.Generic.BProg.B2.T4.T4OutCore.det_glAut σ (A : GL (Fin n) F)]
        rfl
  have hdet : ((M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = ((μ : F)) ^ n := by
    rw [← GeneralLinearGroup.val_det_apply (M : GL (Fin n) F), hdetM, ← hμ,
      Units.val_pow_eq_pow_val]
  have hμ0 : (μ : F) ≠ 0 := Units.ne_zero μ
  have hs : GeneralLinearGroup.scalar (Fin n) (Units.mk0 ((μ : F)⁻¹) (inv_ne_zero hμ0)) *
      (M : GL (Fin n) F) ∈ gramSU h I :=
    scalar_mul_mem_gramSU_of_det_eq_pow h M (μ : F) hμ0 hμnorm hdet
  have hμinvnorm : h.norm (((Units.mk0 ((μ : F)⁻¹) (inv_ne_zero hμ0) : Fˣ) : F)) = 1 := by
    rw [Units.val_mk0, norm_inv_eq, hμnorm, inv_one]
  let X : primeFormUnitary h I :=
    ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 ((μ : F)⁻¹) (inv_ne_zero hμ0)),
      scalar_mem_primeFormUnitary_one h hμinvnorm⟩
  have hX_one : primeFormConjHom h I X = 1 := by
    exact CFSG.GH74.Generic.BProg.B2.T4.T4OutCore.primeFormConjHom_scalar
      (h := h) (n := n) (Units.mk0 ((μ : F)⁻¹) (inv_ne_zero hμ0)) hμinvnorm
  let s : gramSU h I :=
    ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 ((μ : F)⁻¹) (inv_ne_zero hμ0)) *
      (M : GL (Fin n) F), hs⟩
  let sU : primeFormUnitary h I := ⟨(s : GL (Fin n) F), s.2.1⟩
  have hsU : sU = X * M := by
    apply Subtype.ext
    change (s : GL (Fin n) F) = (X : GL (Fin n) F) * (M : GL (Fin n) F)
    rfl
  have hMs : primeFormConjHom h I M = primeFormConjHom h I ⟨s, s.2.1⟩ := by
    show primeFormConjHom h I M = primeFormConjHom h I sU
    have h1 : primeFormConjHom h I (X * M) = primeFormConjHom h I M := by
      rw [map_mul, hX_one, one_mul]
    rw [← h1, ← hsU]
  exact (mem_inner_primeFormP h I _).2 ⟨s, hMs⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

end

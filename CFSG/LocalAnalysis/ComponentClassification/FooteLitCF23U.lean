module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Matrix LocalAnalysis.ComponentInitial UnitaryHigher ClassicalGroups.UnitaryFlag
open LocalAnalysis.ComponentInitial.FourGroupEvenCanonical UnbalancedCatalog.UnitaryFieldTransfer

section Lang

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

omit [CharP K 2] in
theorem one_add_smul_mul_of_mul_self_eq_zero {D : Matrix (Fin n) (Fin n) K} (hD : D * D = 0)
    (a b : K) :
    (1 + a • D) * (1 + b • D) = 1 + (a + b) • D := by
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hD, smul_zero, add_zero, add_smul]
  abel

theorem map_castHom_map (bar : K →+* K) (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (M.map (ZMod.castHom (dvd_refl 2) K)).map bar = M.map (ZMod.castHom (dvd_refl 2) K) := by
  rw [Matrix.map_map, ← RingHom.coe_comp,
    RingHom.ext_zmod (bar.comp (ZMod.castHom (dvd_refl 2) K)) (ZMod.castHom (dvd_refl 2) K)]

theorem map_castHom_mul_self {N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N * N = 0) :
    N.map (ZMod.castHom (dvd_refl 2) K) * N.map (ZMod.castHom (dvd_refl 2) K) = 0 := by
  rw [← Matrix.map_mul, hN, Matrix.map_zero _ (map_zero _)]

theorem map_castHom_one_add (N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (1 + N).map (ZMod.castHom (dvd_refl 2) K) =
      1 + (1 : K) • N.map (ZMod.castHom (dvd_refl 2) K) := by
  rw [one_smul, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] def langMat (ω : K) (A N : Matrix (Fin n) (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) K :=
  A.map (ZMod.castHom (dvd_refl 2) K) * (1 + ω • N.map (ZMod.castHom (dvd_refl 2) K))

theorem map_langMat (bar : K →+* K) (ω : K) (A N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (langMat ω A N).map bar = A.map (ZMod.castHom (dvd_refl 2) K) *
      (1 + bar ω • N.map (ZMod.castHom (dvd_refl 2) K)) := by
  rw [langMat, Matrix.map_mul, map_castHom_map, Matrix.map_add _ (map_add bar),
    Matrix.map_one _ (map_zero bar) (map_one bar), Matrix.map_smul' _ _ _ (map_mul bar),
    map_castHom_map]

theorem langMat_map_bar {bar : K →+* K} {ω : K} (hω : bar ω = ω + 1)
    {A N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N * N = 0) :
    (langMat ω A N).map bar = langMat ω A N * (1 + N).map (ZMod.castHom (dvd_refl 2) K) := by
  rw [map_langMat, hω, langMat, map_castHom_one_add, mul_assoc,
    one_add_smul_mul_of_mul_self_eq_zero (map_castHom_mul_self hN)]

theorem langMat_unitary {bar : K →+* K} {ω : K} (hω : bar ω = ω + 1)
    {A N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N * N = 0) (hNT : Nᵀ = N)
    (hA : Aᵀ * A = 1 + N) : ((langMat ω A N).map bar)ᵀ * langMat ω A N = 1 := by
  have hD := map_castHom_mul_self (K := K) hN
  have hDT : (N.map (ZMod.castHom (dvd_refl 2) K))ᵀ = N.map (ZMod.castHom (dvd_refl 2) K) := by
    rw [← Matrix.transpose_map, hNT]
  have hAA : (A.map (ZMod.castHom (dvd_refl 2) K))ᵀ * A.map (ZMod.castHom (dvd_refl 2) K) =
      1 + (1 : K) • N.map (ZMod.castHom (dvd_refl 2) K) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, hA, map_castHom_one_add]
  rw [map_langMat, hω, langMat, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, hDT, ← mul_assoc, mul_assoc (1 + _), hAA,
    one_add_smul_mul_of_mul_self_eq_zero hD, one_add_smul_mul_of_mul_self_eq_zero hD,
    show ω + 1 + 1 + ω = 0 by linear_combination (ω + 1) * CharTwo.two_eq_zero (R := K),
    zero_smul, add_zero]

theorem det_langMat (ω : K) {A Ai N : Matrix (Fin n) (Fin n) (ZMod 2)} (hN : N * N = 0)
    (hAi : A * Ai = 1) : (langMat ω A N).det = 1 := by
  have hdetA : A.det = 1 := by
    have h1 := congrArg Matrix.det hAi
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact (by decide : ∀ x y : ZMod 2, x * y = 1 → x = 1) _ _ h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (1 + ω • N.map (ZMod.castHom (dvd_refl 2) K)) *
      (1 + ω • N.map (ZMod.castHom (dvd_refl 2) K)) = 1 := by
    rw [one_add_smul_mul_of_mul_self_eq_zero (map_castHom_mul_self hN),
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  have hx := congrArg Matrix.det hsq
  rw [Matrix.det_mul, Matrix.det_one] at hx
  have hx1 : (1 + ω • N.map (ZMod.castHom (dvd_refl 2) K)).det = 1 := by
    set x := (1 + ω • N.map (ZMod.castHom (dvd_refl 2) K)).det
    have h0 : (x + 1) * (x + 1) = 0 := by linear_combination hx + (x + 1) * h2
    linear_combination mul_self_eq_zero.mp h0 - h2
  rw [langMat, Matrix.det_mul, hx1, mul_one, show A.map (ZMod.castHom (dvd_refl 2) K) =
    (ZMod.castHom (dvd_refl 2) K).mapMatrix A from rfl, ← RingHom.map_det, hdetA, map_one]

theorem map_mem_isometry_one {k : Type} [Field k] [CharP k 2] {g : GL (Fin n) (ZMod 2)}
    (hg : (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1) :
    GeneralLinearGroup.map (ZMod.castHom (dvd_refl 2) k) g ∈
      matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k) := by
  rw [mem_matrixIsometryGroup, Matrix.mul_one]
  show ((g : Matrix (Fin n) (Fin n) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) k))ᵀ *
    (g : Matrix (Fin n) (Fin n) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) k) = 1
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_castHom_injective_fin {k : Type} [Field k] [CharP k 2] :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (ZMod.castHom (dvd_refl 2) k)) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : GL (Fin n) k => (z : Matrix (Fin n) (Fin n) k)) hxy
  exact Matrix.map_injective (ZMod.castHom (dvd_refl 2) k).injective h

end Lang

section Aut

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem conj_field_lang {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (σ : K ≃+* K)
    (k g : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (hk : k⁻¹ * primeFormFieldU h hC σ k = g) (hg : primeFormFieldU h hC σ g = g) :
    (primeFormConjHom h _ k)⁻¹ * primeFormFieldHom h hC σ * primeFormConjHom h _ k =
      primeFormFieldHom h hC σ * primeFormConjHom h _ g := by
  have e1 := primeFormField_conj_eq h hC σ k
  have e2 := primeFormField_conj_eq h hC σ g
  rw [hg] at e2
  have e1' : primeFormFieldHom h hC σ * primeFormConjHom h _ k =
      primeFormConjHom h _ (primeFormFieldU h hC σ k) * primeFormFieldHom h hC σ := by
    rw [← e1, inv_mul_cancel_right]
  have e2' : primeFormFieldHom h hC σ * primeFormConjHom h _ g =
      primeFormConjHom h _ g * primeFormFieldHom h hC σ := by
    conv_lhs => rw [← inv_mul_cancel_right (primeFormFieldHom h hC σ * primeFormConjHom h _ g)
      (primeFormFieldHom h hC σ)]
    rw [e2]
  rw [mul_assoc, e1', ← mul_assoc, ← map_inv, ← map_mul, hk, e2']

end Aut

theorem exists_bar_eq_add_one {e : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : UnitaryFieldData 2 e K) : ∃ ω : K, h.bar ω = ω + 1 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have two : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : c + h.bar c ≠ 0 := by
    intro h0
    apply hc
    linear_combination h0 - c * two
  refine ⟨c / (c + h.bar c), ?_⟩
  have hfix : h.bar (c + h.bar c) = c + h.bar c := by
    rw [map_add, h.bar_bar, add_comm]
  rw [map_div₀, hfix, div_add_one hs]
  congr 1
  linear_combination -c * two

theorem exists_lang_witness {e n : ℕ} {K : Type} [Field K] [CharP K 2]
    (h : UnitaryFieldData 2 e K) [CharP h.fixedField 2] {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hC1 : (C : Matrix (Fin n) (Fin n) K) = 1)
    {Cl : GL (Fin n) h.fixedField}
    (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = h.bar x) {A Ai N : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hN : N * N = 0) (hNT : Nᵀ = N) (hA : Aᵀ * A = 1 + N) (hAi : A * Ai = 1)
    (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))
    (hg : ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) =
      (1 + N).map (ZMod.castHom (dvd_refl 2) h.fixedField)) :
    ∃ k : gramSU h (C : Matrix (Fin n) (Fin n) K),
      (MulAut.conj (k : primeFormP h (C : Matrix (Fin n) (Fin n) K)))⁻¹ *
          primeFormFieldHom h hC σ * MulAut.conj (k : primeFormP h (C : Matrix (Fin n) (Fin n) K)) =
        primeFormFieldHom h hC σ * primeFormConjHom h _ (fixedIsometryHom h hCl g) := by
  obtain ⟨ω, hω⟩ := exists_bar_eq_add_one h
  have hkU := langMat_unitary (K := K) hω hN hNT hA
  have hkR : langMat ω A N * ((langMat ω A N).map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hkU
  let k : GL (Fin n) K := ⟨langMat ω A N, ((langMat ω A N).map h.bar)ᵀ, hkR, hkU⟩
  have hkSU : k ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) := by
    rw [mem_gramSU, hC1, Matrix.mul_one]
    exact ⟨hkU, det_langMat ω hN hAi⟩
  have hσfun : (⇑σ : K → K) = ⇑h.bar := funext hσ
  refine ⟨⟨k, hkSU⟩, ?_⟩
  rw [← UnitaryHigher.primeFormConjHom_eq_conj h _ ⟨k, hkSU⟩]
  refine conj_field_lang h hC σ _ _ (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, coe_fixedIsometryHom,
      inv_mul_eq_iff_eq_mul]
    apply Units.ext
    rw [coe_glAut, Units.val_mul, hσfun]
    show (langMat ω A N).map h.bar = langMat ω A N *
      ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype
    rw [hg, Matrix.map_map, ← RingHom.coe_comp,
      RingHom.ext_zmod (h.fixedField.subtype.comp (ZMod.castHom (dvd_refl 2) h.fixedField))
        (ZMod.castHom (dvd_refl 2) K), langMat_map_bar hω hN]
  · rw [coe_primeFormFieldU, coe_fixedIsometryHom]
    apply Units.ext
    rw [coe_glAut, hσfun]
    exact map_subtype_map_bar h _

end CFSG.ComponentClassification.GSThmB.CF23I

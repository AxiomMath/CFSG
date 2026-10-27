module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaAutFusion
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsModel

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem hermitian_add {B B' : Matrix (Fin 3) (Fin 3) F} (hB : (B.map h.bar)ᵀ = B)
    (hB' : (B'.map h.bar)ᵀ = B') : ((B + B').map h.bar)ᵀ = B + B' := by
  rw [Matrix.map_add _ (map_add _), transpose_add, hB, hB']

theorem hermitian_zero : ((0 : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ = 0 := by
  rw [Matrix.map_zero _ (map_zero _), transpose_zero]

theorem mul_self_of_coe_eq_nMat {g : sixS h} {B : Matrix (Fin 3) (Fin 3) F}
    (hg : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = nMat B) : g * g = 1 :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, hg, nMat_mul_self h, Subgroup.coe_one, Units.val_one]))

@[expose] noncomputable def hermS : Subgroup (sixS h) where
  carrier := {g | ∃ B : Matrix (Fin 3) (Fin 3) F, (B.map h.bar)ᵀ = B ∧
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = nMat B}
  mul_mem' := by
    rintro g g' ⟨B, hB, hg⟩ ⟨B', hB', hg'⟩
    exact ⟨B + B', hermitian_add h hB hB', by
      rw [Subgroup.coe_mul, Units.val_mul, hg, hg', nMat_mul]⟩
  one_mem' := ⟨0, hermitian_zero h, by rw [Subgroup.coe_one, Units.val_one, nMat_zero]⟩
  inv_mem' := by
    rintro g ⟨B, hB, hg⟩
    rw [inv_eq_of_mul_eq_one_right (mul_self_of_coe_eq_nMat h hg)]
    exact ⟨B, hB, hg⟩

theorem nElt_mem_hermS (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    nElt h B hB ∈ hermS h :=
  ⟨B, hB, rfl⟩

@[expose] noncomputable def hermQ : Subgroup (sixQ h) :=
  (hermS h).map (sixProj h)

theorem sq_of_mem_hermQ {x : sixQ h} (hx : x ∈ hermQ h) : x ^ 2 = 1 := by
  obtain ⟨g, ⟨B, -, hg⟩, rfl⟩ := hx
  rw [← map_pow, sq, mul_self_of_coe_eq_nMat h hg, map_one]

theorem card_hermS : Nat.card (hermS h) = 2 ^ 9 := by
  rw [← card_hermMat h]
  symm
  refine Nat.card_eq_of_bijective (fun B => ⟨nElt h B.1 B.2, nElt_mem_hermS h B.1 B.2⟩)
    ⟨fun B B' hBB' => ?_, ?_⟩
  · have := congrArg (fun g : hermS h =>
      (((g : sixS h) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hBB'
    exact Subtype.ext (nMat_injective this)
  · rintro ⟨g, B, hB, hg⟩
    exact ⟨⟨B, hB⟩, Subtype.ext (Subtype.ext (Units.ext hg.symm))⟩

theorem nMat_apply_zero_zero (B : Matrix (Fin 3) (Fin 3) F) : nMat B 0 0 = 1 := by
  simp [nMat, reindex_apply]

theorem injOn_sixProj_hermS : Set.InjOn (sixProj h) (hermS h) := by
  rintro g ⟨B, -, hg⟩ g' ⟨B', -, hg'⟩ hgg'
  obtain ⟨c, hc⟩ := (sixProj_eq_iff h).mp hgg'
  have h00 := congrFun (congrFun (congrArg
    (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) hc) 0) 0
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hg, hg', scalar_apply,
    diagonal_mul, nMat_apply_zero_zero, mul_one] at h00
  have hc1 : c = 1 := Units.ext h00.symm
  rw [hc1, map_one, one_mul] at hc
  exact (Subtype.ext hc).symm

theorem card_hermQ : Nat.card (hermQ h) = 2 ^ 9 := by
  rw [hermQ, card_map_of_injOn _ (injOn_sixProj_hermS h), card_hermS]

theorem blocks_of_nMat_mul {a b c d B B' : Matrix (Fin 3) (Fin 3) F}
    (hBM : nMat B * reindex sixEquiv sixEquiv (fromBlocks a b c d) =
      reindex sixEquiv sixEquiv (fromBlocks a b c d) * nMat B') :
    B * c = 0 ∧ B * d = a * B' := by
  rw [nMat, nMat, reindex_mul_reindex, reindex_mul_reindex] at hBM
  have e := (reindex sixEquiv sixEquiv).injective hBM
  rw [fromBlocks_multiply, fromBlocks_multiply] at e
  obtain ⟨e1, e2, -, -⟩ := fromBlocks_inj.mp e
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero] at e1 e2
  exact ⟨add_left_cancel (e1.trans (add_zero a).symm),
    add_left_cancel (e2.trans (add_comm _ _))⟩

theorem hermitian_one : ((1 : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ = 1 := by
  rw [Matrix.map_one _ (map_zero _) (map_one _), transpose_one]

theorem hermitian_single_self (i : Fin 3) :
    ((single i i (1 : F)).map h.bar)ᵀ = single i i 1 := by
  rw [map_single, map_one, transpose_single]

theorem hermitian_single_add (i j : Fin 3) :
    ((single i j (1 : F) + single j i 1).map h.bar)ᵀ = single i j 1 + single j i 1 := by
  rw [Matrix.map_add _ (map_add _), map_single, map_single, map_one, transpose_add,
    transpose_single, transpose_single, add_comm]

theorem hermitian_single_bar (x : F) :
    ((single 0 1 x + single 1 0 (h.bar x) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ =
      single 0 1 x + single 1 0 (h.bar x) := by
  rw [Matrix.map_add _ (map_add _), map_single, map_single, h.bar_bar, transpose_add,
    transpose_single, transpose_single, add_comm]

theorem eq_smul_nMat_of_forall {M : Matrix (Fin 6) (Fin 6) F} (hM : M.det ≠ 0) {φ : F ≃+* F}
    (hBM : ∀ B : Matrix (Fin 3) (Fin 3) F, (B.map h.bar)ᵀ = B →
      nMat B * M = M * nMat (B.map φ)) :
    (∀ x, φ x = x) ∧ ∃ μ : F, μ ≠ 0 ∧ ∃ B₀ : Matrix (Fin 3) (Fin 3) F, M = μ • nMat B₀ := by
  set P := reindex sixEquiv.symm sixEquiv.symm M with hP
  have hMP : M = reindex sixEquiv sixEquiv
      (fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂) := by
    rw [fromBlocks_toBlocks, hP]
    ext i j
    simp
  set a := P.toBlocks₁₁
  set b := P.toBlocks₁₂
  set c := P.toBlocks₂₁
  set d := P.toBlocks₂₂
  have hk : ∀ B, (B.map h.bar)ᵀ = B → B * c = 0 ∧ B * d = a * B.map φ := fun B hB => by
    have := hBM B hB
    rw [hMP] at this
    exact blocks_of_nMat_mul this
  have hc0 : c = 0 := by simpa using (hk 1 (hermitian_one h)).1
  have hda : d = a := by
    have := (hk 1 (hermitian_one h)).2
    rwa [Matrix.one_mul, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.mul_one] at this
  have hcomm : ∀ B, (B.map h.bar)ᵀ = B → B * a = a * B.map φ := fun B hB => by
    have := (hk B hB).2
    rwa [hda] at this
  have hoff : ∀ i j, i ≠ j → a i j = 0 := fun i j hij => by
    have := congrFun (congrFun (hcomm _ (hermitian_single_self h i)) i) j
    rwa [map_single, map_one, single_mul_apply_same, one_mul,
      mul_single_apply_of_ne (hbj := Ne.symm hij)] at this
  have hdiag : ∀ i j, i ≠ j → a j j = a i i := fun i j hij => by
    have := congrFun (congrFun (hcomm _ (hermitian_single_add h i j)) i) j
    rwa [Matrix.map_add _ (map_add _), map_single, map_single, map_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.add_apply, Matrix.add_apply, single_mul_apply_same,
      single_mul_apply_of_ne (h := hij), mul_single_apply_same,
      mul_single_apply_of_ne (hbj := Ne.symm hij), one_mul, mul_one, add_zero,
      add_zero] at this
  set μ := a 0 0
  have ha : a = μ • 1 := by
    ext i j
    rw [Matrix.smul_apply, one_apply, smul_eq_mul]
    split_ifs with hij
    · subst hij
      by_cases hi : i = 0
      · rw [hi, mul_one]
      · rw [hdiag 0 i (Ne.symm hi), mul_one]
    · rw [hoff i j hij, mul_zero]
  have hμ : μ ≠ 0 := by
    intro hμ0
    apply hM
    rw [hMP, det_reindex_self, hc0, hda, det_fromBlocks_zero₂₁, ha, hμ0, zero_smul, det_zero,
      zero_mul]
  refine ⟨fun x => ?_, μ, hμ, μ⁻¹ • b, ?_⟩
  · have h10 : (single (1 : Fin 3) (0 : Fin 3) (h.bar x) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 :=
      single_apply_of_ne _ _ _ _ _ (by decide)
    have := congrFun (congrFun (hcomm _ (hermitian_single_bar h x)) 0) 1
    rw [ha, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.smul_apply, map_apply, Matrix.add_apply, single_apply_same, h10, add_zero,
      smul_eq_mul, smul_eq_mul] at this
    exact (mul_left_cancel₀ hμ this).symm
  · have : (μ • nMat (μ⁻¹ • b) : Matrix (Fin 6) (Fin 6) F) =
        reindex sixEquiv sixEquiv (μ • fromBlocks 1 (μ⁻¹ • b) 0 1) := rfl
    rw [this, fromBlocks_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul, smul_zero, hMP, hc0,
      hda, ha]

theorem hermitian_of_nMat_isometry {B : Matrix (Fin 3) (Fin 3) F}
    (hB : ((nMat B).map h.bar)ᵀ * (sixJ h : Matrix (Fin 6) (Fin 6) F) * nMat B = sixJ h) :
    (B.map h.bar)ᵀ = B := by
  rw [sixJ_eq, nMat, map_reindex, transpose_reindex, reindex_mul_reindex, reindex_mul_reindex,
    fromBlocks_map, fromBlocks_transpose] at hB
  have e := (reindex sixEquiv sixEquiv).injective hB
  simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.map_zero _ (map_zero h.bar),
    transpose_one, transpose_zero, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e
  obtain ⟨-, -, -, e4⟩ := fromBlocks_inj.mp e
  ext i j
  have := congrFun (congrFun e4 i) j
  simp only [Matrix.add_apply, transpose_apply, map_apply, Matrix.zero_apply] at this
  rw [transpose_apply, map_apply]
  linear_combination this - B i j * two_eq_zero h

theorem conj_field_sixProj (A : sixU h) (φ : F ≃+* F) (g : sixS h) :
    (primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_sixJ h) φ) (sixProj h g) =
      sixProj h ⟨(A : GL (Fin 6) F) * glAut φ (g : GL (Fin 6) F) * (A : GL (Fin 6) F)⁻¹,
        conj_mem_gramSU h _ A.2 (glAut_mem_gramSU h (isPrimeFormGram_sixJ h) φ g.2)⟩ := by
  rw [MulAut.mul_apply]
  change primeFormConjHom h _ A
    (primeFormFieldAut h (isPrimeFormGram_sixJ h) φ (g : sixQ h)) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  rfl

theorem nMat_mul_eq_of_fixes (A : sixU h) (φ : F ≃+* F) {B : Matrix (Fin 3) (Fin 3) F}
    (hB : (B.map h.bar)ᵀ = B)
    (hfix : (primeFormConjHom h _ A * primeFormFieldHom h (isPrimeFormGram_sixJ h) φ)
      (sixProj h (nElt h B hB)) = sixProj h (nElt h B hB)) :
    nMat B * ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * nMat (B.map φ) := by
  rw [conj_field_sixProj] at hfix
  obtain ⟨c, hc⟩ := (sixProj_eq_iff h).mp hfix
  have hc' : (nGL B : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) c *
      ((A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹) := hc
  have hn2 : (nGL B : GL (Fin 6) F) * nGL B = 1 := congrArg Subtype.val (nElt_mul_self h B hB)
  have hY2 : (A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹ *
      ((A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹) = 1 := by
    rw [show (A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹ *
        ((A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹) =
        (A : GL (Fin 6) F) * (glAut φ (nGL B) * glAut φ (nGL B)) * (A : GL (Fin 6) F)⁻¹ by group,
      ← map_mul, hn2, map_one, mul_one, mul_inv_cancel]
  have hc2 : Matrix.GeneralLinearGroup.scalar (Fin 6) (c * c) = 1 := by
    set Y := (A : GL (Fin 6) F) * glAut φ (nGL B) * (A : GL (Fin 6) F)⁻¹
    set z := Matrix.GeneralLinearGroup.scalar (Fin 6) c
    rw [← hn2, hc', map_mul]
    rw [mul_assoc, ← mul_assoc Y, (commute_scalar c Y).eq, mul_assoc, ← mul_assoc z z, hY2,
      mul_one]
  have hcc : (c : F) * c = 1 := by
    have := congrFun (congrFun (congrArg
      (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) hc2) 0) 0
    simpa [GeneralLinearGroup.coe_scalar] using this
  have hc1 : c = 1 := by
    have hsq : ((c : F) - 1) ^ 2 = 0 := by
      linear_combination hcc - (c : F) * two_eq_zero h + two_eq_zero h
    exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))
  rw [hc1, map_one, one_mul] at hc'
  have hc'' : (nGL B : GL (Fin 6) F) * A = A * glAut φ (nGL B) := by
    conv_lhs => rw [hc']
    rw [inv_mul_cancel_right]
  have := congrArg (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) hc''
  simp only [Units.val_mul, coe_glAut, coe_nGL] at this
  rwa [nMat_map_of _ (map_zero φ) (map_one φ)] at this

theorem exists_eq_conj_of_fixes_hermQ (β : MulAut (sixQ h)) (hβ : ∀ x ∈ hermQ h, β x = x) :
    ∃ y ∈ hermQ h, β = MulAut.conj y := by
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor h (isPrimeFormGram_sixJ h)
    three_le_six not_six_eq_three β
  have hdet : ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 6) F).isUnit).ne_zero
  obtain ⟨hφ, μ, hμ, B₀, hAB⟩ := eq_smul_nMat_of_forall h hdet (φ := φ) fun B hB =>
    nMat_mul_eq_of_fixes h A φ hB (by
      rw [← hA]
      exact hβ _ ⟨nElt h B hB, nElt_mem_hermS h B hB, rfl⟩)
  have hφ1 : φ = 1 := RingEquiv.ext hφ
  rw [hφ1, map_one, mul_one] at hA
  set u : Fˣ := Units.mk0 μ hμ
  set A' : GL (Fin 6) F := Matrix.GeneralLinearGroup.scalar (Fin 6) u⁻¹ * A with hA'
  have hA'mat : (A' : Matrix (Fin 6) (Fin 6) F) = nMat B₀ := by
    rw [hA', Units.val_mul, GeneralLinearGroup.coe_scalar, hAB, scalar_apply,
      ← smul_eq_diagonal_mul, smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0,
      inv_mul_cancel₀ hμ, one_smul]
  have hA'U : A' ∈ sixU h := mul_mem (scalar_mem_sixU h _) A.2
  have hA'S : A' ∈ sixS h := ⟨hA'U, by rw [hA'mat, det_nMat]⟩
  have hB₀ : (B₀.map h.bar)ᵀ = B₀ := hermitian_of_nMat_isometry h (by
    rw [← hA'mat]
    exact hA'U)
  refine ⟨sixProj h ⟨A', hA'S⟩, ⟨⟨A', hA'S⟩, ⟨B₀, hB₀, hA'mat⟩, rfl⟩, ?_⟩
  rw [hA, conj_sixProj_eq]
  have hAA' : (A : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) u * A' := by
    rw [hA', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin 6) F) * g * (A : GL (Fin 6) F)⁻¹ = A' * g * A'⁻¹
  set z := Matrix.GeneralLinearGroup.scalar (Fin 6) u
  rw [hAA', show z * A' * (g : GL (Fin 6) F) * (z * A')⁻¹ =
      z * (A' * (g : GL (Fin 6) F) * A'⁻¹) * z⁻¹ by group, ← (commute_scalar u _).eq,
    mul_inv_cancel_right]

end CFSG.EvenSmallLie.UnitarySix.Yamada

module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F]

section Field

variable (h : UnitaryFieldData 2 1 F)

include h

theorem bar_eq_sq (c : F) : h.bar c = c ^ 2 := by
  rw [h.bar_apply, pow_one]

theorem natCard_eq_four : Nat.card F = 4 := by
  rw [h.card]
  norm_num

theorem pow_three_eq_one {c : F} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := h.finite
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, natCard_eq_four h]
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [hcard] at this

theorem units_pow_three_eq_one (c : Fˣ) : c ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, pow_three_eq_one h c.ne_zero, Units.val_one])

theorem norm_eq_one {c : F} (hc : c ≠ 0) : h.norm c = 1 := by
  rw [UnitaryFieldData.norm, bar_eq_sq h, ← pow_succ', pow_three_eq_one h hc]

theorem two_eq_zero : (2 : F) = 0 := by
  have := h.charP
  exact CharTwo.two_eq_zero

theorem add_self (a : F) : a + a = 0 := by
  rw [← two_mul, two_eq_zero h, zero_mul]

omit h in
theorem sq_eq_self_iff {c : F} : c ^ 2 = c ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro hc
    have h1 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hc, sub_self]
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  · rintro (rfl | rfl) <;> simp

theorem mem_bot_iff_sq_eq_self {c : F} : c ∈ (⊥ : Subfield F) ↔ c ^ 2 = c := by
  constructor
  · intro hc
    rw [← bar_eq_sq h]
    exact ringHom_apply_of_mem_bot h.bar hc
  · intro hc
    rcases sq_eq_self_iff.mp hc with rfl | rfl
    · exact zero_mem _
    · exact one_mem _

theorem mem_bot_iff {c : F} : c ∈ (⊥ : Subfield F) ↔ c = 0 ∨ c = 1 :=
  (mem_bot_iff_sq_eq_self h).trans sq_eq_self_iff

end Field

variable (h : UnitaryFieldData 2 1 F)

@[expose] noncomputable def barEquiv : F ≃+* F :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEquiv_apply (c : F) : barEquiv h c = c ^ 2 :=
  bar_eq_sq h c

theorem barEquiv_eq_bar (c : F) : barEquiv h c = h.bar c :=
  rfl

theorem barEquiv_mul_self : barEquiv h * barEquiv h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

abbrev sixEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

@[simp] theorem sixEquiv_symm_zero : sixEquiv.symm (0 : Fin 6) = Sum.inl 0 := rfl

@[simp] theorem sixEquiv_symm_one : sixEquiv.symm (1 : Fin 6) = Sum.inl 1 := rfl

@[simp] theorem sixEquiv_symm_two : sixEquiv.symm (2 : Fin 6) = Sum.inl 2 := rfl

@[simp] theorem sixEquiv_symm_three : sixEquiv.symm (3 : Fin 6) = Sum.inr 0 := rfl

@[simp] theorem sixEquiv_symm_four : sixEquiv.symm (4 : Fin 6) = Sum.inr 1 := rfl

@[simp] theorem sixEquiv_symm_five : sixEquiv.symm (5 : Fin 6) = Sum.inr 2 := rfl

theorem reindex_mul_reindex {R : Type} [CommRing R]
    (M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R) :
    reindex sixEquiv sixEquiv M * reindex sixEquiv sixEquiv N =
      reindex sixEquiv sixEquiv (M * N) := by
  simp only [reindex_apply, submatrix_mul_equiv]

theorem map_reindex {R R' : Type} (f : R → R') (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R) :
    (reindex sixEquiv sixEquiv M).map f = reindex sixEquiv sixEquiv (M.map f) := by
  simp only [reindex_apply, submatrix_map]

@[expose] noncomputable def sixJ : GL (Fin 6) F :=
  have := h.charP
  blockSwapGL (n := 6) (r := 3) rfl

theorem coe_sixJ : (sixJ h : Matrix (Fin 6) (Fin 6) F) = blockSwapJ 6 3 :=
  rfl

theorem sixJ_eq : (sixJ h : Matrix (Fin 6) (Fin 6) F) =
    reindex sixEquiv sixEquiv (fromBlocks 0 1 1 0) := by
  rw [coe_sixJ]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockSwapJ, reindex_apply]

theorem isPrimeFormGram_sixJ : IsPrimeFormGram (sixJ h) :=
  have := h.charP
  isPrimeFormGram_blockSwapGL (n := 6) (r := 3) rfl

theorem sixJ_mulVec (v : Fin 6 → F) :
    (sixJ h : Matrix (Fin 6) (Fin 6) F) *ᵥ v = ![v 3, v 4, v 5, v 0, v 1, v 2] := by
  rw [coe_sixJ]
  funext a
  fin_cases a <;> simp [blockSwapJ, mulVec, dotProduct, Fin.sum_univ_six]

theorem gramForm_sixJ (v w : Fin 6 → F) :
    gramForm h (sixJ h : Matrix (Fin 6) (Fin 6) F) v w =
      h.bar (v 0) * w 3 + h.bar (v 1) * w 4 + h.bar (v 2) * w 5 + h.bar (v 3) * w 0 +
        h.bar (v 4) * w 1 + h.bar (v 5) * w 2 := by
  rw [gramForm_apply, sixJ_mulVec]
  simp [dotProduct, Fin.sum_univ_six]

noncomputable abbrev sixU : Subgroup (GL (Fin 6) F) :=
  primeFormUnitary h (sixJ h : Matrix (Fin 6) (Fin 6) F)

noncomputable abbrev sixS : Subgroup (GL (Fin 6) F) :=
  gramSU h (sixJ h : Matrix (Fin 6) (Fin 6) F)

noncomputable abbrev sixScalars : Subgroup (sixS h) :=
  normOneScalars h (sixS h) 6

noncomputable abbrev sixQ : Type :=
  primeFormP h (sixJ h : Matrix (Fin 6) (Fin 6) F)

@[expose] noncomputable def sixProj : sixS h →* sixQ h :=
  QuotientGroup.mk' _

theorem sixProj_apply (g : sixS h) : sixProj h g = (g : sixQ h) :=
  rfl

theorem sixProj_surjective : Function.Surjective (sixProj h) :=
  QuotientGroup.mk'_surjective _

theorem scalar_mem_sixU (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ sixU h := by
  rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul,
    norm_eq_one h c.ne_zero, one_smul]

theorem scalar_mem_sixS (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ sixS h := by
  refine ⟨scalar_mem_sixU h c, ?_⟩
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have h3 := pow_three_eq_one h c.ne_zero
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h3, one_pow]

theorem mem_sixScalars_iff (z : sixS h) :
    z ∈ sixScalars h ↔
      ∃ c : Fˣ, (z : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  constructor
  · rintro ⟨c, -, -, hz⟩
    exact ⟨c, hz⟩
  · rintro ⟨c, hz⟩
    refine ⟨c, norm_eq_one h c.ne_zero, ?_, hz⟩
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_pow_three_eq_one h, one_pow]

theorem sixProj_eq_iff {g g' : sixS h} :
    sixProj h g = sixProj h g' ↔ ∃ c : Fˣ,
      (g' : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) c * g := by
  rw [sixProj_apply, sixProj_apply, QuotientGroup.eq, mem_sixScalars_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : (g' : GL (Fin 6) F) = g * Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
      rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [this, (commute_scalar c (g : GL (Fin 6) F)).eq]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc, ← (commute_scalar c (g : GL (Fin 6) F)).eq,
      inv_mul_cancel_left]

@[expose] noncomputable def sigmaQ : MulAut (sixQ h) :=
  primeFormFieldHom h (isPrimeFormGram_sixJ h) (barEquiv h)

theorem sigmaQ_sixProj (g : sixS h) :
    sigmaQ h (sixProj h g) =
      sixProj h ⟨glAut (barEquiv h) g, glAut_mem_gramSU h (isPrimeFormGram_sixJ h) _ g.2⟩ :=
  primeFormFieldAut_mk h (isPrimeFormGram_sixJ h) (barEquiv h) g

@[expose] def nMat (B : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 6) (Fin 6) F :=
  reindex sixEquiv sixEquiv (fromBlocks 1 B 0 1)

@[expose] def dMat (k : ℕ) : Matrix (Fin 3) (Fin 3) F :=
  diagonal fun i => if (i : ℕ) < k then 1 else 0

theorem nMat_mul (B B' : Matrix (Fin 3) (Fin 3) F) : nMat B * nMat B' = nMat (B + B') := by
  rw [nMat, nMat, reindex_mul_reindex, fromBlocks_multiply, nMat]
  simp [add_comm]

theorem nMat_zero : nMat (0 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [nMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

include h in
theorem nMat_mul_self (B : Matrix (Fin 3) (Fin 3) F) : nMat B * nMat B = 1 := by
  rw [nMat_mul, show B + B = 0 from Matrix.ext fun i j => add_self h (B i j), nMat_zero]

theorem det_nMat (B : Matrix (Fin 3) (Fin 3) F) : (nMat B).det = 1 := by
  rw [nMat, det_reindex_self, det_fromBlocks_zero₂₁, det_one, one_mul]

theorem nMat_injective : Function.Injective (nMat (F := F)) := by
  intro B B' hBB'
  ext i j
  have := congrFun (congrFun hBB' (sixEquiv (Sum.inl i))) (sixEquiv (Sum.inr j))
  simpa [nMat, reindex_apply] using this

theorem nMat_isometry {B : Matrix (Fin 3) (Fin 3) F} (hB : (B.map h.bar)ᵀ = B) :
    ((nMat B).map h.bar)ᵀ * (sixJ h : Matrix (Fin 6) (Fin 6) F) * nMat B = sixJ h := by
  rw [sixJ_eq, nMat, map_reindex, transpose_reindex, reindex_mul_reindex, reindex_mul_reindex,
    fromBlocks_map, fromBlocks_transpose]
  congr 1
  simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.map_zero _ (map_zero h.bar),
    transpose_one, transpose_zero, hB, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [show B + B = 0 from Matrix.ext fun i j => add_self h (B i j)]

@[expose] noncomputable def nGL (B : Matrix (Fin 3) (Fin 3) F) : GL (Fin 6) F :=
  ⟨nMat B, nMat (-B), by rw [nMat_mul, add_neg_cancel, nMat_zero],
    by rw [nMat_mul, neg_add_cancel, nMat_zero]⟩

theorem coe_nGL (B : Matrix (Fin 3) (Fin 3) F) :
    (nGL B : Matrix (Fin 6) (Fin 6) F) = nMat B :=
  rfl

@[expose] noncomputable def nElt (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    sixS h :=
  ⟨nGL B, nMat_isometry h hB, det_nMat B⟩

theorem coe_nElt (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    ((nElt h B hB : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = nMat B :=
  rfl

theorem nElt_mul_self (B : Matrix (Fin 3) (Fin 3) F) (hB : (B.map h.bar)ᵀ = B) :
    nElt h B hB * nElt h B hB = 1 :=
  Subtype.ext (Units.ext (nMat_mul_self h B))

theorem dMat_hermitian (k : ℕ) : ((dMat k : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ = dMat k := by
  rw [dMat, diagonal_map (map_zero h.bar), diagonal_transpose]
  congr 1
  funext i
  split_ifs <;> simp

@[expose] noncomputable def tElt (k : ℕ) : sixS h :=
  nElt h (dMat k) (dMat_hermitian h k)

theorem coe_tElt (k : ℕ) :
    ((tElt h k : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = nMat (dMat k) :=
  rfl

theorem map_bar_eq_self_iff (M : Matrix (Fin 6) (Fin 6) F) :
    M.map h.bar = M ↔ ∀ i j, M i j ∈ (⊥ : Subfield F) := by
  constructor
  · intro hM i j
    rw [mem_bot_iff_sq_eq_self h, ← bar_eq_sq h]
    exact congrFun (congrFun hM i) j
  · intro hM
    ext i j
    rw [map_apply, bar_eq_sq h]
    exact (mem_bot_iff_sq_eq_self h).mp (hM i j)

theorem glAut_barEquiv_eq_self_iff (g : GL (Fin 6) F) :
    glAut (barEquiv h) g = g ↔ ∀ i j, (g : Matrix (Fin 6) (Fin 6) F) i j ∈ (⊥ : Subfield F) := by
  rw [← map_bar_eq_self_iff h]
  constructor
  · intro hg
    have := congrArg (fun x : GL (Fin 6) F => (x : Matrix (Fin 6) (Fin 6) F)) hg
    rw [coe_glAut] at this
    exact this
  · intro hg
    exact Units.ext (by rw [coe_glAut]; exact hg)

@[expose] noncomputable def binarySp : Subgroup (sixS h) where
  carrier := {g | ∀ i j, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j ∈ (⊥ : Subfield F)}
  mul_mem' {g g'} hg hg' := by
    have hg1 := (glAut_barEquiv_eq_self_iff h _).mpr hg
    have hg2 := (glAut_barEquiv_eq_self_iff h _).mpr hg'
    refine (glAut_barEquiv_eq_self_iff h _).mp ?_
    rw [Subgroup.coe_mul, map_mul, hg1, hg2]
  one_mem' := by
    refine (glAut_barEquiv_eq_self_iff h _).mp ?_
    rw [Subgroup.coe_one, map_one]
  inv_mem' {g} hg := by
    have hg1 := (glAut_barEquiv_eq_self_iff h _).mpr hg
    refine (glAut_barEquiv_eq_self_iff h _).mp ?_
    rw [Subgroup.coe_inv, map_inv, hg1]

theorem mem_binarySp_iff {g : sixS h} :
    g ∈ binarySp h ↔
      ∀ i j, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j ∈ (⊥ : Subfield F) :=
  Iff.rfl

theorem mem_binarySp_iff_glAut {g : sixS h} :
    g ∈ binarySp h ↔ glAut (barEquiv h) (g : GL (Fin 6) F) = g :=
  (glAut_barEquiv_eq_self_iff h _).symm

@[expose] noncomputable def t0Elt : sixS h :=
  tElt h 1

theorem nMat_dMat_one : nMat (dMat 1 : Matrix (Fin 3) (Fin 3) F) = 1 + single 0 3 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nMat, dMat, reindex_apply, one_apply]

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

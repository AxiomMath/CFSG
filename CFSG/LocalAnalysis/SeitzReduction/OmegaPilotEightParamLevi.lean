module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusGen

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv coordinateQuadMinus_apply)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val
  fieldAutT fieldAutT_mk matrixDerivedConjugation_fieldPair_val)
open CFSG.SeitzReduction.TwistedE6Pilot (isExtension_coordinateQuadMinus)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open scoped MatrixGroups

section Block

variable {F : Type} [Field F] {n : ℕ}

@[expose] def minusLeviBlock (A : SpecialLinearGroup (Fin (n - 1)) F) :
    Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
  fromBlocks (A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) 0 0
    (fromBlocks ((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) :
      Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ 0 0 1)

theorem minusLeviBlock_one : minusLeviBlock (1 : SpecialLinearGroup (Fin (n - 1)) F) = 1 := by
  rw [minusLeviBlock, inv_one]
  change fromBlocks (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) F) 0 0
    (fromBlocks (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ 0 0 1) = 1
  rw [transpose_one, fromBlocks_one, fromBlocks_one]

theorem minusLeviBlock_mul (A B : SpecialLinearGroup (Fin (n - 1)) F) :
    minusLeviBlock (A * B) = minusLeviBlock A * minusLeviBlock B := by
  have h1 : ((A * B : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F) =
      (A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) * (B : Matrix (Fin (n - 1)) (Fin (n - 1)) F) :=
    Matrix.SpecialLinearGroup.coe_mul A B
  have h2 : (((A * B)⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) :
      Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ =
      ((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ *
        ((B⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ := by
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, transpose_mul]
  simp only [minusLeviBlock, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, h1, h2]

theorem minusLeviBlock_inl_inl (A : SpecialLinearGroup (Fin (n - 1)) F) (i j : Fin (n - 1)) :
    minusLeviBlock A (.inl i) (.inl j) = (A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) i j := rfl

theorem minusLeviBlock_inr_inl (A : SpecialLinearGroup (Fin (n - 1)) F) (i j : Fin (n - 1)) :
    minusLeviBlock A (.inr (.inl i)) (.inr (.inl j)) =
      ((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F) j i :=
  rfl

theorem minusLeviBlock_inr_inr (A : SpecialLinearGroup (Fin (n - 1)) F) (r s : Fin 2) :
    minusLeviBlock A (.inr (.inr r)) (.inr (.inr s)) = (1 : Matrix (Fin 2) (Fin 2) F) r s := rfl

theorem minusLeviBlock_map {F' : Type} [Field F'] (f : F →+* F')
    (A : SpecialLinearGroup (Fin (n - 1)) F) :
    (minusLeviBlock A).map f = minusLeviBlock (Matrix.SpecialLinearGroup.map f A) := by
  rw [minusLeviBlock, minusLeviBlock, fromBlocks_map, fromBlocks_map, transpose_map, ← map_inv]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_zero _ f.map_zero,
    Matrix.map_one _ f.map_zero f.map_one]

end Block

section LeviGL

variable {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)

@[expose] noncomputable def minusLeviMat (A : SpecialLinearGroup (Fin (n - 1)) F) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) F :=
  reindex (minusIndexEquiv n hn) (minusIndexEquiv n hn) (minusLeviBlock A)

@[expose] noncomputable def minusLeviMatHom :
    SpecialLinearGroup (Fin (n - 1)) F →* Matrix (Fin (2 * n)) (Fin (2 * n)) F where
  toFun := minusLeviMat hn
  map_one' := by
    rw [minusLeviMat, minusLeviBlock_one, reindex_apply, submatrix_one_equiv]
  map_mul' A B := by
    rw [minusLeviMat, minusLeviMat, minusLeviMat, minusLeviBlock_mul, reindex_apply,
      reindex_apply, reindex_apply, submatrix_mul_equiv]

@[expose] noncomputable def minusLeviGL :
    SpecialLinearGroup (Fin (n - 1)) F →* GL (Fin (2 * n)) F :=
  (minusLeviMatHom hn).toHomUnits

theorem minusLeviGL_val (A : SpecialLinearGroup (Fin (n - 1)) F) :
    (minusLeviGL hn A).val = minusLeviMat hn A := rfl

theorem minusLeviGL_apply (A : SpecialLinearGroup (Fin (n - 1)) F)
    (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    (minusLeviGL hn A).val (minusIndexEquiv n hn x) (minusIndexEquiv n hn y) =
      minusLeviBlock A x y := by
  rw [minusLeviGL_val, minusLeviMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem minusLeviGL_map {F' : Type} [Field F'] (f : F →+* F')
    (A : SpecialLinearGroup (Fin (n - 1)) F) :
    (minusLeviGL hn A).val.map f = (minusLeviGL hn (Matrix.SpecialLinearGroup.map f A)).val := by
  rw [minusLeviGL_val, minusLeviGL_val, minusLeviMat, minusLeviMat, reindex_apply, reindex_apply,
    ← submatrix_map, minusLeviBlock_map]

theorem minusLeviGL_mulVec (A : SpecialLinearGroup (Fin (n - 1)) F) (v : Fin (2 * n) → F)
    (x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    ((minusLeviGL hn A).val *ᵥ v) (minusIndexEquiv n hn x) =
      (minusLeviBlock A *ᵥ (v ∘ minusIndexEquiv n hn)) x := by
  rw [minusLeviGL_val, minusLeviMat, reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_apply, Equiv.symm_apply_apply]

end LeviGL


section Derived

variable {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)

theorem dotProduct_mulVec_inv_transpose_mulVec (A : SpecialLinearGroup (Fin (n - 1)) F)
    (x y : Fin (n - 1) → F) :
    (A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) *ᵥ x ⬝ᵥ
        (((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) :
          Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ *ᵥ y) =
      x ⬝ᵥ y := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, vecMul_vecMul,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    vecMul_one, dotProduct_comm]

theorem minusLeviGL_mem_isometries (β γ : F) (A : SpecialLinearGroup (Fin (n - 1)) F) :
    minusLeviGL hn A ∈ matrixIsometries (coordinateQuadMinus n F hn β γ) := by
  rw [mem_matrixIsometries_iff]
  intro v
  have hl : ∀ i, ((minusLeviGL hn A).val *ᵥ v) (minusIndexEquiv n hn (.inl i)) =
      ((A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) *ᵥ
        fun l => v (minusIndexEquiv n hn (.inl l))) i := by
    intro i
    rw [minusLeviGL_mulVec, minusLeviBlock, fromBlocks_mulVec]
    simp only [Sum.elim_inl, zero_mulVec, add_zero]
    rfl
  have hr : ∀ i, ((minusLeviGL hn A).val *ᵥ v) (minusIndexEquiv n hn (.inr (.inl i))) =
      ((((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ) *ᵥ
        fun l => v (minusIndexEquiv n hn (.inr (.inl l)))) i := by
    intro i
    rw [minusLeviGL_mulVec, minusLeviBlock, fromBlocks_mulVec]
    simp only [Sum.elim_inr, zero_mulVec, zero_add]
    rw [fromBlocks_mulVec]
    simp only [Sum.elim_inl, zero_mulVec, add_zero]
    rfl
  have ha : ∀ r, ((minusLeviGL hn A).val *ᵥ v) (minusIndexEquiv n hn (.inr (.inr r))) =
      v (minusIndexEquiv n hn (.inr (.inr r))) := by
    intro r
    rw [minusLeviGL_mulVec, minusLeviBlock, fromBlocks_mulVec]
    simp only [Sum.elim_inr, zero_mulVec, zero_add]
    rw [fromBlocks_mulVec]
    simp only [Sum.elim_inr, zero_mulVec, zero_add, one_mulVec]
    rfl
  have key := dotProduct_mulVec_inv_transpose_mulVec A
    (fun l => v (minusIndexEquiv n hn (.inl l))) (fun l => v (minusIndexEquiv n hn (.inr (.inl l))))
  rw [matrixLinearEquiv_apply, coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp only [hl, hr, ha]
  rw [show (∑ i, ((A : Matrix (Fin (n - 1)) (Fin (n - 1)) F) *ᵥ
      fun l => v (minusIndexEquiv n hn (.inl l))) i *
      ((((A⁻¹ : SpecialLinearGroup (Fin (n - 1)) F) : Matrix (Fin (n - 1)) (Fin (n - 1)) F)ᵀ) *ᵥ
        fun l => v (minusIndexEquiv n hn (.inr (.inl l)))) i) =
      ∑ i, v (minusIndexEquiv n hn (.inl i)) * v (minusIndexEquiv n hn (.inr (.inl i))) from key]

theorem minusLeviGL_mem_derived (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤)
    (A : SpecialLinearGroup (Fin (n - 1)) F) :
    minusLeviGL hn A ∈ matrixDerived (coordinateQuadMinus n F hn β γ) := by
  have hle : (minusLeviGL hn).range ≤ matrixIsometries (coordinateQuadMinus n F hn β γ) := by
    rintro _ ⟨B, rfl⟩
    exact minusLeviGL_mem_isometries hn β γ B
  have hr : (minusLeviGL (F := F) hn).range =
      ⁅(minusLeviGL (F := F) hn).range, (minusLeviGL (F := F) hn).range⁆ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]
  have hA : minusLeviGL hn A ∈ (minusLeviGL hn).range := ⟨A, rfl⟩
  rw [hr] at hA
  exact Subgroup.commutator_mono hle hle hA

@[expose] noncomputable def minusLeviProj (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤) :
    SpecialLinearGroup (Fin (n - 1)) F →*
      matrixProjectiveDerived (coordinateQuadMinus n F hn β γ) :=
  (matrixProjectiveProjection _).comp
    ((minusLeviGL hn).codRestrict _ (minusLeviGL_mem_derived hn β γ hperf))

theorem minusLeviProj_apply (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤)
    (A : SpecialLinearGroup (Fin (n - 1)) F) :
    minusLeviProj hn β γ hperf A = matrixProjectiveProjection _
      ⟨minusLeviGL hn A, minusLeviGL_mem_derived hn β γ hperf A⟩ := rfl

theorem minusLeviProj_injective (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤) :
    Function.Injective (minusLeviProj hn β γ hperf) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [minusLeviProj_apply, matrixProjectiveProjection, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hA
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff _ _).1 hA
  have hent : ∀ x y, minusLeviBlock A x y = if x = y then (c : F) else 0 := by
    intro x y
    rw [← minusLeviGL_apply hn A x y]
    have h := congrArg (fun B : GL (Fin (2 * n)) F =>
      (B : Matrix (Fin (2 * n)) (Fin (2 * n)) F) (minusIndexEquiv n hn x)
        (minusIndexEquiv n hn y)) hc
    simp only [CFSG.RankThree.PartOne.KCOrthogonalSubfield.scalar_entry,
      (minusIndexEquiv n hn).injective.eq_iff] at h
    exact h.symm
  have hc1 : (c : F) = 1 := by
    have h := hent (.inr (.inr 0)) (.inr (.inr 0))
    simp only [minusLeviBlock_inr_inr, ↓reduceIte, Matrix.one_apply_eq] at h
    exact h.symm
  ext i j
  have h := hent (.inl i) (.inl j)
  rw [minusLeviBlock_inl_inl, hc1] at h
  simp only [Sum.inl.injEq] at h
  exact h.trans (by simp [Matrix.one_apply])

end Derived

section Compat

variable {n : ℕ} (hn : 1 ≤ n)

theorem fieldAutT_minusLeviProj {F : Type} [Field F] (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤) (σ : F ≃+* F)
    (hQσ : ∀ v, coordinateQuadMinus n F hn β γ (coordinateFieldMap (2 * n) σ v) =
      σ (coordinateQuadMinus n F hn β γ v))
    (A : SpecialLinearGroup (Fin (n - 1)) F) :
    fieldAutT (coordinateQuadMinus n F hn β γ) σ hQσ (minusLeviProj hn β γ hperf A) =
      minusLeviProj hn β γ hperf (Matrix.SpecialLinearGroup.map σ.toRingHom A) := by
  rw [minusLeviProj_apply, minusLeviProj_apply, fieldAutT_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_fieldPair_val]
  apply Units.ext
  rw [← minusLeviGL_map hn σ.toRingHom A]
  rfl

theorem incl_minusLeviProj {F : Type} [Field F] (k : Subfield F) (b c : k)
    (hk : commutator (SpecialLinearGroup (Fin (n - 1)) k) = ⊤)
    (hF : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤)
    (A : SpecialLinearGroup (Fin (n - 1)) k) :
    incl k (isExtension_coordinateQuadMinus k hn b c) (minusLeviProj hn b c hk A) =
      minusLeviProj hn (b : F) (c : F) hF (Matrix.SpecialLinearGroup.map k.subtype A) := by
  rw [minusLeviProj_apply, minusLeviProj_apply, incl_mk]
  congr 1
  apply Subtype.ext
  rw [inclHom_val]
  apply Units.ext
  rw [glIncl_val]
  exact minusLeviGL_map hn k.subtype A

theorem minusCongr_minusLeviProj {K k : Type} [Field K] [Field k] (φ : K ≃+* k) (b c : K)
    (hK : commutator (SpecialLinearGroup (Fin (n - 1)) K) = ⊤)
    (hk : commutator (SpecialLinearGroup (Fin (n - 1)) k) = ⊤)
    (A : SpecialLinearGroup (Fin (n - 1)) K) :
    minusCongr φ hn b c (minusLeviProj hn b c hK A) =
      minusLeviProj hn (φ b) (φ c) hk (Matrix.SpecialLinearGroup.map φ.toRingHom A) := by
  rw [minusLeviProj_apply, minusLeviProj_apply]
  apply matrixProjectiveCongr_mk
  apply Units.ext
  rw [glCongr_coe]
  exact (minusLeviGL_map hn φ.toRingHom A).symm

end Compat

section SL2

theorem commutator_SL2_eq_top_of_charTwo {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 3 ≤ Nat.card F) : commutator (SpecialLinearGroup (Fin 2) F) = ⊤ := by
  obtain ⟨a, ha⟩ := exists_units_ne_one (K := F) hF
  refine Matrix.SL2.commutator_eq_top a.ne_zero fun h => ha (Units.ext ?_)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h0 : ((a : F) - 1) ^ 2 = 0 := by linear_combination h + (1 - (a : F)) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

end SL2

section Root

variable {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)

theorem projHom_frameRootElt_eq_minusLeviProj (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤) {p q : Fin (n - 1)}
    (hpq : p ≠ q) (c : F)
    (hG : frameRootElt (coordinateQuadMinus n F hn β γ) (minusFrameLeft hn) (minusFrameRight hn)
      p q c ∈ orthDerived (coordinateQuadMinus n F hn β γ)) :
    projHom _ ⟨_, hG⟩ =
      minusLeviProj hn β γ hperf (Matrix.SpecialLinearGroup.transvection hpq (-c)) := by
  rw [minusLeviProj_apply]
  change matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, hG⟩) = _
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain ⟨x, rfl⟩ := (minusIndexEquiv n hn).surjective i
  obtain ⟨y, rfl⟩ := (minusIndexEquiv n hn).surjective j
  rw [derivedEquiv_symm_entry]
  change _ = (minusLeviGL hn _).val _ _
  rw [minusLeviGL_apply, (isHypFrame_minus F hn β γ).frameRootElt_apply_coord hpq]
  simp only [minusFrameLeft, minusFrameRight, Pi.single_apply,
    (minusIndexEquiv n hn).injective.eq_iff]
  have hinv : ((Matrix.SpecialLinearGroup.transvection hpq (-c))⁻¹ :
      SpecialLinearGroup (Fin (n - 1)) F) = Matrix.SpecialLinearGroup.transvection hpq c := by
    rw [Matrix.SpecialLinearGroup.transvection_inv, neg_neg]
  rcases x with i | i | r <;> rcases y with j | j | s
  · rw [minusLeviBlock_inl_inl, Matrix.SpecialLinearGroup.transvection_coe]
    simp only [Sum.inl.injEq, reduceCtorEq, ↓reduceIte, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    by_cases hi : i = p
    · subst hi
      by_cases hj : j = i
      · subst hj
        simp [Ne.symm hpq]
      · by_cases hjq : j = q
        · subst hjq
          simp [Ne.symm hj]
        · simp [Ne.symm hj, Ne.symm hjq]
    · simp [hi, Ne.symm hi]
  · simp only [Sum.inl.injEq, reduceCtorEq, ↓reduceIte, mul_zero, sub_zero]
    simp [minusLeviBlock, fromBlocks_apply₁₂]
  · simp only [Sum.inl.injEq, reduceCtorEq, ↓reduceIte, mul_zero, sub_zero]
    simp [minusLeviBlock, fromBlocks_apply₁₂]
  · simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
    simp [minusLeviBlock, fromBlocks_apply₂₁]
  · rw [minusLeviBlock_inr_inl, hinv, Matrix.SpecialLinearGroup.transvection_coe]
    simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    by_cases hi : i = q
    · subst hi
      by_cases hj : j = i
      · subst hj
        simp [hpq]
      · by_cases hjp : j = p
        · subst hjp
          simp [hj, Ne.symm hj]
        · simp [hj, Ne.symm hj, Ne.symm hjp]
    · rcases eq_or_ne i j with rfl | hij
      · simp [hi, Ne.symm hi]
      · simp [hi, Ne.symm hi, hij, Ne.symm hij]
  · simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
    simp [minusLeviBlock, fromBlocks_apply₂₂, fromBlocks_apply₁₂]
  · simp only [Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
    simp [minusLeviBlock, fromBlocks_apply₂₁]
  · simp only [Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
    simp [minusLeviBlock, fromBlocks_apply₂₂, fromBlocks_apply₂₁]
  · rw [minusLeviBlock_inr_inr]
    simp only [Sum.inr.injEq, reduceCtorEq, ↓reduceIte, Matrix.one_apply]

theorem commute_frameHom_minusLeviProj [Finite F] [CharP F 2] (β γ : F)
    (hperf : commutator (SpecialLinearGroup (Fin (n - 1)) F) = ⊤) {s : Fin (n - 1) → Fˣ}
    (hs : ∀ i j, s i = s j) (A : SpecialLinearGroup (Fin (n - 1)) F) :
    Commute ((isHypFrame_minus F hn β γ).frameHom s) (minusLeviProj hn β γ hperf A) := by
  have hX := derivedEquiv_symm_frameLin_entry (isHypFrame_minus F hn β γ) s
  rw [IsHypFrame.frameHom_apply, minusLeviProj_apply]
  change Commute (matrixProjectiveProjection _ ((derivedEquiv _).symm ⟨_, _⟩)) _
  apply Commute.map
  set X := (derivedEquiv (coordinateQuadMinus n F hn β γ)).symm
    ⟨frameLin (minusFrameLeft hn) (minusFrameRight hn) s,
      (isHypFrame_minus F hn β γ).frameLin_mem_orthDerived s⟩ with hXdef
  have hXd : (X : GL (Fin (2 * n)) F).val =
      Matrix.diagonal fun i => ((frameEntry (minusFrameLeft hn) (minusFrameRight hn) s i : Fˣ) :
        F) := by
    ext i j
    rw [hX, Matrix.diagonal_apply]
  have hl : ∀ i, frameEntry (minusFrameLeft hn) (minusFrameRight hn) s
      (minusIndexEquiv n hn (.inl i)) = s i :=
    (isHypFrame_minus F hn β γ).frameEntry_left s
  have hr : ∀ i, frameEntry (minusFrameLeft hn) (minusFrameRight hn) s
      (minusIndexEquiv n hn (.inr (.inl i))) = (s i)⁻¹ :=
    (isHypFrame_minus F hn β γ).frameEntry_right s
  have ha : ∀ r, frameEntry (minusFrameLeft hn) (minusFrameRight hn) s
      (minusIndexEquiv n hn (.inr (.inr r))) = 1 := fun r =>
    frameEntry_of_forall_ne s (fun k h => by
      have := (minusIndexEquiv n hn).injective h
      simp at this) (fun k h => by
      have := (minusIndexEquiv n hn).injective h
      simp at this)
  change X * _ = _ * X
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hXd]
  ext i j
  obtain ⟨x, rfl⟩ := (minusIndexEquiv n hn).surjective i
  obtain ⟨y, rfl⟩ := (minusIndexEquiv n hn).surjective j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, minusLeviGL_apply]
  rcases x with i | i | r <;> rcases y with j | j | t
  · rw [hl, hl, hs i j, mul_comm]
  · simp [minusLeviBlock, fromBlocks_apply₁₂]
  · simp [minusLeviBlock, fromBlocks_apply₁₂]
  · simp [minusLeviBlock, fromBlocks_apply₂₁]
  · rw [hr, hr, hs i j, mul_comm]
  · simp [minusLeviBlock, fromBlocks_apply₂₂, fromBlocks_apply₁₂]
  · simp [minusLeviBlock, fromBlocks_apply₂₁]
  · simp [minusLeviBlock, fromBlocks_apply₂₂, fromBlocks_apply₂₁]
  · rw [ha, ha, mul_comm]

end Root

end CFSG.SeitzReduction.OmegaPilot

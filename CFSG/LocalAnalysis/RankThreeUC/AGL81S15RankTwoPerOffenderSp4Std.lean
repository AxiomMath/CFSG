module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderNat
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

private noncomputable def sp4std_transv {F : Type} [Field F] [CharP F 2]
    (v : Fin 4 → F) (t : F) : GL (Fin 4) F :=
  GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
    (minorForm F) minorForm_isAlt v t)

private theorem sp4std_glMat_transv {F : Type} [Field F] [CharP F 2]
    (v : Fin 4 → F) (t : F) : glMat (sp4std_transv v t) = transvMat v t :=
  glMat_transvection v t

private theorem sp4std_transv_mem {F : Type} [Field F] [CharP F 2]
    (v : Fin 4 → F) (t : F) : sp4std_transv v t ∈ antiSp F := by
  rw [antiSp_eq_closure (K := F)]
  exact Subgroup.subset_closure ⟨v, t, rfl⟩

private theorem sp4std_transvMat_mulVec {F : Type} [Field F]
    (v : Fin 4 → F) (t : F) (x : Fin 4 → F) :
    transvMat v t *ᵥ x = x + (t * minorForm F x v) • v := by
  ext i
  fin_cases i <;>
    simp [transvMat, minorForm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

private theorem sp4std_exists_minorForm_eq_one {F : Type} [Field F]
    (v : Fin 4 → F) (hv : v ≠ 0) : ∃ x : Fin 4 → F, minorForm F x v = 1 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
    by_contra h
    apply hv
    ext j
    exact not_not.mp (not_exists.mp h j)
  refine ⟨Pi.single (3 - i) ((v i)⁻¹), ?_⟩
  rw [minorForm_apply]
  fin_cases i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne]
  all_goals exact inv_mul_cancel₀ (by simpa using hi)

private theorem sp4std_eq_smul_one_of_mulVec {F : Type} [Field F]
    {P : Matrix (Fin 4) (Fin 4) F} {lam : F}
    (h : ∀ u, P *ᵥ u = lam • u) : P = lam • (1 : Matrix (Fin 4) (Fin 4) F) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact h u

theorem natSchur_antiSp {F : Type} [Field F] [CharP F 2] : NatSchur (antiSp F).subtype := by
  intro c hc
  have hstar : ∀ (x v : Fin 4 → F) (t : F),
      c ((t * minorForm F x v) • v) = (t * minorForm F (c x) v) • v := by
    intro x v t
    have hmem := sp4std_transv_mem v t
    have hcT := hc ⟨sp4std_transv v t, hmem⟩ x
    change c (glMat (sp4std_transv v t) *ᵥ x) = glMat (sp4std_transv v t) *ᵥ c x at hcT
    rw [sp4std_glMat_transv, sp4std_transvMat_mulVec v t x,
      sp4std_transvMat_mulVec v t (c x), map_add c] at hcT
    exact add_left_cancel hcT
  have heig : ∀ v : Fin 4 → F, ∃ f : F, c v = f • v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      exact ⟨0, by simp⟩
    · obtain ⟨x, hx⟩ := sp4std_exists_minorForm_eq_one v hv
      refine ⟨minorForm F (c x) v, ?_⟩
      have h := hstar x v 1
      simpa only [hx, one_mul, one_smul] using h
  have hlin : ∀ (t : F) (v : Fin 4 → F), c (t • v) = t • c v := by
    intro t v
    by_cases hv : v = 0
    · subst hv
      simp
    · obtain ⟨x, hx⟩ := sp4std_exists_minorForm_eq_one v hv
      have h1 : c (t • v) = (t * minorForm F (c x) v) • v := by
        have h := hstar x v t
        simpa only [hx, mul_one] using h
      have h2 : c v = minorForm F (c x) v • v := by
        have h := hstar x v 1
        simpa only [hx, one_mul, one_smul] using h
      rw [h1, h2, smul_smul]
  let φ : (Fin 4 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := c
      map_add' := fun a b => map_add c a b
      map_smul' := fun t v => hlin t v }
  obtain ⟨lam, hlam⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := φ) (fun v hli => by
      obtain ⟨f, hf⟩ := heig v
      have hφv : φ v = f • v := hf
      have h0 : f • v + (-1 : F) • φ v = 0 := by rw [hφv]; simp
      have h1 := LinearIndependent.pair_iff.1 hli f (-1) h0
      exact absurd h1.2 (by simp))
  refine ⟨lam, fun u => ?_⟩
  have hthis : φ u = lam • u := by
    simpa using congrArg (fun f : (Fin 4 → F) →ₗ[F] (Fin 4 → F) => f u) hlam
  rw [show c u = φ u from rfl]
  exact hthis

theorem natOut_antiSp {F : Type} [Field F] [CharP F 2] : NatOut (antiSp F).subtype := by
  intro M hM hnorm
  let Mm : Matrix (Fin 4) (Fin 4) F := (M : Matrix (Fin 4) (Fin 4) F)
  let Mmi : Matrix (Fin 4) (Fin 4) F := (M⁻¹ : Matrix (Fin 4) (Fin 4) F)
  let J : Matrix (Fin 4) (Fin 4) F := minorJ F
  have hMm : Mm = (M : Matrix (Fin 4) (Fin 4) F) := rfl
  have hMmi : Mmi = (M⁻¹ : Matrix (Fin 4) (Fin 4) F) := rfl
  have hJeq : J = minorJ F := rfl
  have hJmul : J * J = 1 := minorJ_mul_self
  have hMM : Mm * Mm = 1 := by
    have h := congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hM
    rw [hMm]
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one] using h
  have hMiM : Mmi * Mm = 1 := by
    rw [hMmi, hMm]
    simp
  have hA : Mmᵀ * Mmiᵀ = 1 := by
    rw [← transpose_mul, hMiM, transpose_one]
  let Q : Matrix (Fin 4) (Fin 4) F := Mmᵀ * J * Mm
  let P : Matrix (Fin 4) (Fin 4) F := J * Q
  have hQ : Q = Mmᵀ * J * Mm := rfl
  have hP : P = J * Q := rfl
  have hCm : ∀ l : ↥(antiSp F), (glMat l)ᵀ * Q * glMat l = Q := by
    intro l
    obtain ⟨l', hl'⟩ := hnorm l
    have hl'' : (l' : GL (Fin 4) F) = M * (l : GL (Fin 4) F) * M⁻¹ := by
      simpa using hl'
    have hcoeeq : glMat (l' : GL (Fin 4) F) = Mm * glMat l * Mmi := by
      rw [hl'', hMm, hMmi]
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
    have hconj' := mem_antiSp.mp l'.2
    rw [hcoeeq] at hconj'
    have hconj : Mmiᵀ * (glMat l)ᵀ * Mmᵀ * J * Mm * glMat l * Mmi = J := by
      rw [hJeq]
      simpa only [transpose_mul, Matrix.mul_assoc] using hconj'
    calc (glMat l)ᵀ * Q * glMat l
        = (glMat l)ᵀ * (Mmᵀ * J * Mm) * glMat l := by rw [hQ]
      _ = (Mmᵀ * Mmiᵀ) * (glMat l)ᵀ * (Mmᵀ * J * Mm) * (glMat l * (Mmi * Mm)) := by
            rw [hA, hMiM]; simp
      _ = Mmᵀ * (Mmiᵀ * (glMat l)ᵀ * Mmᵀ * J * Mm * glMat l * Mmi) * Mm := by
            simp only [Matrix.mul_assoc]
      _ = Mmᵀ * J * Mm := by rw [hconj]
      _ = Q := by rw [hQ]
  have hPcomm : ∀ l : ↥(antiSp F), P * glMat l = glMat l * P := by
    intro l
    have hJ : glMat l * J * (glMat l)ᵀ = J := by
      rw [hJeq]
      exact mul_minorJ_mul_transpose_of_mem l.2
    calc P * glMat l
        = J * Q * glMat l := by rw [hP]
      _ = (glMat l * J * (glMat l)ᵀ) * Q * glMat l := by rw [hJ]
      _ = glMat l * J * ((glMat l)ᵀ * Q * glMat l) := by simp only [Matrix.mul_assoc]
      _ = glMat l * J * Q := by rw [hCm l]
      _ = glMat l * (J * Q) := by simp only [Matrix.mul_assoc]
      _ = glMat l * P := by rw [hP]
  let cP : (Fin 4 → F) →+ (Fin 4 → F) :=
    { toFun := fun u => P *ᵥ u
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.mulVec_add] }
  have hcP : ∀ (l : ↥(antiSp F)) (u : Fin 4 → F),
      cP (((antiSp F).subtype l : Matrix (Fin 4) (Fin 4) F) *ᵥ u) =
        ((antiSp F).subtype l : Matrix (Fin 4) (Fin 4) F) *ᵥ cP u := by
    intro l u
    show P *ᵥ (glMat l *ᵥ u) = glMat l *ᵥ (P *ᵥ u)
    calc P *ᵥ (glMat l *ᵥ u)
        = (P * glMat l) *ᵥ u := Matrix.mulVec_mulVec u P (glMat l)
      _ = (glMat l * P) *ᵥ u := by rw [hPcomm l]
      _ = glMat l *ᵥ (P *ᵥ u) := (Matrix.mulVec_mulVec u (glMat l) P).symm
  obtain ⟨lam, hlam⟩ := natSchur_antiSp (F := F) cP hcP
  have hPscalar : P = lam • (1 : Matrix (Fin 4) (Fin 4) F) :=
    sp4std_eq_smul_one_of_mulVec hlam
  have hQscalar : Q = lam • J := by
    calc Q = J * P := by rw [hP, ← Matrix.mul_assoc, hJmul, Matrix.one_mul]
      _ = J * (lam • 1) := by rw [hPscalar]
      _ = lam • J := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hQ1 : Mmᵀ * J * Mm = lam • J := by rw [← hQ, hQscalar]
  have hsq : lam * lam = 1 := by
    have h1 : Mmᵀ * Q * Mm = J := by
      calc Mmᵀ * Q * Mm
          = (Mm * Mm)ᵀ * J * (Mm * Mm) := by
              rw [hQ, transpose_mul]
              simp only [Matrix.mul_assoc]
        _ = J := by rw [hMM, transpose_one, Matrix.one_mul, Matrix.mul_one]
    have h2 : Mmᵀ * Q * Mm = (lam * lam) • J := by
      rw [hQscalar, Matrix.mul_smul, Matrix.smul_mul, hQ1, smul_smul]
    have h3 : J = (lam * lam) • J := h1.symm.trans h2
    have h4 : (1 : F) = lam * lam := by
      have h := congrFun (congrFun h3 (0 : Fin 4)) (3 : Fin 4)
      simpa [J, minorJ_apply, Pi.smul_apply, smul_eq_mul] using h
    exact h4.symm
  have hlam1 : lam = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h5 : (lam - 1) * (lam - 1) = 0 := by
      linear_combination hsq + (1 - lam) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h5)
  have hJfinal : Mmᵀ * J * Mm = J := by
    rw [hQ1, hlam1, one_smul]
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [mem_antiSp]
  show Mmᵀ * J * Mm = J
  exact hJfinal

end CFSG.LocalAnalysis.RankThreeUC.S15

end
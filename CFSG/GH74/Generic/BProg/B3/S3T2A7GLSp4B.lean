module

public import CFSG.GH74.Generic.Front.SpFld

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical.SteinbergBY
open CFSG.GH74.Filter.ClassicalOdd

variable {F : Type} [Field F]

theorem embedSp_injective {K : Type} [Field K] (f : K →+* F) :
    Function.Injective (embedSp f) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrArg (fun k : StatedSp 2 F =>
    ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j) hgh
  simp only [coe_embedSp, Matrix.map_apply] at this
  exact f.injective this

theorem exists_q8q8_fixed [Finite F] (hF : Odd (Nat.card F)) (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ * σ = 1) (A : gsp 2 F) (c : F)
    (hAσ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ = c • 1) :
    ∃ φ : Q8 × Q8 →* StatedSp 2 F, Function.Injective φ ∧
      ∀ g, (conjSp 2 F A * fieldSp 2 F σ) (φ g) = φ g := by
  classical
  obtain ⟨M, t, hh⟩ := exists_conj_to_field σ hσ1 hσ2 A c hAσ
  have hinv : gspFieldMap σ M⁻¹ = (gspFieldMap σ M)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← gspFieldMap_mul, mul_inv_cancel, gspFieldMap_one_right])
  have hA' : A = M * gspFieldMap σ M⁻¹ * scalarGsp t := by
    rw [hinv]
    calc A = (A * gspFieldMap σ M) * (gspFieldMap σ M)⁻¹ := by group
      _ = M * scalarGsp t * (gspFieldMap σ M)⁻¹ := by rw [hh]
      _ = M * (gspFieldMap σ M)⁻¹ * scalarGsp t := by
          rw [mul_assoc M (scalarGsp t), scalarGsp_mul_comm, ← mul_assoc]
  have hconj : conjSp 2 F A * fieldSp 2 F σ =
      conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F M)⁻¹ := by
    have hcA : conjSp 2 F A = conjSp 2 F M * conjSp 2 F (gspFieldMap σ M⁻¹) := by
      rw [hA', map_mul, map_mul, conjSp_scalarGsp, mul_one]
    calc conjSp 2 F A * fieldSp 2 F σ
        = conjSp 2 F M * conjSp 2 F (gspFieldMap σ M⁻¹) * fieldSp 2 F σ := by rw [hcA]
      _ = conjSp 2 F M * (fieldSp 2 F σ * conjSp 2 F M⁻¹) := by
          rw [fieldSp_mul_conjSp, mul_assoc]
      _ = conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F M)⁻¹ := by rw [map_inv, mul_assoc]
  set F₀ := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ with hF₀def
  have hrank := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield_finrank F σ
    (by rw [pow_two]; exact hσ2) hσ1
  have hcardF : Nat.card F = Nat.card ↥F₀ ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ↥F₀) (V := F), hrank]
  have hF₀ : Odd (Nat.card ↥F₀) := by
    have h2 : Odd (Nat.card ↥F₀ * Nat.card ↥F₀) := by rw [← pow_two, ← hcardF]; exact hF
    exact (Nat.odd_mul.1 h2).1
  have hch : ringChar ↥F₀ ≠ 2 := ringChar_ne_two_of_two_ne_zero (two_ne_zero_of_odd_card hF₀)
  obtain ⟨φ₀, hφ₀, -⟩ := exists_q8q8_Sp4 (F := ↥F₀) hch
  have hfix : ∀ k : StatedSp 2 ↥F₀,
      fieldSp 2 F σ (embedSp F₀.subtype k) = embedSp F₀.subtype k := by
    intro k
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp, coe_embedSp]
    ext i j
    simp only [Matrix.map_apply]
    exact (CFSG.ComponentClassification.CatalogueBLinearTwoDescent.mem_fixedSubfield F σ _).1
      (((k : GL (Fin 2 ⊕ Fin 2) ↥F₀) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F₀) i j).2
  refine ⟨(conjSp 2 F M).toMonoidHom.comp ((embedSp F₀.subtype).comp φ₀),
    (conjSp 2 F M).injective.comp ((embedSp_injective F₀.subtype).comp hφ₀), fun g => ?_⟩
  change (conjSp 2 F A * fieldSp 2 F σ) (conjSp 2 F M (embedSp F₀.subtype (φ₀ g))) =
    conjSp 2 F M (embedSp F₀.subtype (φ₀ g))
  have hy : ((conjSp 2 F M)⁻¹ : MulAut ↥(StatedSp 2 F))
      ((conjSp 2 F M) (embedSp F₀.subtype (φ₀ g))) = embedSp F₀.subtype (φ₀ g) := by simp
  rw [hconj, MulAut.mul_apply, MulAut.mul_apply, hy, hfix]

end CFSG.GH74.Generic.BProg.B3.S3T2A7.GLR

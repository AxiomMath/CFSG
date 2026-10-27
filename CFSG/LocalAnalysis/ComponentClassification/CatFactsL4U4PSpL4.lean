module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpCore
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DarbouxL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks4
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace PSpL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag Blocks HBlocks StabL
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem reindex_gram : reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = omg := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omg, fromBlocks, finSumFinEquiv, Fin.addCases, Fin.castLT]

@[expose] noncomputable def spGL (R : Type) [Field R] : StatedSp 2 R →* GL (Fin 4) R :=
  (Units.map (Matrix.reindexAlgEquiv R R finSumFinEquiv).toMonoidHom).comp (StatedSp 2 R).subtype

theorem coe_spGL (R : Type) [Field R] (M : StatedSp 2 R) :
    ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) =
      reindex finSumFinEquiv finSumFinEquiv ((M : GL (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := rfl

theorem spGL_spec (R : Type) [Field R] (M : StatedSp 2 R) :
    ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R)ᵀ * omg *
        ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = omg ∧
      ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R).det = 1 := by
  have hM : ((M : GL (Fin 2 ⊕ Fin 2) R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) ∈
      symplecticGroup (Fin 2) R :=
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp
      ((ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := R)).le M.2)
  have hJ := (ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr hM
  have hr : ∀ X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R,
      reindex finSumFinEquiv finSumFinEquiv X * reindex finSumFinEquiv finSumFinEquiv Y =
        reindex finSumFinEquiv finSumFinEquiv (X * Y) := fun X Y =>
    ((Matrix.reindexAlgEquiv R R finSumFinEquiv).map_mul X Y).symm
  rw [coe_spGL]
  refine ⟨?_, by rw [det_reindex_self]; exact SymplecticGroup.det_eq_one hM⟩
  rw [← reindex_gram, transpose_reindex, hr, hr, hJ]

theorem mem_statedScalars_of_spGL {R : Type} [Field R] {M : StatedSp 2 R} {c : R}
    (hc : ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = c • 1) :
    (M : GL (Fin 2 ⊕ Fin 2) R) ∈ StatedScalars (Fin 2 ⊕ Fin 2) R := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := (spGL_spec R M).2
    rw [hc, zero_smul, det_zero] at this
    exact zero_ne_one this
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
  apply (reindex finSumFinEquiv finSumFinEquiv).injective
  rw [← coe_spGL, hc]
  ext i j
  simp [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem spGL_of_mem_statedScalars {R : Type} [Field R] {M : StatedSp 2 R}
    (hM : (M : GL (Fin 2 ⊕ Fin 2) R) ∈ StatedScalars (Fin 2 ⊕ Fin 2) R) :
    ∃ c : Rˣ, ((spGL R M : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = (c : R) • 1 := by
  obtain ⟨c, hc⟩ := hM
  refine ⟨c, ?_⟩
  rw [coe_spGL, ← hc, GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.smul_apply, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem formA_eq : (formA : Matrix (Fin 4) (Fin 4) F) =
    (Matrix.diagonal ![1, 1, 1, -1])ᵀ * omg * Matrix.diagonal ![1, 1, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formA, omg, Matrix.mul_apply, Matrix.diagonal_apply]

theorem exists_transpose_mul_mul_eq_omg (h2 : (2 : F) ≠ 0) {R : Matrix (Fin 4) (Fin 4) F}
    (hR : Rᵀ = -R) (hRu : IsUnit R.det) :
    ∃ P : GL (Fin 4) F, (P : Matrix (Fin 4) (Fin 4) F)ᵀ * R * (P : Matrix (Fin 4) (Fin 4) F) =
      omg := by
  obtain ⟨P, hPu, hP⟩ := exists_transpose_mul_mul_eq_formA h2 hR hRu
  set D : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal ![1, 1, 1, -1] with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hDt : Dᵀ = D := by rw [hD, Matrix.diagonal_transpose]
  have hdet : IsUnit (P * D).det := by
    rw [det_mul]
    refine hPu.mul ?_
    rw [hD, det_diagonal, Fin.prod_univ_four]
    simp
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (P * D) hdet.ne_zero, ?_⟩
  rw [GeneralLinearGroup.val_mkOfDetNeZero]
  calc (P * D)ᵀ * R * (P * D) = Dᵀ * (Pᵀ * R * P) * D := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Dᵀ * (Dᵀ * omg * D) * D := by rw [hP, formA_eq]
    _ = omg := by
        rw [hDt]
        calc D * (D * omg * D) * D = (D * D) * omg * (D * D) := by simp only [Matrix.mul_assoc]
          _ = omg := by rw [hDD, Matrix.one_mul, Matrix.mul_one]

variable [Fintype F]

theorem exists_psp_of_alt_L4 (hF : Fintype.card F % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card F = p ^ f) (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ M : Subgroup (projectiveSL 4 F), (∀ y ∈ M, (conjAut 4 F A * dualAut 4 F) y = y) ∧
      Blueprint.LieModel ↥M .PSp 2 p f := by
  classical
  have h2 := two_ne_zero_of_card_mod_four hF
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin 4) (Fin 4) F) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  obtain ⟨P, hP⟩ := exists_transpose_mul_mul_eq_omg h2 hRt hRu
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let ι : StatedSp 2 F →* SpecialLinearGroup (Fin 4) F :=
    { toFun := fun M => ⟨((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
        by
          rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul,
            (spGL_spec F M).2, mul_one, ← det_mul, hPP, det_one]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun M N => by
        apply Subtype.ext
        show ((MulAut.conj P (spGL F (M * N)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((MulAut.conj P (spGL F N) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        rw [map_mul, map_mul, Units.val_mul] }
  have hι : ∀ M, (ι M : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := fun M => by
    change ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
  set φ := (proj 4 F).comp ι with hφ
  refine ⟨φ.range, ?_, ?_⟩
  · rintro _ ⟨M, rfl⟩
    rw [hφ, MonoidHom.comp_apply]
    apply conjAut_dualAut_proj_of_transpose_mul_mul A
    rw [hι]
    apply conj_transpose_mul_mul hPP
    rw [← hRdef, hP]
    exact (spGL_spec F M).1
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · rw [Nat.card_eq_fintype_card, pow_zero] at hK
        omega
      · exact h
    refine lieModel_range_of_ker hp hf hK (fun h => ?_) φ ?_
    · rw [← hK, Nat.card_eq_fintype_card] at h
      omega
    · ext M
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars,
        Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨c, -, hc⟩
        apply mem_statedScalars_of_spGL (c := (c : F))
        have e1 : (P : Matrix (Fin 4) (Fin 4) F) *
            ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
          rw [← hι, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
        have hPi : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        calc ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * ((P : Matrix (Fin 4) (Fin 4) F) *
              ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
                (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) := by
              simp only [← Matrix.mul_assoc]
              rw [hPi, Matrix.one_mul, Matrix.mul_assoc, hPi, Matrix.mul_one]
          _ = (c : F) • 1 := by
              rw [e1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPi]
      · intro hM
        obtain ⟨c, hc⟩ := spGL_of_mem_statedScalars hM
        refine ⟨c, ?_, ?_⟩
        · have hd := (spGL_spec F M).2
          rw [hc, det_smul, det_one, mul_one, Fintype.card_fin] at hd
          exact Units.ext (by rw [Units.val_pow_eq_pow_val, hd, Units.val_one])
        · rw [hι, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP, Matrix.scalar_apply,
            Matrix.smul_one_eq_diagonal]

end PSpL

end CFSG.ComponentClassification.CatFactsL4U4

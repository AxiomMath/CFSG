module

public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4LinNSL
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4Shape
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4PSL
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.L4U4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open CFSG.ComponentClassification.CatFactsL4U4
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem exists_smul_of_proj_comm {X Z : SL(4, K)}
    (hc : proj 4 K X * proj 4 K Z = proj 4 K Z * proj 4 K X) :
    ∃ c : K, (X : Matrix (Fin 4) (Fin 4) K) * Z = c • ((Z : Matrix (Fin 4) (Fin 4) K) * X) := by
  have h1 : proj 4 K (Z * X) = proj 4 K (X * Z) := by rw [map_mul, map_mul, hc]
  obtain ⟨c, hc'⟩ := InvClassL.eq_smul_of_proj_eq h1
  exact ⟨c, by simpa only [Matrix.SpecialLinearGroup.coe_mul] using hc'⟩

theorem normalSimpleShape_of_nonsquare (hK : ringChar K ≠ 2) {g : SL(4, K)} {c : K}
    (hc0 : c ≠ 0) (hsq : ¬ IsSquare c) (hg : (g : Matrix (Fin 4) (Fin 4) K) * g = c • 1) :
    NormalSimpleShape (projectiveSL 4 K) (proj 4 K g) := by
  set μ : Kˣ := Units.mk0 c hc0 with hμ
  have : Fact (¬ IsSquare (μ : K)) := ⟨by simpa [hμ] using hsq⟩
  have hB2 : Matrix.SpecialLinearGroup.toGL g ^ 2 = GeneralLinearGroup.scalar (Fin 4) μ := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hg,
      GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal, hμ, Units.val_mk0]
  have hd : (letI := matrixModule (Matrix.SpecialLinearGroup.toGL g) μ hB2;
      Module.finrank (extension (μ : K)) (Fin 4 → K) = 2) := by
    have h := matrixDimension_twice (Matrix.SpecialLinearGroup.toGL g) μ hB2
    rw [Fintype.card_fin] at h
    change matrixDimension (Matrix.SpecialLinearGroup.toGL g) μ hB2 = 2
    omega
  set Ψ := rowSPsi hB2 hd with hΨ
  have hU : rowSU μ Ψ = Matrix.SpecialLinearGroup.toGL g := rowSU_rowSPsi hB2 hd
  have : Finite (extension (μ : K)) :=
    CFSG.ComponentClassification.CatalogueBProjectiveInvolution.quadraticExtension_finite _
  have h4 : 4 ≤ Nat.card (extension (μ : K)) := by
    rw [card_extension]
    have : 3 ≤ Nat.card K := ProjectiveEigenspace.three_le_card_of_two_ne_zero (Ring.two_ne_zero hK)
    nlinarith
  set φ := (proj 4 K).comp (rowSPiSL μ Ψ) with hφ
  have hker := ker_proj_rowSPiSL μ Ψ
  refine ⟨φ.range, ?_, ?_, isSimpleGroup_range_of_ker_eq_center h4 φ hker,
    isPerfect_range_of_ker_eq_center h4 φ hker, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, toGL_rowSPiSL, ← hU]
    exact rowSPi_commute_rowSU μ Ψ _
  · refine le_normalizer_of_forall_conj fun y hy x hx => ?_
    obtain ⟨Y, rfl⟩ := proj_surjective 4 K y
    obtain ⟨x, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    obtain ⟨ζ, hζ⟩ := exists_smul_of_proj_comm hy
    have hζ' : ((Matrix.SpecialLinearGroup.toGL Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (g : Matrix (Fin 4) (Fin 4) K) =
        ζ • ((g : Matrix (Fin 4) (Fin 4) K) * (Matrix.SpecialLinearGroup.toGL Y :
          GL (Fin 4) K)) := by
      simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hζ
    have hζ1 := eq_one_or_eq_neg_one_of_mul_eq_smul hc0 hg hζ'
    obtain ⟨x', hx'⟩ := exists_conj_rowSPi μ Ψ hζ1 (Y := Matrix.SpecialLinearGroup.toGL Y)
      (by rw [hU]; simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hζ) x
    refine ⟨x', ?_⟩
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, toGL_rowSPiSL, toGL_rowSPiSL, hx']
  · intro a ha b hb _ _
    obtain ⟨Y, rfl⟩ := proj_surjective 4 K a
    obtain ⟨Y', rfl⟩ := proj_surjective 4 K b
    have hcomm : ∀ Z : SL(4, K), proj 4 K Z ∈ Subgroup.centralizer (φ.range : Set _) →
        ∀ x : SL(2, extension (μ : K)), ∃ c : Kˣ,
          Matrix.SpecialLinearGroup.toGL Z * rowSPi μ Ψ (Matrix.SpecialLinearGroup.toGL x) =
            GeneralLinearGroup.scalar (Fin 4) c * rowSPi μ Ψ (Matrix.SpecialLinearGroup.toGL x) *
              Matrix.SpecialLinearGroup.toGL Z := by
      intro Z hZ x
      have hmem := Subgroup.mem_centralizer_iff.mp hZ _ ⟨x, rfl⟩
      obtain ⟨d, hd⟩ := exists_smul_of_proj_comm (X := Z) (Z := rowSPiSL μ Ψ x) hmem.symm
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_smul, ← Matrix.SpecialLinearGroup.coe_mul] at hd
        have := congrArg Matrix.det hd
        rw [(Z * rowSPiSL μ Ψ x).2, det_zero] at this
        exact one_ne_zero this
      refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply,
        ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact hd
    have hYY := comm_of_forall_rowSPi μ Ψ (hcomm Y ha) (hcomm Y' hb)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul]
    exact hYY

end CFSG.ClassicalInvolution.Q3.TA3.L4U4

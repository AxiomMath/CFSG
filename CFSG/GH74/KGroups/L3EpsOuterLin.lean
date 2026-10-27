module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.GH74.KGroups.L3EpsLin

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

theorem exists_sl_of_sq_scalar' (A : GL (Fin 3) F) (c : Fˣ)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (c : F) • 1) :
    ∃ Asl : SpecialLinearGroup (Fin 3) F, conjAut 3 F A = descendAut 3 F (MulAut.conj Asl) := by
  set d := (A : Matrix (Fin 3) (Fin 3) F).det with hd
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
  have hdc : d ^ 2 = (c : F) ^ 3 := by
    have := congrArg Matrix.det hAA
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at this
    simpa [pow_two] using this
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  set s : F := d / c with hs
  have hs0 : s ≠ 0 := div_ne_zero hd0 hc0
  have hs3 : s ^ 3 = d := by
    rw [hs, div_pow, ← hdc]
    field_simp
  have hdetA' : ((s⁻¹ : F) • (A : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, ← hd]
    simp only [Fintype.card_fin, inv_pow, hs3]
    exact inv_mul_cancel₀ hd0
  let Asl : SpecialLinearGroup (Fin 3) F := ⟨(s⁻¹ : F) • (A : Matrix (Fin 3) (Fin 3) F), hdetA'⟩
  have hscalM : ∀ u : Fˣ, ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := fun u => by
    rw [smul_one_eq_diagonal]; rfl
  have hAscal : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) *
      Matrix.SpecialLinearGroup.toGL Asl := by
    apply Units.ext
    rw [Units.val_mul, hscalM]
    show (A : Matrix (Fin 3) (Fin 3) F) = (s • (1 : Matrix (Fin 3) (Fin 3) F)) *
      ((s⁻¹ : F) • (A : Matrix (Fin 3) (Fin 3) F))
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  refine ⟨Asl, ?_⟩
  have hsl : CatalogueBHigherLinearAction.slConjugation 3 F (Matrix.SpecialLinearGroup.toGL Asl) =
      MulAut.conj Asl := by
    ext g i j
    rw [CatalogueBHigherLinearAction.slConjugation_matrix, MulAut.conj_apply,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    congr 3
  rw [hAscal, map_mul, conjAut_scalar, one_mul]
  unfold conjAut
  rw [MonoidHom.comp_apply, hsl]

theorem conjAut_mem_inner_of_sq_scalar (A : GL (Fin 3) F) (c : Fˣ)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (c : F) • 1) :
    conjAut 3 F A ∈ inner (projectiveSL 3 F) := by
  obtain ⟨Asl, h⟩ := exists_sl_of_sq_scalar' A c hAA
  refine ⟨proj 3 F Asl, ?_⟩
  rw [h]
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [descendAut_proj]
  simp [MulAut.conj_apply, map_mul, map_inv]

open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear in
theorem lin_involution_cases [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) {c : MulAut (projectiveSL 3 F)} (hc2 : c * c = 1) :
    (∃ (A : GL (Fin 3) F) (u : Fˣ), (A : Matrix (Fin 3) (Fin 3) F) * A = (u : F) • 1 ∧
        c = conjAut 3 F A) ∨
      ∃ A : GL (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A ∧ c = conjAut 3 F A * dualAut 3 F := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hcA⟩ := hform c
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨B, hB⟩ := sq_eq_conj_field A σ hε
    have h1 : conjAut 3 F B * fieldAut 3 F (σ ^ 2) = 1 := by
      rw [← hB, ← hcA, pow_two]; exact hc2
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl B _ h1).1
  have hσ : σ = 1 := by
    obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic hp F hFc
    have hf0 : f ≠ 0 := by rintro rfl; exact absurd hf (by decide)
    have : Finite (RingAut F) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hf0)
    have hσf : σ ^ f = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    obtain ⟨k, hk⟩ := hf
    calc σ = σ ^ (2 * k) * σ := by rw [pow_mul, hσ2, one_pow, one_mul]
      _ = σ ^ f := by rw [hk, pow_succ]
      _ = 1 := hσf
  rw [hσ] at hcA
  interval_cases ε
  · left
    rw [pow_zero, mul_one, map_one, mul_one] at hcA
    have hsq : conjAut 3 F A * conjAut 3 F A = 1 := by rw [← hcA]; exact hc2
    have h1 : conjAut 3 F (A * A) * fieldAut 3 F 1 = 1 := by
      rw [map_one, mul_one, map_mul]; exact hsq
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl (A * A) 1 h1
    have hscal : ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [smul_one_eq_diagonal]; rfl
    have hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (u : F) • 1 := by
      rw [← hscal, hu, Units.val_mul]
    exact ⟨A, u, hAA, hcA⟩
  · right
    rw [pow_one, map_one, mul_one] at hcA
    refine ⟨A, ?_, hcA⟩
    have hsq : (conjAut 3 F A * fieldAut 3 F 1 * dualAut 3 F) ^ 2 = 1 := by
      rw [map_one, mul_one, pow_two, ← hcA]; exact hc2
    rcases transpose_eq_or_eq_neg_of_sq le_rfl A hsq with h | h
    · exact h
    · exfalso
      have hdet := congrArg Matrix.det h
      rw [Matrix.det_transpose, Matrix.det_neg] at hdet
      have hd0 : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero
      simp only [Fintype.card_fin] at hdet
      apply hd0
      have h22 : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F).det = 0 := by
        linear_combination hdet
      exact (mul_eq_zero.1 h22).resolve_left h2

theorem lin_involution_form [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) {c : MulAut (projectiveSL 3 F)} (hc2 : c * c = 1)
    (hout : c ∉ inner (projectiveSL 3 F)) :
    ∃ A : GL (Fin 3) F, (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A ∧ c = conjAut 3 F A * dualAut 3 F := by
  rcases lin_involution_cases hp hFc hf h2 hc2 with ⟨A, u, hAA, hcA⟩ | h
  · exact absurd (hcA ▸ conjAut_mem_inner_of_sq_scalar A u hAA) hout
  · exact h

theorem transpose_inv_of_symm {n : ℕ} (A : GL (Fin n) F)
    (hA : (A : Matrix (Fin n) (Fin n) F)ᵀ = A) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ = (A⁻¹ : GL (Fin n) F) := by
  have h : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
      (A : Matrix (Fin n) (Fin n) F)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
      = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
          ((A : Matrix (Fin n) (Fin n) F) * (A⁻¹ : GL (Fin n) F)) := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *
          (A : Matrix (Fin n) (Fin n) F)ᵀ) * (A⁻¹ : GL (Fin n) F) := by
        rw [hA, Matrix.mul_assoc]
    _ = (A⁻¹ : GL (Fin n) F) := by rw [h, Matrix.one_mul]

variable {A : GL (Fin 3) F}

theorem graphLift_graphLift (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) (g : SL(3, F)) :
    graphLift A (graphLift A g) = g := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_graphLift, toGL_graphLift]
  have hIA : GeneralLinearGroup.inverseTranspose A = A⁻¹ := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose]
    exact transpose_inv_of_symm A hA
  have hIAinv : GeneralLinearGroup.inverseTranspose A⁻¹ = A := by
    rw [← hIA, GeneralLinearGroup.inverseTranspose_inverseTranspose]
  simp only [map_mul, hIA, hIAinv, GeneralLinearGroup.inverseTranspose_inverseTranspose]
  group

theorem exists_isometrySL_rep (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) {g : SL(3, F)}
    (h : proj 3 F (graphLift A g) = proj 3 F g) :
    ∃ g' : SL(3, F), g' ∈ isometrySL 3 A⁻¹ ∧ proj 3 F g' = proj 3 F g := by
  have hz : g⁻¹ * graphLift A g ∈ scalars 3 F := proj_eq_proj_iff.1 h.symm
  set z := g⁻¹ * graphLift A g with hzdef
  have hz3 : z ^ 3 = 1 := scalars_pow_three hz
  have h1 : graphLift A g = g * z := by rw [hzdef]; group
  have hφz : graphLift A z = z⁻¹ := by
    calc graphLift A z = (graphLift A g)⁻¹ * graphLift A (graphLift A g) := by
          rw [hzdef, map_mul, map_inv]
      _ = (g * z)⁻¹ * g := by rw [graphLift_graphLift hA, h1]
      _ = z⁻¹ := by group
  have hz2 : z ^ 2 = z⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hz3
  refine ⟨g * z ^ 2, ?_, ?_⟩
  · rw [← graphLift_eq_iff, map_mul, map_pow, hφz, h1, hz2]
    group
  · have h2 : proj 3 F (z ^ 2) = 1 := proj_eq_one_iff.2 (pow_mem hz 2)
    rw [map_mul, h2, mul_one]


theorem lin_graph_centralizer [Finite F] (hF : ringChar F ≠ 2) (h3 : Nat.card F ≠ 3)
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ∃ N : Subgroup (projectiveSL 3 F), CFSG.IsQuasisimple ↥N ∧
      (∀ n ∈ N, (conjAut 3 F A * dualAut 3 F) n = n) ∧
      (∀ x, (conjAut 3 F A * dualAut 3 F) x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) ∧
      (∀ x y, (conjAut 3 F A * dualAut 3 F) x = x → (conjAut 3 F A * dualAut 3 F) y = y →
        ⁅x, y⁆ ∈ N) := by
  classical
  set R : GL (Fin 3) F := A⁻¹ with hR
  have hRsymm : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R := transpose_inv_of_symm A hA
  set I := CatalogueBGraphForm.isometryGroup 3 F R with hI
  set Ω := ⁅I, I⁆ with hΩ
  have hq : CFSG.IsQuasisimple Ω := by
    have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hF
    have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hF R hRsymm
    have hdim : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
    obtain ⟨d, ψ, e, -, -, -, hq0, -⟩ := orthogonal_three_derived hodd h3
      (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
    have := isQuasisimple_trans (isoOrthGL hF R hRsymm) hq0
    rwa [trans_commutator] at this
  set ΩS : Subgroup SL(3, F) := Ω.comap SpecialLinearGroup.toGL with hΩS
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hqS : CFSG.IsQuasisimple ΩS :=
    LocalCores.isQuasisimple_of_mulEquiv ((ΩS.equivMapOfInjective _
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmapΩ)).symm hq
  have hrep : ∀ x : projectiveSL 3 F, (conjAut 3 F A * dualAut 3 F) x = x →
      ∃ g : SL(3, F), g ∈ isometrySL 3 A⁻¹ ∧ proj 3 F g = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective 3 F x
    rw [conjAut_mul_dualAut_proj] at hx
    exact exists_isometrySL_rep hA hx
  refine ⟨ΩS.map (proj 3 F), ?_, ?_, ?_, ?_⟩
  · refine LocalCores.isQuasisimple_map hqS (proj 3 F) fun hker => ?_
    have hab : ∀ a ∈ ΩS, ∀ b ∈ ΩS, a * b = b * a := by
      intro a ha b hb
      have ha' : a ∈ scalars 3 F := by
        have h1 : proj 3 F a = 1 := hker ha
        exact proj_eq_one_iff.1 h1
      exact (mem_center_iff.1 (scalars_le_center 3 F ha') b).symm
    have : Nontrivial ΩS := LocalCores.isQuasisimple_nontrivial hqS
    have hcomm : commutator ΩS = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hab a a.2 b b.2)
    have hperfF := hqS.1.commutator_eq_top
    rw [hcomm] at hperfF
    exact bot_ne_top hperfF
  · rintro _ ⟨h, hh, rfl⟩
    rw [conjAut_mul_dualAut_proj]
    congr 1
    exact (graphLift_eq_iff A h).2 (commutator_le_self I hh)
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨h, hh, rfl⟩ := hn
    refine ⟨g * h * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    change SpecialLinearGroup.toGL (g * h * g⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    have hg' : graphLiftGL A (SpecialLinearGroup.toGL g) = SpecialLinearGroup.toGL g *
        GeneralLinearGroup.scalar (Fin 3) 1 := by
      rw [map_one, mul_one]
      exact (graphLiftGL_eq_iff A _).2 hg
    exact conj_mem_commutator_isometryGroup hg' hh
  · intro x y hx hy
    obtain ⟨g, hg, rfl⟩ := hrep x hx
    obtain ⟨k, hk, rfl⟩ := hrep y hy
    refine ⟨⁅g, k⁆, ?_, by simp only [map_commutatorElement]⟩
    change SpecialLinearGroup.toGL ⁅g, k⁆ ∈ Ω
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hg hk


end CFSG.GH74.KGroups.L3Eps

module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLg

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OFL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped commutatorElement

theorem mul_self_fin_two {E : Type*} [CommRing E] (M : Matrix (Fin 2) (Fin 2) E) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem eq_neg_one_or_eq_one_or {E : Type*} [Field E] {M : Matrix (Fin 2) (Fin 2) E}
    (hdet : M.det = 1) {c : E} (hM : M * M = c • 1) : c = -1 ∨ M = 1 ∨ M = -1 := by
  have h := mul_self_fin_two M
  rw [hM, hdet, one_smul] at h
  have h' : (c + 1) • (1 : Matrix (Fin 2) (Fin 2) E) = M.trace • M := by
    rw [add_smul, one_smul, h]
    abel
  by_cases hc : c + 1 = 0
  · left
    linear_combination hc
  right
  have ht : M.trace ≠ 0 := by
    intro ht
    rw [ht, zero_smul] at h'
    have := congrFun (congrFun h' 0) 0
    simp at this
    exact hc this
  have hMs : M = (M.trace⁻¹ * (c + 1)) • (1 : Matrix (Fin 2) (Fin 2) E) := by
    rw [mul_smul, h', smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hd : (M.trace⁻¹ * (c + 1)) * (M.trace⁻¹ * (c + 1)) = 1 := by
    have := hdet
    rw [hMs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    rw [← sq]
    exact this
  rcases mul_self_eq_one_iff.mp hd with h1 | h1
  · left
    rw [hMs, h1, one_smul]
  · right
    rw [hMs, h1, neg_one_smul]

variable {F : Type} [Field F]

theorem mul_self_eq_neg_one {l : F} (hl : l ≠ 0) (hns : ¬ IsSquare l)
    {Z : SpecialLinearGroup (Fin 4) F} (hZ : Z ∈ SK F hl) (hZ1 : proj 4 F Z ≠ 1)
    (hZ2 : proj 4 F Z ^ 2 = 1) : Z * Z = -1 := by
  classical
  set l' : Fˣ := Units.mk0 l hl with hl'
  have hns' : ¬ IsSquare (l' : F) := hns
  have hstr :=
    nonsquare_projective_centralizer_structure 4 (by norm_num) (kG hl) l' (kG_sq hl) hns'
  let : Fact (¬ IsSquare l'.val) := ⟨hns'⟩
  let := matrixModule (kG hl) l' (kG_sq hl)
  dsimp only at hstr
  obtain ⟨-, -, hm, -, -, -, -, -, -, -, -, e', -, -, -, -, -, -, hscal, -⟩ := hstr
  have hm2 : Module.finrank (extension l'.val) (Fin 4 → F) = 2 := by omega
  set E := extension l'.val with hE
  set τ : GL (Fin (Module.finrank E (Fin 4 → F))) E ≃* GL (Fin 2) E :=
    Units.mapEquiv (Matrix.reindexRingEquiv E (finCongr hm2)).toMulEquiv with hτ
  set ρ := e'.trans τ with hρ
  have hρs : ∀ c : Fˣ, ((ρ (ordinaryCentralizerScalar (kG hl) c) : GL (Fin 2) E) :
      Matrix (Fin 2) (Fin 2) E) = algebraMap F E c • 1 := by
    intro c
    rw [hρ, MulEquiv.trans_apply, hscal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hτ, Matrix.reindexRingEquiv, Matrix.scalar_apply]
      rfl
    · simp [hτ, Matrix.reindexRingEquiv, Matrix.scalar_apply, hij]
  set ι : CK F hl →* Subgroup.centralizer {kG hl} :=
    (SpecialLinearGroup.toGL.comp (CK F hl).subtype).codRestrict _ fun x => x.2 with hι
  set ψ : CK F hl →* Eˣ := GeneralLinearGroup.det.comp (ρ.toMonoidHom.comp ι) with hψ
  have hS : SK F hl ≤ ψ.ker.map (CK F hl).subtype := by
    rw [SK, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : CK F hl), (⟨b, hb⟩ : CK F hl)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨y, hy, hyZ⟩ := hS hZ
  have hdet : ((ρ (ι y) : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hy)
    rwa [hψ, MonoidHom.comp_apply, GeneralLinearGroup.val_det_apply, Units.val_one] at this
  have hιy : (((ι y : Subgroup.centralizer {kG hl}) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = Z := by
    rw [← hyZ]
    rfl
  have hZs : Z * Z ∈ scalars 4 F := by
    rw [← proj_eq_one_iff, map_mul, ← sq, hZ2]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hZs
  have hyy : ι y * ι y = ordinaryCentralizerScalar (kG hl) c := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hιy]
    change ((Z * Z : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [hc, GeneralLinearGroup.coe_scalar]
  have hMM : ((ρ (ι y) : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *
      ((ρ (ι y) : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = algebraMap F E c • 1 := by
    rw [← Units.val_mul, ← map_mul, hyy, hρs]
  rcases eq_neg_one_or_eq_one_or hdet hMM with h1 | h1 | h1
  ·
    have hc1 : (c : F) = -1 := by
      apply (algebraMap F E).injective
      rw [h1, map_neg, map_one]
    have hc' : (Z : Matrix (Fin 4) (Fin 4) F) * Z = Matrix.scalar (Fin 4) (c : F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact hc
    apply Subtype.ext
    change (Z : Matrix (Fin 4) (Fin 4) F) * Z = _
    rw [hc', hc1, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, map_neg,
      map_one]
  all_goals exfalso
  all_goals apply hZ1
  all_goals rw [proj_eq_one_iff]
  ·
    have h2 : ρ (ι y) = ρ (ordinaryCentralizerScalar (kG hl) 1) := by
      apply Units.ext
      rw [h1, hρs, Units.val_one, map_one, one_smul]
    have h3 := congrArg (fun x : Subgroup.centralizer {kG hl} =>
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (ρ.injective h2)
    simp only [hιy] at h3
    refine mem_scalars.2 ⟨1, one_pow 4, ?_⟩
    rw [h3]
    change ((GeneralLinearGroup.scalar (Fin 4) (1 : Fˣ) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = _
    rw [GeneralLinearGroup.coe_scalar]
  ·
    have h2 : ρ (ι y) = ρ (ordinaryCentralizerScalar (kG hl) (-1)) := by
      apply Units.ext
      rw [h1, hρs, Units.val_neg, Units.val_one, map_neg, map_one, neg_one_smul]
    have h3 := congrArg (fun x : Subgroup.centralizer {kG hl} =>
      ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) (ρ.injective h2)
    simp only [hιy] at h3
    refine mem_scalars.2 ⟨-1, by norm_num, ?_⟩
    rw [h3]
    change ((GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = _
    rw [GeneralLinearGroup.coe_scalar]

@[expose] def dK (l a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![a, l * b, 0, 0; b, a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem dK_comm (l a b : F) : dK l a b * kZero l = kZero l * dK l a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dK, kZero, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem det_dK (l a b : F) : (dK l a b).det = a ^ 2 - l * b ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [dK, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem exists_norm_eq [Fintype F] (hq : Fintype.card F % 2 = 1) {l : F} (hl : l ≠ 0) (d : F) :
    ∃ a b : F, a ^ 2 - l * b ^ 2 = d := by
  classical
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C d) (g := -(Polynomial.C l * Polynomial.X ^ 2))
    (by rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; rfl)
    (by
      rw [Polynomial.degree_neg, Polynomial.degree_C_mul_X_pow 2 hl]
      rfl) hq
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_neg, Polynomial.eval_mul] at hab
  linear_combination hab

theorem exists_conj_eq [Fintype F] (hq : Fintype.card F % 2 = 1) {l : F} (hl : l ≠ 0)
    (hns : ¬ IsSquare l) {W : GL (Fin 4) F}
    (hW : (W : Matrix (Fin 4) (Fin 4) F) * W = l • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∃ Y : SpecialLinearGroup (Fin 4) F,
      (conjAut 4 F (SpecialLinearGroup.toGL Y))⁻¹ * conjAut 4 F (kG hl) *
        conjAut 4 F (SpecialLinearGroup.toGL Y) = conjAut 4 F W := by
  classical
  set l' : Fˣ := Units.mk0 l hl with hl'
  have hW2 : W ^ 2 = GeneralLinearGroup.scalar (Fin 4) l' := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, hW, GeneralLinearGroup.coe_scalar, hl', Units.val_mk0,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  obtain ⟨P, hP⟩ := exists_conj_eq_kG (l := l') hns hW2
  have hP' : P⁻¹ * W * P = kG hl := hP
  set d : F := (P : Matrix (Fin 4) (Fin 4) F).det with hd
  have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
  obtain ⟨a, b, hab⟩ := exists_norm_eq hq hl d
  have hD0 : (dK l a b).det ≠ 0 := by rw [det_dK, hab]; exact hd0
  set D : GL (Fin 4) F := GeneralLinearGroup.mkOfDetNeZero (dK l a b) hD0 with hD
  have hDm : (D : Matrix (Fin 4) (Fin 4) F) = dK l a b := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hDk : D * kG hl = kG hl * D := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hDm, coe_kG, dK_comm])
  set Y' : GL (Fin 4) F := D * P⁻¹ with hY'
  have hY'det : (Y' : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    rw [hY', Units.val_mul, Matrix.det_mul, hDm, det_dK, hab]
    have h1 : (P : Matrix (Fin 4) (Fin 4) F).det *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [hd]
    exact h1
  refine ⟨⟨Y', hY'det⟩, ?_⟩
  have hY : SpecialLinearGroup.toGL (⟨Y', hY'det⟩ : SpecialLinearGroup (Fin 4) F) = Y' :=
    Units.ext rfl
  rw [hY, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  have hW' : W = P * kG hl * P⁻¹ := by rw [← hP']; group
  rw [hW', hY', _root_.mul_inv_rev, inv_inv]
  calc P * D⁻¹ * kG hl * (D * P⁻¹) = P * (D⁻¹ * (kG hl * D)) * P⁻¹ := by group
    _ = P * (D⁻¹ * (D * kG hl)) * P⁻¹ := by rw [hDk]
    _ = P * kG hl * P⁻¹ := by group

end OFL

end CFSG.ComponentClassification.CatFactsL4U4

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.HardMathSupport.Dickson.Sec6.HeisAux.NormalForm
import CFSG.RankThree.PartOne.LIT.RankMatrix
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289b

section Unitriangular
open Matrix

variable {F : Type} [Field F]

@[expose] def upM (p q r : F) : Matrix (Fin 3) (Fin 3) F := !![1, p, q; 0, 1, r; 0, 0, 1]

theorem det_upM (p q r : F) : (upM p q r).det = 1 := by
  simp [upM, Matrix.det_fin_three]

@[expose] def upSL (p q r : F) : SpecialLinearGroup (Fin 3) F := ⟨upM p q r, det_upM p q r⟩

@[simp] theorem coe_upSL (p q r : F) :
    ((upSL p q r : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = upM p q r := rfl

theorem upSL_mul (p q r p' q' r' : F) :
    upSL p q r * upSL p' q' r' = upSL (p + p') (q + q' + p * r') (r + r') := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, coe_upSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem upSL_zero : upSL (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upM]

theorem upSL_inv (p q r : F) : (upSL p q r)⁻¹ = upSL (-p) (p * r - q) (-r) := by
  rw [inv_eq_iff_mul_eq_one, upSL_mul]
  rw [show p + -p = 0 by ring, show q + (p * r - q) + p * -r = 0 by ring,
    show r + -r = 0 by ring, upSL_zero]

theorem upSL_commutator (p q r p' q' r' : F) :
    upSL p q r * upSL p' q' r' * (upSL p q r)⁻¹ * (upSL p' q' r')⁻¹ =
      upSL 0 (p * r' - p' * r) 0 := by
  rw [upSL_inv, upSL_inv, upSL_mul, upSL_mul, upSL_mul]
  congr 1 <;> ring

theorem upSL_eq_transvection01 (p : F) :
    upSL p 0 0 = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) p := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upM, Matrix.single_apply, Matrix.one_apply]

theorem upSL_eq_transvection02 (q : F) :
    upSL 0 q 0 = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) q := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upM, Matrix.single_apply, Matrix.one_apply]

theorem upSL_eq_transvection12 (r : F) :
    upSL 0 0 r = SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) r := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upM, Matrix.single_apply, Matrix.one_apply]

@[expose] def jM : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem jM_mul_jM : (jM : Matrix (Fin 3) (Fin 3) F) * jM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jM, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_jM [CharP F 2] : (jM : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [jM, Matrix.det_fin_three, CharTwo.neg_eq]

@[expose] def jSL [CharP F 2] : SpecialLinearGroup (Fin 3) F := ⟨jM, det_jM⟩

theorem jSL_mul_self [CharP F 2] : (jSL : SpecialLinearGroup (Fin 3) F) * jSL = 1 :=
  Subtype.ext jM_mul_jM

theorem jSL_inv [CharP F 2] : (jSL : SpecialLinearGroup (Fin 3) F)⁻¹ = jSL :=
  inv_eq_of_mul_eq_one_right jSL_mul_self

theorem jM_mul_mul_jM_apply (M : Matrix (Fin 3) (Fin 3) F) (a b : Fin 3) :
    ((jM * M * jM : Matrix (Fin 3) (Fin 3) F)) a b = M (Fin.rev a) (Fin.rev b) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp [jM]

theorem jSL_conj_transvection [CharP F 2] {i j : Fin 3} (hij : i ≠ j) (i' j' : Fin 3)
    (hij' : i' ≠ j') (hi : i' = Fin.rev i) (hj : j' = Fin.rev j) (c : F) :
    jSL * SpecialLinearGroup.transvection hij c * jSL⁻¹ =
      SpecialLinearGroup.transvection hij' c := by
  subst hi hj
  rw [jSL_inv]
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  change jM * (1 + Matrix.single i j c) * jM = 1 + Matrix.single (Fin.rev i) (Fin.rev j) c
  ext a b
  rw [jM_mul_mul_jM_apply]
  have e1 : (i = Fin.rev a) ↔ (Fin.rev i = a) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  have e2 : (j = Fin.rev b) ↔ (Fin.rev j = b) :=
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.rev_inj, e1, e2]

end Unitriangular

section Generation
open Matrix

variable {F : Type} [Field F]

@[expose] def xM (l : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![l, l ^ 5, l]

theorem det_xM {l : F} (hl : l ^ 7 = 1) : (xM l).det = 1 := by
  simp [xM, Matrix.det_diagonal, Fin.prod_univ_three]
  linear_combination hl

@[expose] def xSL {l : F} (hl : l ^ 7 = 1) : SpecialLinearGroup (Fin 3) F := ⟨xM l, det_xM hl⟩

theorem xSL_mul_upSL {l : F} (hl : l ^ 7 = 1) (p q r : F) :
    xSL hl * upSL p q r = upSL (l ^ 3 * p) q (l ^ 4 * r) * xSL hl := by
  apply Subtype.ext
  change xM l * upM p q r = upM (l ^ 3 * p) q (l ^ 4 * r) * xM l
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xM, upM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-(l * p)) * hl | linear_combination (l * p) * hl

@[expose] def uSL (σ : F ≃+* F) (ω a : F) : SpecialLinearGroup (Fin 3) F :=
  upSL a (ω * (a * σ a)) (σ a)

theorem uSL_inv_conj (σ : F ≃+* F) (ω : F) {l : F} (hl : l ^ 7 = 1) (a : F) :
    (uSL σ ω a)⁻¹ * xSL hl * uSL σ ω a * (xSL hl)⁻¹ =
      upSL ((l ^ 3 - 1) * a) ((1 - l ^ 4) * (a * σ a)) ((l ^ 4 - 1) * σ a) := by
  rw [show (uSL σ ω a)⁻¹ * xSL hl * uSL σ ω a * (xSL hl)⁻¹ =
    (uSL σ ω a)⁻¹ * (xSL hl * uSL σ ω a * (xSL hl)⁻¹) by group]
  rw [uSL, xSL_mul_upSL, mul_inv_cancel_right, upSL_inv, upSL_mul]
  congr 1 <;> ring

section Gen

variable [CharP F 2] {σ : F ≃+* F} {ω l : F}

theorem mem_of_transvections (H : Subgroup (SpecialLinearGroup (Fin 3) F))
    (h01 : ∀ c, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H)
    (h02 : ∀ c, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H)
    (h12 : ∀ c, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H)
    (hJ : jSL ∈ H) : H = ⊤ := by
  have hconj : ∀ {i j : Fin 3} (hij : i ≠ j) (i' j' : Fin 3) (hij' : i' ≠ j')
      (hi : i' = Fin.rev i) (hj : j' = Fin.rev j),
      (∀ c, SpecialLinearGroup.transvection hij c ∈ H) →
      ∀ c, SpecialLinearGroup.transvection hij' c ∈ H := by
    intro i j hij i' j' hij' hi hj h c
    rw [← jSL_conj_transvection hij i' j' hij' hi hj c]
    exact H.mul_mem (H.mul_mem hJ (h c)) (H.inv_mem hJ)
  have h21 := hconj (show (0 : Fin 3) ≠ 1 by decide) 2 1 (by decide) rfl rfl h01
  have h10 := hconj (show (1 : Fin 3) ≠ 2 by decide) 1 0 (by decide) rfl rfl h12
  have h20 := hconj (show (0 : Fin 3) ≠ 2 by decide) 2 0 (by decide) rfl rfl h02
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ H := by
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 c
    · exact h02 c
    · exact h10 c
    · exact absurd rfl hij
    · exact h12 c
    · exact h20 c
    · exact h21 c
    · exact absurd rfl hij
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  exact hall i j hij c

theorem closure_eq_top [Finite F] (hσσ : ∀ x, σ (σ x) = x) (hl : l ^ 7 = 1) (hl1 : l ≠ 1)
    (hσl : σ l = l)
    (hinj : ∀ μ : F, (l ^ 4 - 1) * σ μ - (l ^ 3 - 1) * μ = 0 → μ = 0) :
    Subgroup.closure (Set.range (uSL σ ω) ∪ {jSL, xSL hl}) = ⊤ := by
  set H := Subgroup.closure (Set.range (uSL σ ω) ∪ {jSL, xSL hl}) with hH
  have hu : ∀ a, uSL σ ω a ∈ H := fun a => Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
  have hJ : jSL ∈ H := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hx : xSL hl ∈ H := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hv : ∀ a, upSL ((l ^ 3 - 1) * a) ((1 - l ^ 4) * (a * σ a)) ((l ^ 4 - 1) * σ a) ∈ H := by
    intro a
    rw [← uSL_inv_conj σ ω hl a]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem (hu a)) hx) (hu a)) (H.inv_mem hx)
  have hσ1 : σ 1 = 1 := map_one σ
  set f : F →+ F :=
    { toFun := fun μ => (l ^ 4 - 1) * σ μ - (l ^ 3 - 1) * μ
      map_zero' := by simp
      map_add' := fun x y => by simp only [map_add]; ring } with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.1 (hinj _ h0)
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hfinj
  have h02 : ∀ c, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H := by
    intro c
    obtain ⟨μ, hμ⟩ := hfsurj c
    have hcomm := upSL_commutator 1 (ω * (1 * σ 1)) (σ 1) ((l ^ 3 - 1) * μ)
      ((1 - l ^ 4) * (μ * σ μ)) ((l ^ 4 - 1) * σ μ)
    have hmem : upSL 1 (ω * (1 * σ 1)) (σ 1) * upSL ((l ^ 3 - 1) * μ)
        ((1 - l ^ 4) * (μ * σ μ)) ((l ^ 4 - 1) * σ μ) * (upSL 1 (ω * (1 * σ 1)) (σ 1))⁻¹ *
        (upSL ((l ^ 3 - 1) * μ) ((1 - l ^ 4) * (μ * σ μ)) ((l ^ 4 - 1) * σ μ))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem (hu 1) (hv μ)) (H.inv_mem (hu 1))) (H.inv_mem (hv μ))
    rw [hcomm] at hmem
    rw [← upSL_eq_transvection02, ← hμ]
    convert hmem using 2
    simp only [hf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hσ1]
    ring
  have hx02 : ∀ q, upSL 0 q 0 ∈ H := fun q => by rw [upSL_eq_transvection02]; exact h02 q
  have hl3 : l ^ 3 - l ^ 4 ≠ 0 := by
    intro h
    have hl0 : l ≠ 0 := by rintro rfl; simp at hl
    have : l ^ 3 * (1 - l) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact hl0 (pow_eq_zero_iff (by norm_num) |>.1 h')
    · exact hl1 (by linear_combination -h')
  have h01 : ∀ c, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H := by
    intro c
    set a' := c / (l ^ 3 - l ^ 4) with ha'
    have hσα : σ ((1 - l ^ 4) * a') = (1 - l ^ 4) * σ a' := by
      rw [map_mul, map_sub, map_pow, hσl, hσ1]
    have hprod := H.mul_mem (hu ((1 - l ^ 4) * a')) (hv a')
    rw [uSL, upSL_mul, hσα] at hprod
    have h2 := H.mul_mem hprod (hx02 (-(ω * ((1 - l ^ 4) * a' * ((1 - l ^ 4) * σ a')) +
      (1 - l ^ 4) * (a' * σ a') + (1 - l ^ 4) * a' * ((l ^ 4 - 1) * σ a'))))
    rw [upSL_mul] at h2
    rw [← upSL_eq_transvection01]
    convert h2 using 2
    · have e : (1 - l ^ 4) * a' + (l ^ 3 - 1) * a' + 0 = (l ^ 3 - l ^ 4) * a' := by ring
      rw [e, ha', mul_div_cancel₀ _ hl3]
    · ring
    · ring
  have hx01 : ∀ p, upSL p 0 0 ∈ H := fun p => by rw [upSL_eq_transvection01]; exact h01 p
  have h12 : ∀ c, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H := by
    intro c
    have h1 := H.mul_mem (H.mul_mem (hx01 (-σ c)) (hu (σ c)))
      (hx02 (-(ω * (σ c * σ (σ c)) + -σ c * σ (σ c))))
    rw [uSL, upSL_mul, upSL_mul, hσσ] at h1
    rw [← upSL_eq_transvection12]
    convert h1 using 2 <;> ring
  exact mem_of_transvections H h01 h02 h12 hJ

end Gen

end Generation

section GraphField
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def tauJ (σ : F ≃+* F) : MulAut (projectiveSL 3 F) :=
  conjAut 3 F (SpecialLinearGroup.toGL jSL) * fieldAut 3 F σ * dualAut 3 F

theorem toGL_jSL_inv : (SpecialLinearGroup.toGL (jSL : SpecialLinearGroup (Fin 3) F))⁻¹ =
    SpecialLinearGroup.toGL jSL := by
  rw [← map_inv, jSL_inv]

theorem coe_tauJ_lift (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    ((CatalogueBHigherLinearAction.slConjugation 3 F (SpecialLinearGroup.toGL jSL)
        (SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose)) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      jM * ((((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose).map σ) *
        jM := by
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, toGL_jSL_inv]
  rfl

theorem tauJ_proj (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    tauJ σ (proj 3 F g) = proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F
      (SpecialLinearGroup.toGL jSL) (SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose))) := by
  rw [tauJ, MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]

variable {σ : F ≃+* F} {ω l : F}

theorem tauJ_uSL (hσσ : ∀ x, σ (σ x) = x) (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω ^ 2) (a : F) :
    tauJ σ (proj 3 F (uSL σ ω a)) = proj 3 F (uSL σ ω a) := by
  rw [tauJ_proj]
  congr 1
  apply Subtype.ext
  rw [coe_tauJ_lift, uSL, upSL_inv]
  ext i j
  rw [jM_mul_mul_jM_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;> simp [upM, Matrix.transpose_apply, hσσ, hσω] <;>
    first | ring1 | linear_combination (-a) * h2 | linear_combination (-(σ a)) * h2 |
      linear_combination (-(σ a * a)) * hω + (σ a * a) * h2 |
      linear_combination (σ a * a) * hω - (σ a * a) * h2 |
      linear_combination (-(a * σ a)) * hω + (a * σ a) * h2 |
      linear_combination (a * σ a) * hω - (a * σ a) * h2

theorem tauJ_jSL : tauJ σ (proj 3 F jSL) = proj 3 F jSL := by
  rw [tauJ_proj]
  congr 1
  apply Subtype.ext
  rw [coe_tauJ_lift, jSL_inv]
  ext i j
  rw [jM_mul_mul_jM_apply]
  fin_cases i <;> fin_cases j <;> simp [jSL, jM, Matrix.transpose_apply]

theorem xSL_inv_coe (hl : l ^ 7 = 1) :
    (((xSL hl)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![l ^ 6, l ^ 2, l ^ 6] := by
  have h : xSL hl * ⟨Matrix.diagonal ![l ^ 6, l ^ 2, l ^ 6], by
      simp [Matrix.det_diagonal, Fin.prod_univ_three]
      linear_combination (l ^ 7 + 1) * hl⟩ = 1 := by
    apply Subtype.ext
    change xM l * Matrix.diagonal ![l ^ 6, l ^ 2, l ^ 6] = 1
    rw [xM, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp <;> linear_combination hl
  rw [inv_eq_of_mul_eq_one_right h]

theorem tauJ_xSL (hl : l ^ 7 = 1) (hσl : σ l = l) :
    tauJ σ (proj 3 F (xSL hl)) = (proj 3 F (xSL hl))⁻¹ := by
  rw [tauJ_proj, ← map_inv]
  congr 1
  apply Subtype.ext
  rw [coe_tauJ_lift, xSL_inv_coe]
  ext i j
  rw [jM_mul_mul_jM_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, Matrix.diagonal_apply, hσl]

theorem tauJ_mul_self (hσσ : ∀ x, σ (σ x) = x) : tauJ σ * tauJ σ = 1 := by
  have h := sq_conjAut_fieldAut_dualAut (n := 3) (SpecialLinearGroup.toGL
    (jSL : SpecialLinearGroup (Fin 3) F)) σ
  have hσ2 : σ * σ = 1 := RingEquiv.ext fun x => hσσ x
  have hit : Matrix.GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL
      (jSL : SpecialLinearGroup (Fin 3) F)) = SpecialLinearGroup.toGL jSL := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, toGL_jSL_inv]
    change (jM : Matrix (Fin 3) (Fin 3) F).transpose = jM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jM, Matrix.transpose_apply]
  have hmap : Matrix.GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL
      (jSL : SpecialLinearGroup (Fin 3) F)) = SpecialLinearGroup.toGL jSL := by
    apply Units.ext
    change (jM : Matrix (Fin 3) (Fin 3) F).map σ = jM
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jM]
  have hA : SpecialLinearGroup.toGL (jSL : SpecialLinearGroup (Fin 3) F) *
      Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL jSL)) = 1 := by
    rw [hit, hmap, ← map_mul, jSL_mul_self, map_one]
  rw [sq, hA, hσ2, map_one, map_one, one_mul] at h
  exact h

theorem orderOf_proj_xSL (hl : l ^ 7 = 1) (hl1 : l ≠ 1) : orderOf (proj 3 F (xSL hl)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    rw [proj_eq_one_iff]
    refine ⟨1, one_pow 3, ?_⟩
    have : ((xSL hl ^ 7 : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      change xM l ^ 7 = 1
      rw [xM, Matrix.diagonal_pow, ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp
      · exact hl
      · rw [← pow_mul]; linear_combination (l ^ 28 + l ^ 21 + l ^ 14 + l ^ 7 + 1) * hl
      · exact hl
    rw [this]
    simp
  · intro h
    rw [proj_eq_one_iff] at h
    obtain ⟨c, -, hc⟩ := h
    have e0 := congrFun (congrFun hc 0) 0
    have e1 := congrFun (congrFun hc 1) 1
    change xM l 0 0 = _ at e0
    change xM l 1 1 = _ at e1
    simp [xM] at e0 e1
    have h4 : l ^ 5 = l := e1.trans e0.symm
    have hl0 : l ≠ 0 := by rintro rfl; simp at hl
    have h41 : l ^ 4 = 1 := by
      have : l * (l ^ 4 - 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' hl0
      · linear_combination h'
    apply hl1
    calc l = l ^ 8 * (l ^ 7)⁻¹ := by field_simp
      _ = 1 := by rw [hl, show l ^ 8 = (l ^ 4) ^ 2 by ring, h41]; simp

theorem closure_fix_eq_top [Finite F] (hσσ : ∀ x, σ (σ x) = x) (hω : ω ^ 2 + ω + 1 = 0)
    (hσω : σ ω = ω ^ 2) (hl : l ^ 7 = 1) (hl1 : l ≠ 1) (hσl : σ l = l)
    (hinj : ∀ μ : F, (l ^ 4 - 1) * σ μ - (l ^ 3 - 1) * μ = 0 → μ = 0) :
    Subgroup.closure ({p | tauJ σ p = p} ∪ {proj 3 F (xSL hl)}) = ⊤ := by
  have h := closure_eq_top (ω := ω) hσσ hl hl1 hσl hinj
  have hmap := congrArg (Subgroup.map (proj 3 F)) h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ (proj_surjective 3 F)] at hmap
  rw [eq_top_iff, ← hmap]
  apply Subgroup.closure_mono
  rintro _ ⟨g, hg, rfl⟩
  rcases hg with ⟨a, rfl⟩ | hg
  · exact Or.inl (tauJ_uSL hσσ hω hσω a)
  · rcases hg with rfl | rfl
    · exact Or.inl tauJ_jSL
    · exact Or.inr rfl

end GraphField

section Field64Lifts
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Field64

variable {F : Type} [Field F] [Finite F]

theorem pow_64 (hF : Nat.card F = 64) (x : F) : x ^ 64 = x := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card x
  rwa [Fintype.card_eq_nat_card, hF] at h

theorem pow_63 (hF : Nat.card F = 64) {x : F} (hx : x ≠ 0) : x ^ 63 = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [Fintype.card_eq_nat_card, hF] at h

theorem charP_two (hF : Nat.card F = 64) : CharP F 2 :=
  finite_field_prime_power_characteristic (p := 2) (k := 6) Nat.prime_two (by norm_num)
    (by rw [hF]; norm_num)

theorem exists_sigma (hF : Nat.card F = 64) : ∃ σ : F ≃+* F, ∀ x, σ x = x ^ 8 := by
  obtain ⟨φ, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality (p := 2) (n := 6)
    Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
  exact ⟨φ ^ 3, fun x => by rw [pow_apply_of_frobenius hφ]; norm_num⟩

theorem exists_cube_root (hF : Nat.card F = 64) : ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h
  have h3 : (u : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have h1 : (u : F) ≠ 1 := fun h1 => by
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    omega
  refine ⟨u, ?_⟩
  have : ((u : F) - 1) * ((u : F) ^ 2 + u + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)

theorem exists_seventh_root (hF : Nat.card F = 64) : ∃ l : F, l ^ 7 = 1 ∧ l ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h : 7 ∣ Nat.card Fˣ := by rw [Nat.card_units, hF]; norm_num
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 7 h
  refine ⟨(u : F), ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    omega

variable {σ : F ≃+* F}

theorem sigma_sigma (hF : Nat.card F = 64) (hσ : ∀ x, σ x = x ^ 8) (x : F) : σ (σ x) = x := by
  rw [hσ, hσ, ← pow_mul]
  exact pow_64 hF x

theorem sigma_cube_root (hσ : ∀ x, σ x = x ^ 8) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    σ ω = ω ^ 2 := by
  rw [hσ]
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  calc ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
    _ = ω ^ 2 := by rw [h3]; ring

theorem sigma_seventh_root (hσ : ∀ x, σ x = x ^ 8) {l : F} (hl : l ^ 7 = 1) : σ l = l := by
  rw [hσ]
  calc l ^ 8 = l ^ 7 * l := by ring
    _ = l := by rw [hl, one_mul]

theorem sigma_inj [CharP F 2] (hF : Nat.card F = 64) (hσ : ∀ x, σ x = x ^ 8) {l : F}
    (hl : l ^ 7 = 1) (hl1 : l ≠ 1) (μ : F) (h : (l ^ 4 - 1) * σ μ - (l ^ 3 - 1) * μ = 0) :
    μ = 0 := by
  by_contra hμ
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl
  set A := l ^ 4 - 1 with hA
  set B := l ^ 3 - 1 with hB
  have hA0 : A ≠ 0 := by
    intro h0
    apply hl1
    have h4 : l ^ 4 = 1 := by linear_combination h0
    calc l = l ^ 8 * (l ^ 7)⁻¹ := by field_simp
      _ = 1 := by rw [hl, show l ^ 8 = (l ^ 4) ^ 2 by ring, h4]; simp
  have hB0 : B ≠ 0 := by
    intro h0
    apply hl1
    have h3 : l ^ 3 = 1 := by linear_combination h0
    calc l = (l ^ 7) * ((l ^ 3) ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [hl, h3]; simp
  have hAB : A ≠ B := by
    intro h0
    apply hl1
    have : l ^ 3 * (l - 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h') hl0
    · linear_combination h'
  rw [hσ] at h
  have h7 : A * μ ^ 7 = B := by
    have : μ * (A * μ ^ 7 - B) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hμ)
  have h9 : A ^ 9 = B ^ 9 := by
    rw [← h7, mul_pow, ← pow_mul, pow_63 hF hμ, mul_one]
  have hσA : A ^ 8 = A := by
    have : σ A = A := by rw [hA, map_sub, map_pow, sigma_seventh_root hσ hl, map_one]
    rw [← hσ, this]
  have hσB : B ^ 8 = B := by
    have : σ B = B := by rw [hB, map_sub, map_pow, sigma_seventh_root hσ hl, map_one]
    rw [← hσ, this]
  have hA7 : A ^ 7 = 1 := by
    have : A * (A ^ 7 - 1) = 0 := by linear_combination hσA
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hA0)
  have hB7 : B ^ 7 = 1 := by
    have : B * (B ^ 7 - 1) = 0 := by linear_combination hσB
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hB0)
  have h2 : A ^ 2 = B ^ 2 := by
    have e1 : A ^ 9 = A ^ 2 := by rw [show A ^ 9 = A ^ 7 * A ^ 2 by ring, hA7, one_mul]
    have e2 : B ^ 9 = B ^ 2 := by rw [show B ^ 9 = B ^ 7 * B ^ 2 by ring, hB7, one_mul]
    rw [← e1, ← e2, h9]
  apply hAB
  have hsq : (A - B) ^ 2 = A ^ 2 - B ^ 2 := sub_pow_char A B
  have : (A - B) ^ 2 = 0 := by rw [hsq, h2, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

end Field64

section Lifts

variable {F : Type} [Field F]

theorem pow_three_of_mem_scalars {s : SpecialLinearGroup (Fin 3) F} (hs : s ∈ scalars 3 F) :
    s ^ 3 = 1 := by
  obtain ⟨c, hc, hsc⟩ := mem_scalars.1 hs
  apply Subtype.ext
  change (s : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1
  rw [hsc, ← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]

theorem mem_center_of_mem_scalars {s : SpecialLinearGroup (Fin 3) F} (hs : s ∈ scalars 3 F) :
    s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := scalars_le_center 3 F hs

theorem mul_pow_three_of_mem_scalars (g : SpecialLinearGroup (Fin 3) F)
    {s : SpecialLinearGroup (Fin 3) F} (hs : s ∈ scalars 3 F) : (g * s) ^ 3 = g ^ 3 := by
  have hc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars hs)
  have hcomm : Commute g s := hc g
  rw [hcomm.mul_pow, pow_three_of_mem_scalars hs, mul_one]

theorem pow_three_eq_of_proj_eq {g h : SpecialLinearGroup (Fin 3) F}
    (hgh : proj 3 F g = proj 3 F h) : g ^ 3 = h ^ 3 := by
  rw [proj_eq_proj_iff] at hgh
  have : h = g * (g⁻¹ * h) := by group
  rw [this, mul_pow_three_of_mem_scalars g hgh]

theorem pow_three_conj (k g : SpecialLinearGroup (Fin 3) F) (hg : g ^ 3 ∈ scalars 3 F) :
    (k * g * k⁻¹) ^ 3 = g ^ 3 := by
  rw [conj_pow]
  have hc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars hg)
  rw [hc k, mul_inv_cancel_right]

theorem pow_three_mem_scalars {g : SpecialLinearGroup (Fin 3) F}
    (hg : proj 3 F g ^ 3 = 1) : g ^ 3 ∈ scalars 3 F := by
  rw [← proj_eq_one_iff, map_pow]
  exact hg

variable {D : Subgroup (projectiveSL 3 F)}

theorem pow_three_eq_one_of_conj (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hconj : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ 1 → d₂ ≠ 1 → ∃ g, g * d₁ * g⁻¹ = d₂)
    {g : SpecialLinearGroup (Fin 3) F} (hg : proj 3 F g ∈ D) : g ^ 3 = 1 := by
  have hg3 : g ^ 3 ∈ scalars 3 F := pow_three_mem_scalars (hD3 _ hg)
  by_cases h1 : proj 3 F g = 1
  · exact pow_three_of_mem_scalars (proj_eq_one_iff.1 h1)
  · have hsq : proj 3 F g ^ 2 ∈ D := D.pow_mem hg 2
    have hsq1 : proj 3 F g ^ 2 ≠ 1 := by
      intro h
      apply h1
      have h3 := hD3 _ hg
      calc proj 3 F g = proj 3 F g ^ 3 * (proj 3 F g ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h]; group
    obtain ⟨q, hq⟩ := hconj _ hg _ hsq h1 hsq1
    obtain ⟨k, rfl⟩ := proj_surjective 3 F q
    have hk : proj 3 F (k * g * k⁻¹) = proj 3 F (g ^ 2) := by
      rw [map_mul, map_mul, map_inv, map_pow, hq]
    have e := pow_three_eq_of_proj_eq hk
    rw [pow_three_conj k g hg3, ← pow_mul, show 2 * 3 = 3 + 3 by norm_num, pow_add] at e
    have : g ^ 3 * g ^ 3 = g ^ 3 * 1 := by rw [mul_one]; exact e.symm
    exact mul_left_cancel this

end Lifts

end Field64Lifts

section E9
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

section Noncomm

theorem exists_scalar_ne_one {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    ∃ s ∈ scalars 3 F, s ≠ 1 := by
  have hω0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hω3 : (Units.mk0 ω hω0) ^ 3 = 1 := Units.ext (by
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    linear_combination (ω - 1) * hω)
  refine ⟨scalarElement _ hω3, scalarElement_mem_scalars _ hω3, fun h => ?_⟩
  have h0 := congrFun (congrFun (congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
    (g : Matrix (Fin 3) (Fin 3) F)) h) 0) 0
  simp at h0
  rw [h0] at hω
  exact h3 (by linear_combination hω)

variable [Finite F] {D : Subgroup (projectiveSL 3 F)}

theorem exists_noncomm_lifts {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0)
    (hD9 : Nat.card D = 9)
    (hcube : ∀ g : SpecialLinearGroup (Fin 3) F, proj 3 F g ∈ D → g ^ 3 = 1) :
    ∃ a b : SpecialLinearGroup (Fin 3) F, proj 3 F a ∈ D ∧ proj 3 F b ∈ D ∧ a * b ≠ b * a := by
  by_contra hne
  push Not at hne
  set Dh : Subgroup (SpecialLinearGroup (Fin 3) F) := D.comap (proj 3 F) with hDh
  set f := (proj 3 F).subgroupComap D with hf
  have hsurj : Function.Surjective f :=
    (proj 3 F).subgroupComap_surjective D (proj_surjective 3 F)
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  have hidx : f.ker.index = 9 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hD9]
  have hcardDh : Nat.card f.ker * 9 = Nat.card Dh := by
    rw [← hidx]
    exact Subgroup.card_mul_index f.ker
  obtain ⟨s, hs, hs1⟩ := exists_scalar_ne_one hω h3
  have hsD : s ∈ Dh := by
    show proj 3 F s ∈ D
    rw [proj_eq_one_iff.2 hs]
    exact D.one_mem
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    have : (⟨s, hsD⟩ : Dh) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact proj_eq_one_iff.2 hs
    rw [hbot, Subgroup.mem_bot] at this
    exact hs1 (congrArg Subtype.val this)
  have hker2 : 1 < Nat.card f.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hker
  set E : Subgroup (GL (Fin 3) F) := Dh.map SpecialLinearGroup.toGL with hE
  have hEcard : Nat.card E = Nat.card Dh :=
    Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective
  have hle := CFSG.RankThree.PartOne.LIT.card_le_sq_of_det_gl (K := F) (ι := Fin 3) (r := 3)
    Nat.prime_three (by exact_mod_cast h3) (by simp) E
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
      rw [← map_mul, ← map_mul, hne g h hg hh])
    (by
      rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow, hcube g hg, map_one])
    (by
      rintro _ ⟨g, hg, rfl⟩
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact g.2)
  rw [hEcard, ← hcardDh] at hle
  omega

end Noncomm

section Involution

variable [CharP F 2]

theorem eq_diagonal_of_commute {θ ζ : F} (hθ : θ ≠ 0) (hζ : ζ ^ 2 + ζ + 1 = 0) (hζ1 : ζ ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) F}
    (h : M * Matrix.diagonal ![θ, θ * ζ, θ * ζ ^ 2] =
      Matrix.diagonal ![θ, θ * ζ, θ * ζ ^ 2] * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hζ21 : ζ ^ 2 ≠ 1 := fun h2 => hζ1 (by
    have h3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by field_simp
      _ = 1 := by rw [h3, h2]; simp)
  have hζζ : ζ ≠ ζ ^ 2 := fun h2 => hζ1 (by
    have : ζ * (ζ - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hζ0
    · linear_combination h')
  have hd : ∀ i j, M i j * (![θ, θ * ζ, θ * ζ ^ 2] j - ![θ, θ * ζ, θ * ζ ^ 2] i) = 0 := by
    intro i j
    have := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    linear_combination this
  have hdist : ∀ i j, i ≠ j → ![θ, θ * ζ, θ * ζ ^ 2] j - ![θ, θ * ζ, θ * ζ ^ 2] i ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · intro h'; apply hζ1; exact mul_left_cancel₀ hθ (by linear_combination h')
    · intro h'; apply hζ21; exact mul_left_cancel₀ hθ (by linear_combination h')
    · intro h'; apply hζ1; exact mul_left_cancel₀ hθ (by linear_combination -h')
    · intro h'; apply hζζ; exact mul_left_cancel₀ hθ (by linear_combination -h')
    · intro h'; apply hζ21; exact mul_left_cancel₀ hθ (by linear_combination -h')
    · intro h'; apply hζζ; exact mul_left_cancel₀ hθ (by linear_combination h')
  intro i j hij
  exact (mul_eq_zero.1 (hd i j)).resolve_right (hdist i j hij)

theorem eq_of_sq_eq {x y : F} (h : x ^ 2 = y ^ 2) : x = y := by
  have hsq : (x - y) ^ 2 = x ^ 2 - y ^ 2 := sub_pow_char x y
  rw [h, sub_self] at hsq
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hsq)

theorem eq_one_of_commute_heis {a b : SpecialLinearGroup (Fin 3) F} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : a * b * a⁻¹ * b⁻¹ ∈ scalars 3 F) (hne : a * b ≠ b * a)
    {t : projectiveSL 3 F} (ht : t * t = 1) (hta : t * proj 3 F a = proj 3 F a * t) : t = 1 := by
  obtain ⟨c, hc3, hcz⟩ := mem_scalars.1 hab
  set ζ : F := (c : F) with hζdef
  have hζ3 : ζ ^ 3 = 1 := by rw [hζdef, ← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    apply hne
    have hz1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      apply Subtype.ext
      rw [hcz, h1, map_one]
      rfl
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hz1, one_mul]
  have hζ : ζ ^ 2 + ζ + 1 = 0 := by
    have : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hζ1)
  set Am : Matrix (Fin 3) (Fin 3) F := (a : Matrix (Fin 3) (Fin 3) F) with hAm
  set Bm : Matrix (Fin 3) (Fin 3) F := (b : Matrix (Fin 3) (Fin 3) F) with hBm
  have hAm3 : Am ^ 3 = 1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) ha
    simpa using this
  have hBm3 : Bm ^ 3 = (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hb
    rw [one_smul]
    simpa using this
  have hcomm : Am * Bm = ζ • (Bm * Am) := by
    have e : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    have e' : Am * Bm = ((a * b * a⁻¹ * b⁻¹ : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (Bm * Am) :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) e
    rw [e', hcz, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  obtain ⟨B, θ, hBu, hθ, hB0, -⟩ := CFSG.HardMathSupport.Dickson.Sec6.Heis.normal_form ζ 1 hζ hζ1
    one_ne_zero Am Bm hAm3 hBm3 hcomm
  obtain ⟨T, rfl⟩ := proj_surjective 3 F t
  have hT2 : T * T ∈ scalars 3 F := by rw [← proj_eq_one_iff, map_mul]; exact ht
  have hTa : a⁻¹ * (T * a * T⁻¹) ∈ scalars 3 F := by
    rw [← proj_eq_proj_iff, map_mul, map_mul, map_inv, hta, mul_inv_cancel_right]
  set s := a⁻¹ * (T * a * T⁻¹) with hs
  have hsc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars hTa)
  have hT2c := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars hT2)
  have hTaT : T * a * T⁻¹ = a * s := by rw [hs]; group
  have hs2 : s * s = 1 := by
    have e1 : (T * T) * a * (T * T)⁻¹ = a := by rw [← hT2c a, mul_inv_cancel_right]
    have e2 : (T * T) * a * (T * T)⁻¹ = T * (T * a * T⁻¹) * T⁻¹ := by group
    rw [e2, hTaT] at e1
    have e3 : T * (a * s) * T⁻¹ = (T * a * T⁻¹) * (T * s * T⁻¹) := by group
    rw [e3, hTaT, hsc T, mul_inv_cancel_right] at e1
    have : a * (s * s) = a * 1 := by rw [mul_one, ← mul_assoc]; exact e1
    exact mul_left_cancel this
  have hs1 : s = 1 := by
    have h3 := pow_three_of_mem_scalars hTa
    calc s = s ^ 3 * (s * s)⁻¹ := by group
      _ = 1 := by rw [h3, hs2]; group
  have hTA : T * a = a * T := by
    have : T * a * T⁻¹ = a := by rw [hTaT, hs1, mul_one]
    calc T * a = T * a * T⁻¹ * T := by group
      _ = a * T := by rw [this]
  set Tm : Matrix (Fin 3) (Fin 3) F := (T : Matrix (Fin 3) (Fin 3) F) with hTm
  have hTAm : Tm * Am = Am * Tm := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hTA
    simpa using this
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hBu)
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).1 hBu)
  set Dg : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![θ, θ * ζ, θ * ζ ^ 2] with hDg
  have hAD : B⁻¹ * Am * B = Dg := by
    rw [Matrix.mul_assoc, hB0, ← Matrix.mul_assoc, hBinv, Matrix.one_mul]
  set M := B⁻¹ * Tm * B with hM
  have hMD : M * Dg = Dg * M := by
    rw [← hAD, hM]
    calc B⁻¹ * Tm * B * (B⁻¹ * Am * B) = B⁻¹ * (Tm * Am) * B := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B B⁻¹, hBinv', Matrix.one_mul]
      _ = B⁻¹ * (Am * Tm) * B := by rw [hTAm]
      _ = B⁻¹ * Am * B * (B⁻¹ * Tm * B) := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc B B⁻¹, hBinv', Matrix.one_mul]
  have hdiag := eq_diagonal_of_commute hθ hζ hζ1 hMD
  obtain ⟨c₂, -, hc₂⟩ := mem_scalars.1 hT2
  have hMM : M * M = (c₂ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have hTT : Tm * Tm = (c₂ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      have : Tm * Tm = Matrix.scalar (Fin 3) (c₂ : F) := hc₂
      rw [this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    calc M * M = B⁻¹ * (Tm * Tm) * B := by
          rw [hM]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B B⁻¹, hBinv', Matrix.one_mul]
      _ = (c₂ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [hTT, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hBinv]
  have hsqi : ∀ i, M i i ^ 2 = c₂ := by
    intro i
    have := congrFun (congrFun hMM i) i
    rw [Matrix.mul_apply, Fin.sum_univ_three] at this
    fin_cases i <;> simp [hdiag 0 1 (by decide), hdiag 0 2 (by decide), hdiag 1 0 (by decide),
      hdiag 1 2 (by decide), hdiag 2 0 (by decide), hdiag 2 1 (by decide)] at this ⊢ <;>
      linear_combination this
  have h01 : M 0 0 = M 1 1 := eq_of_sq_eq ((hsqi 0).trans (hsqi 1).symm)
  have h02 : M 0 0 = M 2 2 := eq_of_sq_eq ((hsqi 0).trans (hsqi 2).symm)
  set m := M 0 0 with hm
  have hMs : M = m • (1 : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i
      · simp [hm]
      · simp [h01]
      · simp [h02]
    · rw [hdiag i j hij]
      simp [Matrix.one_apply_ne hij]
  have hTs : Tm = m • (1 : Matrix (Fin 3) (Fin 3) F) := by
    calc Tm = B * M * B⁻¹ := by
          rw [hM]; simp only [Matrix.mul_assoc]
          rw [hBinv', Matrix.mul_one, ← Matrix.mul_assoc, hBinv', Matrix.one_mul]
      _ = m • (1 : Matrix (Fin 3) (Fin 3) F) := by
          rw [hMs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hBinv']
  have hdet : m ^ 3 = 1 := by
    have := T.2
    change Tm.det = 1 at this
    rw [hTs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  have hm0 : m ≠ 0 := by rintro h0; rw [h0] at hdet; simp at hdet
  apply proj_eq_one_iff.2
  refine ⟨Units.mk0 _ hm0, Units.ext (by simpa using hdet), ?_⟩
  change Tm = _
  rw [hTs, Units.val_mk0, Matrix.smul_one_eq_diagonal]
  rfl

end Involution

end E9

section LiftAut
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F]

section Lift

theorem map_commutator_eq (φ : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F)
    {a b : SpecialLinearGroup (Fin 3) F} (ha : proj 3 F (φ a) = proj 3 F a)
    (hb : proj 3 F (φ b) = proj 3 F b) : φ (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by
  have hs : a⁻¹ * φ a ∈ scalars 3 F := proj_eq_proj_iff.1 ha.symm
  have ht : b⁻¹ * φ b ∈ scalars 3 F := proj_eq_proj_iff.1 hb.symm
  set s := a⁻¹ * φ a with hsdef
  set t := b⁻¹ * φ b with htdef
  have hsc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars hs)
  have htc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars ht)
  have ea : φ a = a * s := by rw [hsdef]; group
  have eb : φ b = b * t := by rw [htdef]; group
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, ea, eb]
  calc a * s * (b * t) * (a * s)⁻¹ * (b * t)⁻¹
      = a * (s * b) * t * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * (b * s) * t * s⁻¹ * a⁻¹ * t⁻¹ * b⁻¹ := by rw [hsc b]
    _ = a * b * (s * t * s⁻¹) * a⁻¹ * t⁻¹ * b⁻¹ := by group
    _ = a * b * t * a⁻¹ * t⁻¹ * b⁻¹ := by rw [← hsc t, mul_inv_cancel_right]
    _ = a * b * (t * a⁻¹) * t⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * t) * t⁻¹ * b⁻¹ := by rw [htc a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

@[expose] noncomputable def liftCF (A : GL (Fin 3) F) (σ : F ≃+* F) :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
  (CatalogueBHigherLinearAction.slConjugation 3 F A).toMonoidHom.comp
    (SpecialLinearGroup.map σ.toRingHom)

@[expose] noncomputable def liftCFD (A : GL (Fin 3) F) (σ : F ≃+* F) :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
  (liftCF A σ).comp (CatalogueBGraphForm.slGraphAut 3 F).toMonoidHom

theorem liftCF_proj (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F g) = proj 3 F (liftCF A σ g) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  rfl

theorem liftCFD_proj (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SpecialLinearGroup (Fin 3) F) :
    (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F g) = proj 3 F (liftCFD A σ g) := by
  rw [MulAut.mul_apply, dualAut_proj, liftCF_proj]
  rfl

theorem conj_scalar_matrix (A : GL (Fin 3) F) (w : F) :
    (A : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) w *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) w := by
  rw [← (Matrix.scalar_commute w (fun r => Commute.all _ r) (A : Matrix (Fin 3) (Fin 3) F)).eq,
    Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem liftCF_scalar (A : GL (Fin 3) F) (σ : F ≃+* F) {z : SpecialLinearGroup (Fin 3) F}
    {c : F} (hz : (z : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c) :
    (liftCF A σ z : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (σ c) := by
  change ((CatalogueBHigherLinearAction.slConjugation 3 F A
    (SpecialLinearGroup.map σ.toRingHom z) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = _
  rw [CatalogueBHigherLinearAction.slConjugation_matrix]
  have : ((SpecialLinearGroup.map σ.toRingHom z : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (σ c) := by
    rw [SpecialLinearGroup.map_apply_coe, hz]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [this]
  exact conj_scalar_matrix A (σ c)

theorem liftCFD_scalar (A : GL (Fin 3) F) (σ : F ≃+* F) {z : SpecialLinearGroup (Fin 3) F}
    {c : F} (hc : c ≠ 0) (hz : (z : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c) :
    (liftCFD A σ z : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (σ c)⁻¹ := by
  have hzi : ((z⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) c⁻¹ := by
    have h1 : (z : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) c⁻¹ = 1 := by
      rw [hz, ← map_mul, mul_inv_cancel₀ hc, map_one]
    have h2 := Matrix.inv_eq_right_inv h1
    change Matrix.adjugate (z : Matrix (Fin 3) (Fin 3) F) = _
    rw [← h2, Matrix.inv_def, z.2, Ring.inverse_one, one_smul]
  have hg : ((CatalogueBGraphForm.slGraphAut 3 F z : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c⁻¹ := by
    rw [CatalogueBGraphForm.slGraphAut_matrix, hzi]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
    split_ifs with h1 h2 <;> simp_all
  change (liftCF A σ (CatalogueBGraphForm.slGraphAut 3 F z) : Matrix (Fin 3) (Fin 3) F) = _
  rw [liftCF_scalar A σ hg, map_inv₀]

end Lift

section Frobenius

variable [Finite F]

theorem pow_three_eq_one_of_fix (hF : Nat.card F = 64) {σ : F ≃+* F} {c : F} (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (h : σ c = c) : σ ^ 3 = 1 := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality (p := 2)
    (n := 6) Nat.prime_two (by norm_num) (by rw [hF]; norm_num)
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, rfl⟩ : ∃ k < 6, φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % 6, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  rw [pow_apply_of_frobenius hφ] at h
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc3
  have hc2 : c ^ 2 ≠ c := fun h2 => hc1 (by
    have : c * (c - 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hc0
    · linear_combination h')
  have h6 : φ ^ 6 = 1 := by rw [← hord]; exact pow_orderOf_eq_one φ
  interval_cases k
  · simp
  · exact absurd (by simpa using h) hc2
  · rw [← pow_mul]; norm_num [h6]
  · exfalso; apply hc2
    calc c ^ 2 = (c ^ 3) ^ 2 * c ^ 2 := by rw [hc3]; ring
      _ = c ^ 2 ^ 3 := by ring
      _ = c := h
  · rw [← pow_mul, show 4 * 3 = 6 * 2 by norm_num, pow_mul, h6, one_pow]
  · exfalso; apply hc2
    calc c ^ 2 = (c ^ 3) ^ 10 * c ^ 2 := by rw [hc3]; ring
      _ = c ^ 2 ^ 5 := by ring
      _ = c := h

end Frobenius

end LiftAut

section Center
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F]

theorem conj_injective_projectiveSL [CharP F 2] :
    Function.Injective (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have hs : IsSimpleGroup (projectiveSL 3 F) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup
  have hZ : Subgroup.center (projectiveSL 3 F) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (projectiveSL 3 F)) with
      h | h
    · exact h
    · exfalso
      have hc : proj 3 F (upSL 1 0 0) * proj 3 F (upSL 0 0 1) =
          proj 3 F (upSL 0 0 1) * proj 3 F (upSL 1 0 0) :=
        Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top _) _ |>.symm
      rw [← map_mul, ← map_mul, upSL_mul, upSL_mul, proj_eq_proj_iff, upSL_inv, upSL_mul] at hc
      obtain ⟨u, -, hu⟩ := mem_scalars.1 hc
      have h02 := congrFun (congrFun hu 0) 2
      have h00 := congrFun (congrFun hu 0) 0
      simp [upM, Matrix.scalar_apply] at h02 h00
  rw [injective_iff_map_eq_one]
  intro p hp
  have hc : p ∈ Subgroup.center (projectiveSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have := congrArg (fun α : MulAut (projectiveSL 3 F) => α q) hp
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc q * p = p * q * p⁻¹ * p := by rw [this]
      _ = p * q := by group
  rw [hZ] at hc
  exact hc

end Center

section InnerPart
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F] [CharP F 2]

section E9

variable {D : Subgroup (projectiveSL 3 F)}

theorem e9_structure (hF : Nat.card F = 64) (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD3 : ∀ d ∈ D, d ^ 3 = 1) (hD9 : Nat.card D = 9)
    (hconj : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ 1 → d₂ ≠ 1 → ∃ g, g * d₁ * g⁻¹ = d₂) :
    (∃ a b : SpecialLinearGroup (Fin 3) F, proj 3 F a ∈ D ∧ proj 3 F b ∈ D ∧
      a * b * a⁻¹ * b⁻¹ ∈ scalars 3 F ∧ a * b ≠ b * a) ∧
    (∀ d ∈ D, d ≠ 1 → ∀ t : projectiveSL 3 F, t * t = 1 → t * d = d * t → t = 1) := by
  obtain ⟨ω, hω⟩ := exists_cube_root hF
  have h3 : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    intro h; exact one_ne_zero (by linear_combination h - h2 : (1 : F) = 0)
  have hcube := fun g (hg : proj 3 F g ∈ D) => pow_three_eq_one_of_conj hD3 hconj hg
  obtain ⟨a, b, ha, hb, hab⟩ := exists_noncomm_lifts hω h3 hD9 hcube
  have hz : a * b * a⁻¹ * b⁻¹ ∈ scalars 3 F := by
    rw [← proj_eq_one_iff]
    simp only [map_mul, map_inv]
    rw [hDcomm _ ha _ hb]
    group
  refine ⟨⟨a, b, ha, hb, hz, hab⟩, ?_⟩
  have hno := fun t (ht : t * t = 1) (hta : t * proj 3 F a = proj 3 F a * t) =>
    eq_one_of_commute_heis (hcube a ha) (hcube b hb) hz hab ht hta
  have ha1 : proj 3 F a ≠ 1 := by
    intro h
    apply hab
    have hc := Subgroup.mem_center_iff.1 (mem_center_of_mem_scalars (proj_eq_one_iff.1 h))
    exact (hc b).symm
  intro d hd hd1 t ht htd
  obtain ⟨g, hg⟩ := hconj d hd (proj 3 F a) ha hd1 ha1
  have h1 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht]; group
  have h2 : (g * t * g⁻¹) * proj 3 F a = proj 3 F a * (g * t * g⁻¹) := by
    rw [← hg]
    calc g * t * g⁻¹ * (g * d * g⁻¹) = g * (t * d) * g⁻¹ := by group
      _ = g * (d * t) * g⁻¹ := by rw [htd]
      _ = g * d * g⁻¹ * (g * t * g⁻¹) := by group
  have h3' := hno _ h1 h2
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h3']; group

end E9

section Aut

variable {D : Subgroup (projectiveSL 3 F)} {X : Subgroup (MulAut (projectiveSL 3 F))}

theorem eq_one_of_conj_mem (hD3 : ∀ d ∈ D, d ^ 3 = 1) (hD9 : Nat.card D = 9)
    (hno : ∀ d ∈ D, d ≠ 1 → ∀ t : projectiveSL 3 F, t * t = 1 → t * d = d * t → t = 1)
    (hX : IsPGroup 2 X)
    (hDX : ∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 F))))
    {p : projectiveSL 3 F} (hp : MulAut.conj p ∈ X) : p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup (projectiveSL 3 F) := X.comap MulAut.conj with hS
  have hinj := conj_injective_projectiveSL (F := F)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hX
  have hSdvd : Nat.card S ∣ 2 ^ n := by
    rw [← hn, ← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
  have hS3 : ¬ 3 ∣ Nat.card S := fun h3 =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hSdvd)) (by norm_num)
  have hDS : D ≤ Subgroup.normalizer (S : Set (projectiveSL 3 F)) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [hS, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hDX d hd) _
  have hpow : ∀ m : D, m ^ 3 = 1 := fun m => Subtype.ext (by simpa using hD3 m m.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three D S hpow (by rw [hD9]; norm_num) hS3 hDS
  have hSbot : S = ⊥ := by
    rw [hgen]
    refine iSup₂_eq_bot.mpr fun m hm => ?_
    have hm1 : (m : projectiveSL 3 F) ≠ 1 := fun h => hm (Subtype.ext h)
    by_contra hne
    set C := S ⊓ Subgroup.centralizer ({(m : projectiveSL 3 F)} : Set (projectiveSL 3 F))
      with hC
    have hC1 : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    have hCdvd : Nat.card C ∣ 2 ^ n := (Subgroup.card_dvd_of_le inf_le_left).trans hSdvd
    have h2C : 2 ∣ Nat.card C := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hCdvd
      rw [hk'] at hC1 ⊢
      rcases k with _ | k
      · simp at hC1
      · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2C
    have ht2 : (t : projectiveSL 3 F) * t = 1 := by
      have := pow_orderOf_eq_one t
      rw [ht, sq] at this
      exact congrArg Subtype.val this
    have ht1 : (t : projectiveSL 3 F) ≠ 1 := by
      intro h
      have : t = 1 := Subtype.ext h
      rw [this, orderOf_one] at ht
      omega
    have htm : (t : projectiveSL 3 F) * m = m * t :=
      Subgroup.mem_centralizer_singleton_iff.1 (t.2.2)
    exact ht1 (hno m m.2 hm1 t ht2 htm)
  have hpS : p ∈ S := hp
  rw [hSbot] at hpS
  exact hpS

end Aut

end InnerPart

section OuterPart
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F] [CharP F 2]

section Aut2

variable {D : Subgroup (projectiveSL 3 F)} {X : Subgroup (MulAut (projectiveSL 3 F))}

theorem mul_conj_mul_inv (α : MulAut (projectiveSL 3 F)) (y : projectiveSL 3 F) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem apply_eq_of_mem (hinn : ∀ p : projectiveSL 3 F, MulAut.conj p ∈ X → p = 1)
    (hDX : ∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 F))))
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ X) {e : projectiveSL 3 F} (he : e ∈ D) :
    x e = e := by
  have hw : MulAut.conj e * x * (MulAut.conj e)⁻¹ * x⁻¹ ∈ X :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hDX e he) x).mp hx) (inv_mem hx)
  have hw' : MulAut.conj e * x * (MulAut.conj e)⁻¹ * x⁻¹ = MulAut.conj (e * x e⁻¹) := by
    rw [map_mul, ← mul_conj_mul_inv, map_inv]
    group
  rw [hw'] at hw
  have h1 := hinn _ hw
  rw [mul_eq_one_iff_eq_inv, map_inv, inv_inv] at h1
  exact h1.symm

theorem exists_pow_conjAut_fieldAut (A : GL (Fin 3) F) (σ : F ≃+* F) (n : ℕ) :
    ∃ B : GL (Fin 3) F, (conjAut 3 F A * fieldAut 3 F σ) ^ n =
      conjAut 3 F B * fieldAut 3 F (σ ^ n) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * Matrix.GeneralLinearGroup.map ((σ ^ n : F ≃+* F) : F →+* F) A, ?_⟩
    rw [pow_succ, hB, conjAut_mul_fieldAut_mul, pow_succ]

variable (hinn : ∀ p : projectiveSL 3 F, MulAut.conj p ∈ X → p = 1) (hX : IsPGroup 2 X)
  {a b : SpecialLinearGroup (Fin 3) F} {c : Fˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
  (hz : ((a * b * a⁻¹ * b⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.scalar (Fin 3) (c : F))
  (hfix : ∀ x ∈ X, x (proj 3 F a) = proj 3 F a ∧ x (proj 3 F b) = proj 3 F b)

include hinn hX hc3 hc1 hz hfix

theorem eq_one_of_conjAut_fieldAut (hF : Nat.card F = 64) {x : MulAut (projectiveSL 3 F)}
    (hx : x ∈ X) {A : GL (Fin 3) F} {σ : F ≃+* F} (hxA : x = conjAut 3 F A * fieldAut 3 F σ) :
    x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσc : σ (c : F) = c := by
    have h1 := map_commutator_eq (liftCF A σ)
      (a := a) (b := b) (by rw [← liftCF_proj, ← hxA]; exact (hfix x hx).1)
      (by rw [← liftCF_proj, ← hxA]; exact (hfix x hx).2)
    have h2 := liftCF_scalar A σ hz
    rw [h1, hz] at h2
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.scalar_apply] using this.symm
  have hc3' : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc1' : (c : F) ≠ 1 := fun h => hc1 (Units.ext h)
  have hσ3 := pow_three_eq_one_of_fix hF hc3' hc1' hσc
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨B, hB⟩ := exists_pow_conjAut_fieldAut A σ (2 ^ k)
  rw [← hxA, hxk] at hB
  have hσk := (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) B (σ ^ 2 ^ k) hB.symm).1
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    have h2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hσ1, map_one, mul_one] at hxA
  have hx3 : x ^ 3 = 1 := by
    set u := Matrix.GeneralLinearGroup.det A with hu
    set B' : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A ^ 3 with hB'
    have hdet : ((B' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [hB', Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : (A : Matrix (Fin 3) (Fin 3) F).det = (u : F) := rfl
      rw [this, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        inv_pow, inv_mul_cancel, Units.val_one]
    set g : SpecialLinearGroup (Fin 3) F := ⟨B', hdet⟩ with hg
    have hgB : SpecialLinearGroup.toGL g = B' := Units.ext rfl
    have hx3' : x ^ 3 = MulAut.conj (proj 3 F g) := by
      rw [← conjAut_toGL, hgB, hB', map_mul, conjAut_scalar, one_mul, map_pow, hxA]
    have hmem : MulAut.conj (proj 3 F g) ∈ X := hx3' ▸ X.pow_mem hx 3
    rw [hx3', hinn _ hmem, map_one]
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem sq_eq_one_of_conjAut_fieldAut_dualAut (hF : Nat.card F = 64)
    {x : MulAut (projectiveSL 3 F)} (hx : x ∈ X) {A : GL (Fin 3) F} {σ : F ≃+* F}
    (hxA : x = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) : x * x = 1 ∧ σ ≠ 1 := by
  constructor
  · have h := sq_conjAut_fieldAut_dualAut A σ
    rw [← hxA, sq] at h
    exact eq_one_of_conjAut_fieldAut hinn hX hc3 hc1 hz hfix hF (X.mul_mem hx hx) h
  · intro hσ
    have hc0 : (c : F) ≠ 0 := c.ne_zero
    have hσc : (σ (c : F))⁻¹ = c := by
      have h1 := map_commutator_eq (liftCFD A σ)
        (a := a) (b := b) (by rw [← liftCFD_proj, ← hxA]; exact (hfix x hx).1)
        (by rw [← liftCFD_proj, ← hxA]; exact (hfix x hx).2)
      have h2 := liftCFD_scalar A σ hc0 hz
      rw [h1, hz] at h2
      have := congrFun (congrFun h2 0) 0
      simpa [Matrix.scalar_apply] using this.symm
    rw [hσ] at hσc
    have e : (1 : F ≃+* F) (c : F) = c := rfl
    rw [e] at hσc
    have hcc : (c : F) * c = 1 := by
      calc (c : F) * c = (c : F) * (c : F)⁻¹ := by rw [hσc]
        _ = 1 := mul_inv_cancel₀ hc0
    apply hc1
    apply Units.ext
    have hc3' : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    calc (c : F) = (c : F) ^ 3 * ((c : F) * c)⁻¹ := by field_simp
      _ = 1 := by rw [hc3', hcc]; simp

end Aut2

end OuterPart

section Main
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

variable {F : Type} [Field F] [Finite F]

theorem graphField_mul_graphField (A B : GL (Fin 3) F) (σ ρ : F ≃+* F) :
    conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F * (conjAut 3 F B * fieldAut 3 F ρ * dualAut 3 F) =
      conjAut 3 F (A * Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.GeneralLinearGroup.inverseTranspose B)) * fieldAut 3 F (σ * ρ) := by
  have hdd : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (n := 3) (K := F)).2.2.2.1
  calc conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F * (conjAut 3 F B * fieldAut 3 F ρ * dualAut 3 F)
      = conjAut 3 F A * fieldAut 3 F σ * (dualAut 3 F * conjAut 3 F B) * fieldAut 3 F ρ *
          dualAut 3 F := by simp only [mul_assoc]
    _ = conjAut 3 F A * fieldAut 3 F σ *
          conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose B) *
          (dualAut 3 F * fieldAut 3 F ρ) * dualAut 3 F := by
        rw [dualAut_mul_conjAut]; simp only [mul_assoc]
    _ = conjAut 3 F A * fieldAut 3 F σ *
          (conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose B) * fieldAut 3 F ρ) *
          (dualAut 3 F * dualAut 3 F) := by
        rw [dualAut_mul_fieldAut]; simp only [mul_assoc]
    _ = _ := by rw [hdd, mul_one, conjAut_mul_fieldAut_mul]

variable [CharP F 2]

theorem autFacts_P (hF : Nat.card F = 64) {D : Subgroup (projectiveSL 3 F)}
    (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD3 : ∀ d ∈ D, d ^ 3 = 1)
    (hD9 : Nat.card D = 9)
    (hconj : ∀ d₁ ∈ D, ∀ d₂ ∈ D, d₁ ≠ 1 → d₂ ≠ 1 → ∃ g, g * d₁ * g⁻¹ = d₂)
    {X : Subgroup (MulAut (projectiveSL 3 F))} (hX : IsPGroup 2 X)
    (hDX : ∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (X : Set (MulAut (projectiveSL 3 F)))) :
    X = ⊥ ∨ ∃ τ : MulAut (projectiveSL 3 F), X = Subgroup.zpowers τ ∧ τ * τ = 1 ∧
      ∃ x : projectiveSL 3 F, orderOf x = 7 ∧ τ x = x⁻¹ ∧
        Subgroup.closure ({p | τ p = p} ∪ {x}) = ⊤ := by
  obtain ⟨⟨a, b, ha, hb, hz, hab⟩, hno⟩ := e9_structure hF hDcomm hD3 hD9 hconj
  have hinn := fun p (hp : MulAut.conj p ∈ X) => eq_one_of_conj_mem hD3 hD9 hno hX hDX hp
  have hfixD := fun x (hx : x ∈ X) e (he : e ∈ D) => apply_eq_of_mem hinn hDX hx he
  have hfix : ∀ x ∈ X, x (proj 3 F a) = proj 3 F a ∧ x (proj 3 F b) = proj 3 F b :=
    fun x hx => ⟨hfixD x hx _ ha, hfixD x hx _ hb⟩
  obtain ⟨c, hc3, hcz⟩ := mem_scalars.1 hz
  have hc1 : c ≠ 1 := by
    intro h
    apply hab
    have hz1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      apply Subtype.ext
      rw [hcz, h, Units.val_one, map_one]
      rfl
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hz1, one_mul]
  have hcf := fun x (hx : x ∈ X) A σ (hxA : x = conjAut 3 F A * fieldAut 3 F σ) =>
    eq_one_of_conjAut_fieldAut hinn hX hc3 hc1 hcz hfix hF hx hxA
  have hcfd := fun x (hx : x ∈ X) A σ (hxA : x = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) =>
    sq_eq_one_of_conjAut_fieldAut_dualAut hinn hX hc3 hc1 hcz hfix hF hx hxA
  have hcls : ∀ x ∈ X, x = 1 ∨ ∃ A σ, x = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F := by
    intro x hx
    obtain ⟨A, σ, ε, hε, hxe⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 x
    interval_cases ε
    · left
      rw [pow_zero, mul_one] at hxe
      exact hcf x hx A σ hxe
    · right
      rw [pow_one] at hxe
      exact ⟨A, σ, hxe⟩
  rcases eq_or_ne X ⊥ with hbot | hne
  · exact Or.inl hbot
  right
  obtain ⟨⟨τ, hτX⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hτ1' : τ ≠ 1 := fun h => hτ1 (Subtype.ext h)
  obtain ⟨A, σ, hτA⟩ := (hcls τ hτX).resolve_left hτ1'
  obtain ⟨hτ2, hσ1⟩ := hcfd τ hτX A σ hτA
  refine ⟨τ, ?_, hτ2, ?_⟩
  ·
    apply le_antisymm _ ((Subgroup.zpowers_le).2 hτX)
    intro y hy
    rcases hcls y hy with rfl | ⟨B, ρ, hyB⟩
    · exact Subgroup.one_mem _
    · have hτy : τ * y = 1 := by
        apply hcf (τ * y) (X.mul_mem hτX hy) _ _
        rw [hτA, hyB, graphField_mul_graphField]
      have : y = τ := by
        have h1 : y = τ⁻¹ := eq_inv_of_mul_eq_one_right hτy
        rw [h1, inv_eq_of_mul_eq_one_right hτ2]
      rw [this]
      exact Subgroup.mem_zpowers τ
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hσ8, H, hH⟩ := odd_linear_graph_field_involution_conjugacy (p := 2) (f := 6)
      Nat.prime_two (by norm_num) (by rw [hF]; norm_num) (le_refl 3) A σ hσ1
      (by rw [sq, ← hτA]; exact hτ2)
    have hσ8' : ∀ x, σ x = x ^ 8 := fun x => by rw [hσ8]; norm_num
    have hσσ := sigma_sigma hF hσ8'
    obtain ⟨-, -, H', hH'⟩ := odd_linear_graph_field_involution_conjugacy (p := 2) (f := 6)
      Nat.prime_two (by norm_num) (by rw [hF]; norm_num) (le_refl 3)
      (SpecialLinearGroup.toGL jSL) σ hσ1 (by rw [sq]; exact tauJ_mul_self hσσ)
    obtain ⟨ω, hω⟩ := exists_cube_root hF
    obtain ⟨l, hl, hl1⟩ := exists_seventh_root hF
    set β : MulAut (projectiveSL 3 F) := conjAut 3 F H * (conjAut 3 F H')⁻¹ with hβ
    have hτβ : τ = β * tauJ σ * β⁻¹ := by
      have e : fieldAut 3 F σ * dualAut 3 F =
          (conjAut 3 F H')⁻¹ * tauJ σ * conjAut 3 F H' := by
        rw [tauJ, hH']
        group
      rw [hτA, hH, e, hβ]
      group
    set y := proj 3 F (xSL hl) with hy
    refine ⟨β y, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq, hy, orderOf_proj_xSL hl hl1]
    · rw [hτβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
        hy, tauJ_xSL hl (sigma_seventh_root hσ8' hl), map_inv]
    · have htop := closure_fix_eq_top (ω := ω) hσσ hω (sigma_cube_root hσ8' hω) hl hl1
        (sigma_seventh_root hσ8' hl) (sigma_inj hF hσ8' hl hl1)
      rw [eq_top_iff, ← Subgroup.map_top_of_surjective (β : projectiveSL 3 F →* projectiveSL 3 F)
        β.surjective, ← htop, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨p, hp, rfl⟩
      rcases hp with hp | hp
      · left
        show τ (β p) = β p
        rw [hτβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
        exact congrArg β hp
      · right
        rw [Set.mem_singleton_iff.1 hp]
        rfl

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input289b

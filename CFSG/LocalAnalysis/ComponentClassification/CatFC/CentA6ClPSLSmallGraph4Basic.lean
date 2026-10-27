module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallInner4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallBasic

public noncomputable section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix

namespace CFSG.ComponentClassification.CatFC.PSLSmall

namespace Graph4


section Explicit

variable {K : Type} [Field K]

@[expose] def Gc (w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, w, 0; 0, 0, 0, w]

@[expose] def Mc : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

theorem Gc_transpose (w : K) : (Gc w)ᵀ = Gc w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gc]

theorem Mc_mul_self (h3 : (3 : K) = 0) : (Mc : Matrix (Fin 4) (Fin 4) K) * Mc = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mc, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;>
    linear_combination h3

theorem Mc_transpose_Gc_Mc (h3 : (3 : K) = 0) (w : K) :
    (Mc : Matrix (Fin 4) (Fin 4) K)ᵀ * Gc w * Mc = (-1 : K) • Gc w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mc, Gc, Matrix.mul_apply, Fin.sum_univ_four] <;>
    linear_combination (w) * h3

theorem det_Mc (h3 : (3 : K) = 0) : (Mc : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Mc, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (-1 : K) * h3

theorem single_dot_mulVec_single {n : ℕ} (S : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Pi.single i (1 : K) : Fin n → K) ⬝ᵥ S *ᵥ (Pi.single j (1 : K) : Fin n → K) = S i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem eq_of_quad_eq (h2 : (2 : K) ≠ 0) {n : ℕ} {S₁ S₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : S₁ᵀ = S₁) (h₂ : S₂ᵀ = S₂)
    (h : ∀ v : Fin n → K, v ⬝ᵥ S₁ *ᵥ v = v ⬝ᵥ S₂ *ᵥ v) : S₁ = S₂ := by
  have hdiag : ∀ i, S₁ i i = S₂ i i := by
    intro i
    have := h (Pi.single i 1)
    rwa [single_dot_mulVec_single, single_dot_mulVec_single] at this
  ext i j
  have hsum := h (Pi.single i 1 + Pi.single j 1)
  have e1 : ∀ S : Matrix (Fin n) (Fin n) K, Sᵀ = S →
      (Pi.single i (1 : K) + Pi.single j (1 : K) : Fin n → K) ⬝ᵥ
        S *ᵥ (Pi.single i (1 : K) + Pi.single j (1 : K) : Fin n → K) =
        S i i + 2 * S i j + S j j := by
    intro S hS
    have hji : S j i = S i j := by
      have := congrFun (congrFun hS i) j
      simpa using this
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, single_dot_mulVec_single, hji]
    ring
  rw [e1 S₁ h₁, e1 S₂ h₂, hdiag i, hdiag j] at hsum
  have : (2 : K) * S₁ i j = 2 * S₂ i j := by linear_combination hsum
  exact mul_left_cancel₀ h2 this

theorem quad_congr {n : ℕ} (P G : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    v ⬝ᵥ (Pᵀ * G * P) *ᵥ v = (P *ᵥ v) ⬝ᵥ G *ᵥ (P *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem units_sq_eq_one {K : Type} [Field K] [Finite K] (hK3 : Nat.card K = 3) (u : Kˣ) :
    u ^ 2 = 1 := by
  have := pow_card_eq_one' (G := Kˣ) (x := u)
  rwa [card_units_of_card_three hK3] at this

open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBOddQuadratic CFSG.ClassicalGroups.Orthogonal QuadraticMap

theorem exists_coords [Finite K] (hK3 : Nat.card K = 3) (R : GL (Fin 4) K)
    (hR : (R : Matrix (Fin 4) (Fin 4) K)ᵀ = (R : Matrix (Fin 4) (Fin 4) K))
    (hno : ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm R x = 0) :
    ∃ (w : K) (P : GL (Fin 4) K), (w = 1 ∨ w = -1) ∧
      (R : Matrix (Fin 4) (Fin 4) K) =
        (P : Matrix (Fin 4) (Fin 4) K)ᵀ * Gc w * (P : Matrix (Fin 4) (Fin 4) K) := by
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have hQ := polarBilin_matrixQuadraticForm_nondegenerate hodd' R hR
  have hdim : Module.finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨w, ha, ⟨e⟩⟩ := exists_plane_binary_isometry hodd (matrixQuadraticForm R) hQ hdim hno
  have hnsq := binary_tail_nonsquare w ha
  have hw : ((w 0 : Kˣ) : K) = ((w 1 : Kˣ) : K) := by
    have h0 : ((w 0 : Kˣ) : K) ^ 2 = 1 := by
      simpa using congrArg Units.val (units_sq_eq_one hK3 (w 0))
    have h1 : ((w 1 : Kˣ) : K) ^ 2 = 1 := by
      simpa using congrArg Units.val (units_sq_eq_one hK3 (w 1))
    simp only [Units.val_div_eq_div_val, Units.val_neg] at hnsq
    rcases sq_eq_one_iff.mp h0 with ha | ha <;> rcases sq_eq_one_iff.mp h1 with hb | hb
    · rw [ha, hb]
    · exfalso
      apply hnsq
      rw [ha, hb]
      exact ⟨1, by norm_num⟩
    · exfalso
      apply hnsq
      rw [ha, hb]
      exact ⟨1, by norm_num⟩
    · rw [ha, hb]
  have h3 : (3 : K) = 0 := by
    have : CharP K 3 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by norm_num) (by rw [hK3]; norm_num : Nat.card K = 3 ^ 1)
    exact_mod_cast CharP.cast_eq_zero K 3
  let ε : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := e.toLinearEquiv.trans (planeBinaryCoordinates 1)
  have hq : ∀ v : Fin 4 → K, v ⬝ᵥ (R : Matrix (Fin 4) (Fin 4) K) *ᵥ v =
      (ε v) ⬝ᵥ Gc ((w 0 : Kˣ) : K) *ᵥ (ε v) := by
    intro v
    have h1 : matrixQuadraticForm R v = v ⬝ᵥ (R : Matrix (Fin 4) (Fin 4) K) *ᵥ v := by
      change matrixForm R v v = _
      exact matrixForm_apply R v v
    rw [← h1, ← e.map_app v]
    rw [QuadraticMap.prod_apply, hyperbolicSumForm_apply, Fin.sum_univ_one,
      weightedSumSquares_apply, Fin.sum_univ_two]
    simp only [ε, LinearEquiv.trans_apply, planeBinaryCoordinates, LinearEquiv.coe_mk,
      Units.smul_def, smul_eq_mul, Gc, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    simp
    linear_combination (((e v).1 0).1 * ((e v).1 0).2) * h3 - ((e v).2 1 * (e v).2 1) * hw
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hodd'
  refine ⟨((w 0 : Kˣ) : K), matrixActionEquiv.symm ε, ?_, ?_⟩
  · have h0 : ((w 0 : Kˣ) : K) ^ 2 = 1 := by
      simpa using congrArg Units.val (units_sq_eq_one hK3 (w 0))
    exact sq_eq_one_iff.mp h0
  · apply eq_of_quad_eq h2 hR
    · simp [Matrix.transpose_mul, Gc_transpose, Matrix.mul_assoc]
    · intro v
      rw [hq v, quad_congr, matrixActionEquiv_symm_mulVec]

theorem conj_sim {n : ℕ} (P Pi M G : Matrix (Fin n) (Fin n) K) (c : K) (hP : P * Pi = 1)
    (hM : Mᵀ * G * M = c • G) :
    (Pi * M * P)ᵀ * (Pᵀ * G * P) * (Pi * M * P) = c • (Pᵀ * G * P) := by
  have h1 : Piᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
  calc (Pi * M * P)ᵀ * (Pᵀ * G * P) * (Pi * M * P)
      = Pᵀ * Mᵀ * (Piᵀ * Pᵀ) * G * (P * Pi) * M * P := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Pᵀ * (Mᵀ * G * M) * P := by
        rw [h1, hP]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = c • (Pᵀ * G * P) := by rw [hM, Matrix.mul_smul, Matrix.smul_mul]

end Explicit

section Char

open CFSG.ComponentClassification.CatalogueBGraphForm

variable {n : ℕ} [Nonempty (Fin n)] {K : Type} [Field K]

noncomputable def mulChar (A : GL (Fin n) K) (h : ∀ c : Kˣ, c ^ 2 = 1) :
    fixedPGL n K A →* Kˣ :=
  (QuotientGroup.lift (similitudeProjection n K A).ker (similitudeMultiplierHom n K A⁻¹) (by
      rw [similitudeProjection_kernel]
      rintro _ ⟨c, rfl⟩
      rw [MonoidHom.mem_ker, similitudeMultiplier_scalar]
      exact h c)).comp (similitudeScalarQuotientEquivFixedPGL n K A).symm.toMonoidHom

theorem mulChar_apply (A : GL (Fin n) K) (h : ∀ c : Kˣ, c ^ 2 = 1) (g : similitudeGroup n K A⁻¹)
    (hmem : ProjGenLinGroup.mk g.val ∈ fixedPGL n K A) :
    mulChar A h ⟨ProjGenLinGroup.mk g.val, hmem⟩ = similitudeMultiplierHom n K A⁻¹ g := by
  have h1 : (⟨ProjGenLinGroup.mk g.val, hmem⟩ : fixedPGL n K A) = similitudeProjection n K A g :=
    Subtype.ext rfl
  have h2 : (similitudeScalarQuotientEquivFixedPGL n K A).symm (similitudeProjection n K A g) =
      QuotientGroup.mk g := (MulEquiv.symm_apply_eq _).mpr rfl
  rw [h1]
  simp only [mulChar, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2, QuotientGroup.lift_mk]

end Char

section Evidence

open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearHigherB

variable {K : Type} [Field K] [Finite K]

theorem nonsplit_evidence (hK3 : Nat.card K = 3) (A : GL (Fin 4) K)
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = (A : Matrix (Fin 4) (Fin 4) K))
    (hno : ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0) :
    OuterEvidence (pureGraphAction 4 K A) := by
  have hR := transpose_inv_of_transpose_eq A hA
  obtain ⟨w, P, hw, hRP⟩ := exists_coords hK3 A⁻¹ hR hno
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hodd'
  have h3 : (3 : K) = 0 := by
    have : CharP K 3 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by norm_num) (by rw [hK3]; norm_num : Nat.card K = 3 ^ 1)
    exact_mod_cast CharP.cast_eq_zero K 3
  have hdet : (Mc : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
    rw [det_Mc h3]; exact one_ne_zero
  let Mg : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Mc hdet
  have hMg : (Mg : Matrix (Fin 4) (Fin 4) K) = Mc := rfl
  let t : GL (Fin 4) K := P⁻¹ * Mg * P
  have ht_val : (t : Matrix (Fin 4) (Fin 4) K) =
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Mc * (P : Matrix (Fin 4) (Fin 4) K) := by
    simp only [t, Units.val_mul, hMg]
  have hPPi : (P : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsim : (t : Matrix (Fin 4) (Fin 4) K)ᵀ * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (t : Matrix (Fin 4) (Fin 4) K) =
      (((-1 : Kˣ) : K)) • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [ht_val, hRP]
    have := conj_sim (P : Matrix (Fin 4) (Fin 4) K) ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      Mc (Gc w) (-1) hPPi (Mc_transpose_Gc_Mc h3 w)
    simpa using this
  have hdett : Matrix.det (t : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [ht_val, Matrix.det_mul, Matrix.det_mul, det_Mc h3]
    have : Matrix.det ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Matrix.det (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    linear_combination this
  have hMM : Mg * Mg = GeneralLinearGroup.scalar (Fin 4) (-1) := by
    apply Units.ext
    rw [Units.val_mul, hMg, Mc_mul_self h3]
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have htsq : t * t = GeneralLinearGroup.scalar (Fin 4) (-1) := by
    have h1 : t * t = P⁻¹ * (Mg * Mg) * P := by simp only [t]; group
    rw [h1, hMM, ← GeneralLinearGroup.scalar_commute (-1) P⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hsimG : t ∈ similitudeGroup 4 K A⁻¹ := (mem_similitudeGroup 4 K A⁻¹ t).2 ⟨-1, hsim⟩
  have hfix : ProjGenLinGroup.mk t ∈ fixedPGL 4 K A :=
    (projective_fixed_iff_similitude 4 K A t).2 hsimG
  have hpsl : ProjGenLinGroup.mk t ∈ pslRange 4 K := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.mk_mem_pslRange_iff_det_power]
    refine ⟨1, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdett]
    simp
  have hunits : ∀ c : Kˣ, c ^ 2 = 1 := units_sq_eq_one hK3
  let e1 := fixedPSLEquivT 4 K A
  let x : fixedPSL 4 K A := e1.symm ⟨⟨ProjGenLinGroup.mk t, hfix⟩, hpsl⟩
  have hex : e1 x = ⟨⟨ProjGenLinGroup.mk t, hfix⟩, hpsl⟩ := e1.apply_symm_apply _
  let ψ : fixedPSL 4 K A →* Kˣ :=
    (mulChar A hunits).comp ((fixedT 4 K A).subtype.comp e1.toMonoidHom)
  have hψx : ψ x = similitudeMultiplierHom 4 K A⁻¹ ⟨t, hsimG⟩ := by
    change mulChar A hunits (e1 x).val = _
    rw [hex]
    exact mulChar_apply A hunits ⟨t, hsimG⟩ hfix
  have hmult : similitudeMultiplierHom 4 K A⁻¹ ⟨t, hsimG⟩ = -1 :=
    similitudeMultiplier_unique_matrix 4 K A⁻¹ ⟨t, hsimG⟩ (-1) hsim
  have hψne : ψ x ≠ 1 := by
    rw [hψx, hmult]
    intro h
    apply h2
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hx1 : x ≠ 1 := fun h => hψne (by rw [h, map_one])
  have hx2 : x ^ 2 = 1 := by
    apply e1.injective
    rw [map_pow, hex, map_one]
    apply Subtype.ext
    apply Subtype.ext
    change (ProjGenLinGroup.mk t) ^ 2 = 1
    rw [← map_pow, sq, htsq, ProjGenLinGroup.mk_scalar]
  exact ⟨x, Kˣ, inferInstance, ψ, orderOf_eq_prime hx2 hx1, hψne⟩

end Evidence

end Graph4

end CFSG.ComponentClassification.CatFC.PSLSmall

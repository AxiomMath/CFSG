module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Order8Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph4Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatFC
open CFSG.ComponentClassification.CatFC.PSLSmall
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Two

open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatLeafProof (psl_two_normal_form)

noncomputable def diagGL {F : Type} [Field F] (b : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(b : F), 1])
    (by rw [Matrix.det_diagonal, Fin.prod_univ_two]; simp)

theorem diagGL_pow_val {F : Type} [Field F] (b : Fˣ) (k : ℕ) :
    ((diagGL b ^ k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![((b ^ k : Fˣ) : F), 1] := by
  rw [Units.val_pow_eq_pow_val]
  change (Matrix.diagonal ![(b : F), 1]) ^ k = _
  rw [Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> simp

theorem mk_diagGL_pow_eq_one_iff {F : Type} [Field F] (b : Fˣ) (k : ℕ) :
    (ProjGenLinGroup.mk (diagGL b) : ProjGenLinGroup (Fin 2) F) ^ k = 1 ↔ b ^ k = 1 := by
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨u, hu⟩
    have hu' : ((GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        Matrix.diagonal ![((b ^ k : Fˣ) : F), 1] := by
      rw [← diagGL_pow_val, hu]
    have h0 := congrFun (congrFun hu' 0) 0
    have h1 := congrFun (congrFun hu' 1) 1
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h0 h1
    apply Units.ext
    simp [← h0, h1]
  · intro h
    refine ⟨1, ?_⟩
    apply Units.ext
    rw [diagGL_pow_val, h]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]

theorem orderOf_mk_diagGL {F : Type} [Field F] (b : Fˣ) (hb : orderOf b = 8) :
    orderOf (ProjGenLinGroup.mk (diagGL b) : ProjGenLinGroup (Fin 2) F) = 8 := by
  have h8 : (ProjGenLinGroup.mk (diagGL b) : ProjGenLinGroup (Fin 2) F) ^ 8 = 1 := by
    rw [mk_diagGL_pow_eq_one_iff, ← hb]
    exact pow_orderOf_eq_one b
  have h4 : ¬ (ProjGenLinGroup.mk (diagGL b) : ProjGenLinGroup (Fin 2) F) ^ 4 = 1 := by
    rw [mk_diagGL_pow_eq_one_iff]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hb]; norm_num)
  exact orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8

variable {K : Type} [Field K] [Finite K]

theorem exists_fixedPSL_orderOf_eq (hK : Nat.card K = 81) {τ : K ≃+* K} (hτ2 : τ ^ 2 = 1)
    (hτ : τ ≠ 1) (x₀ : ProjGenLinGroup (Fin 2) (fixedField K τ)) :
    ∃ x : fixedPSL 2 K τ, orderOf x = orderOf x₀ := by
  have hoddK : Odd (Nat.card K) := by rw [hK]; decide
  have hodd := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hoddK
  let e1 := fixedPSLEquivT 2 K τ
  let e2 := subfieldPGLEquivFixed (Fin 2) K τ
  let ι : fixedPSL 2 K τ →* ProjGenLinGroup (Fin 2) (fixedField K τ) :=
    e2.symm.toMonoidHom.comp ((fixedT 2 K τ).subtype.comp e1.toMonoidHom)
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : ((fixedT 2 K τ).subtype.comp e1.toMonoidHom) a =
        ((fixedT 2 K τ).subtype.comp e1.toMonoidHom) b := e2.symm.injective hab
    exact e1.injective (Subtype.val_injective h1)
  have hmem : e2 x₀ ∈ fixedT 2 K τ := by
    obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective x₀
    change (e2 (ProjGenLinGroup.mk B)).val ∈ pslRange 2 K
    rw [subfieldPGLEquivFixed_val, subfield_projectivity_mem_pslRange_iff]
    exact exists_sq_of_fixedField hodd hτ2 hτ (Matrix.GeneralLinearGroup.det B)
  let x : fixedPSL 2 K τ := e1.symm ⟨e2 x₀, hmem⟩
  have hιx : ι x = x₀ := by
    change e2.symm ((fixedT 2 K τ).subtype (e1 (e1.symm ⟨e2 x₀, hmem⟩))) = x₀
    rw [MulEquiv.apply_symm_apply]
    exact e2.symm_apply_apply x₀
  exact ⟨x, by rw [← orderOf_injective ι hι x, hιx]⟩

theorem hasOrder8_pslFieldAut_two (hK : Nat.card K = 81) {τ : K ≃+* K} (hτ2 : τ ^ 2 = 1)
    (hτ : τ ≠ 1) : HasOrder8 (pslFieldAut (Fin 2) K τ) := by
  have hcard := fixedField_card_square K τ hτ2 hτ
  have hq0 : Nat.card (fixedField K τ) = 9 := by
    have h2 : Nat.card (fixedField K τ) ^ 2 = 9 ^ 2 := by
      rw [← hcard, hK]
      norm_num
    exact Nat.pow_left_injective two_ne_zero h2
  obtain ⟨b, hb⟩ : ∃ b : (fixedField K τ)ˣ, orderOf b = 8 := by
    obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (fixedField K τ)ˣ)
    exact ⟨b, by rw [hb, Nat.card_units, hq0]⟩
  obtain ⟨x, hx⟩ := exists_fixedPSL_orderOf_eq hK hτ2 hτ (ProjGenLinGroup.mk (diagGL b))
  exact ⟨x, hx.trans (orderOf_mk_diagGL b hb)⟩

end Two

section Four

open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatFC.PSLSmall.Graph4

section Explicit

variable {K : Type} [Field K]

@[expose] def Tc : Matrix (Fin 4) (Fin 4) K :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, -1; 0, 0, 1, 1]

@[expose] def Tc2 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

@[expose] def Tc4 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

theorem Tc_transpose_Gc_Tc (h3 : (3 : K) = 0) (w : K) :
    (Tc : Matrix (Fin 4) (Fin 4) K)ᵀ * Gc w * Tc = (-1 : K) • Gc w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tc, Gc, Matrix.mul_apply, Fin.sum_univ_four] <;>
    linear_combination (w) * h3

theorem det_Tc (h3 : (3 : K) = 0) : (Tc : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  simp [Tc, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (-1 : K) * h3

theorem Tc_mul_self (h3 : (3 : K) = 0) : (Tc : Matrix (Fin 4) (Fin 4) K) * Tc = Tc2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tc, Tc2, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination h3 | linear_combination (-1 : K) * h3

theorem Tc2_mul_self : (Tc2 : Matrix (Fin 4) (Fin 4) K) * Tc2 = Tc4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tc2, Tc4, Matrix.mul_apply, Fin.sum_univ_four]

theorem Tc4_mul_self : (Tc4 : Matrix (Fin 4) (Fin 4) K) * Tc4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tc4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem Tc_sq (h3 : (3 : K) = 0) : (Tc : Matrix (Fin 4) (Fin 4) K) ^ 2 = Tc2 := by
  rw [pow_two]
  exact Tc_mul_self h3

theorem Tc_pow_four (h3 : (3 : K) = 0) : (Tc : Matrix (Fin 4) (Fin 4) K) ^ 4 = Tc4 := by
  have h : (Tc : Matrix (Fin 4) (Fin 4) K) ^ 4 = (Tc ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, Tc_sq h3, pow_two]
  exact Tc2_mul_self

theorem Tc_pow_eight (h3 : (3 : K) = 0) : (Tc : Matrix (Fin 4) (Fin 4) K) ^ 8 = 1 := by
  have h : (Tc : Matrix (Fin 4) (Fin 4) K) ^ 8 = (Tc ^ 4) ^ 2 := by rw [← pow_mul]
  rw [h, Tc_pow_four h3, pow_two]
  exact Tc4_mul_self

end Explicit

variable {K : Type} [Field K] [Finite K]

theorem nonsplit_hasOrder8 (hK3 : Nat.card K = 3) (A : GL (Fin 4) K)
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = (A : Matrix (Fin 4) (Fin 4) K))
    (hno : ¬ ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
      ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0) :
    HasOrder8 (pureGraphAction 4 K A) := by
  have hR := transpose_inv_of_transpose_eq A hA
  obtain ⟨w, P, hw, hRP⟩ := exists_coords hK3 A⁻¹ hR hno
  have hodd : Odd (Nat.card K) := by rw [hK3]; decide
  have hodd' := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hodd'
  have h3 : (3 : K) = 0 := by
    have : CharP K 3 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_three (by norm_num) (by rw [hK3]; norm_num : Nat.card K = 3 ^ 1)
    exact_mod_cast CharP.cast_eq_zero K 3
  have hdet : (Tc : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
    rw [det_Tc h3]; exact one_ne_zero
  let Tg : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Tc hdet
  have hTg : (Tg : Matrix (Fin 4) (Fin 4) K) = Tc := rfl
  let t : GL (Fin 4) K := P⁻¹ * Tg * P
  have ht_val : (t : Matrix (Fin 4) (Fin 4) K) =
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Tc * (P : Matrix (Fin 4) (Fin 4) K) := by
    simp only [t, Units.val_mul, hTg]
  have hPPi : (P : Matrix (Fin 4) (Fin 4) K) *
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsim : (t : Matrix (Fin 4) (Fin 4) K)ᵀ *
      ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (t : Matrix (Fin 4) (Fin 4) K) =
      (((-1 : Kˣ) : K)) • ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [ht_val, hRP]
    have := conj_sim (P : Matrix (Fin 4) (Fin 4) K)
      ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) Tc (Gc w) (-1) hPPi
      (Tc_transpose_Gc_Tc h3 w)
    simpa using this
  have hdett : Matrix.det (t : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [ht_val, Matrix.det_mul, Matrix.det_mul, det_Tc h3]
    have : Matrix.det ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Matrix.det (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    linear_combination this
  have htpow : ∀ n : ℕ, t ^ n = P⁻¹ * Tg ^ n * P := by
    intro n
    have := conj_pow (a := P⁻¹) (b := Tg) (i := n)
    rwa [inv_inv] at this
  have hTg8 : Tg ^ 8 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hTg, Tc_pow_eight h3, Units.val_one]
  have ht8 : t ^ 8 = 1 := by
    rw [htpow, hTg8]; group
  have ht4 : t ^ 4 ∉ Subgroup.center (GL (Fin 4) K) := by
    intro hz
    have hc := Subgroup.mem_center_iff.1 hz P
    have hTg4 : Tg ^ 4 ∈ Subgroup.center (GL (Fin 4) K) := by
      have h1 : Tg ^ 4 = P * t ^ 4 * P⁻¹ := by rw [htpow]; group
      have h2' : P * t ^ 4 * P⁻¹ = t ^ 4 := by rw [hc]; group
      rw [h1, h2']
      exact hz
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hTg4
    obtain ⟨u, hu⟩ := hTg4
    have hu' : ((Matrix.GeneralLinearGroup.scalar (Fin 4) u : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Tc4 := by
      rw [hu, Units.val_pow_eq_pow_val, hTg, Tc_pow_four h3]
    have h00 : (u : K) = 1 := by
      have := congrFun (congrFun hu' 0) 0
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Tc4] using this
    have h22 : (u : K) = -1 := by
      have := congrFun (congrFun hu' 2) 2
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Tc4] using this
    apply h2
    linear_combination h22 - h00
  have hsimG : t ∈ similitudeGroup 4 K A⁻¹ := (mem_similitudeGroup 4 K A⁻¹ t).2 ⟨-1, hsim⟩
  have hfix : ProjGenLinGroup.mk t ∈ fixedPGL 4 K A :=
    (projective_fixed_iff_similitude 4 K A t).2 hsimG
  have hpsl : ProjGenLinGroup.mk t ∈ pslRange 4 K := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.mk_mem_pslRange_iff_det_power]
    refine ⟨1, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdett]
    simp
  let e1 := fixedPSLEquivT 4 K A
  let x : fixedPSL 4 K A := e1.symm ⟨⟨ProjGenLinGroup.mk t, hfix⟩, hpsl⟩
  have hex : e1 x = ⟨⟨ProjGenLinGroup.mk t, hfix⟩, hpsl⟩ := e1.apply_symm_apply _
  have hx8 : x ^ 8 = 1 := by
    apply e1.injective
    rw [map_pow, hex, map_one]
    apply Subtype.ext
    apply Subtype.ext
    change (ProjGenLinGroup.mk t) ^ 8 = 1
    rw [← map_pow, ht8, map_one]
  have hx4 : ¬ x ^ 4 = 1 := by
    intro h
    have h1 : e1 (x ^ 4) = 1 := by rw [h, map_one]
    rw [map_pow, hex] at h1
    have h1' := congrArg (fun y : fixedT 4 K A => (y.val.val : ProjGenLinGroup (Fin 4) K)) h1
    have h1'' : (ProjGenLinGroup.mk t) ^ 4 = 1 := h1'
    rw [← map_pow, ProjGenLinGroup.mk_eq_one] at h1''
    exact ht4 h1''
  exact ⟨x, orderOf_eq_prime_pow (p := 2) (n := 2) hx4 hx8⟩

end Four

end CFSG.EvenSporadicStandard.M24Std.KForm

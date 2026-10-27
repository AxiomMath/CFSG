module

public import CFSG.GH74.Generic.S1.LinForm
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.GH74.Generic.Front.InvolutionLA
public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix CFSG.GH74.L5U5 CFSG.GH74.Generic
open scoped MatrixGroups


variable {F : Type} [Field F]

theorem slConj_toGL (h : SL(4, F)) :
    CatalogueBHigherLinearAction.slConjugation 4 F (Matrix.SpecialLinearGroup.toGL h) =
      MulAut.conj h := by
  ext g : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
    map_inv]

theorem slGraph_slConj_slGraph [Finite F] (A : GL (Fin 4) F) :
    CatalogueBGraphForm.slGraphAut 4 F * CatalogueBHigherLinearAction.slConjugation 4 F A *
        CatalogueBGraphForm.slGraphAut 4 F =
      CatalogueBHigherLinearAction.slConjugation 4 F (GeneralLinearGroup.inverseTranspose A) := by
  have hn3 : 3 ≤ 4 := by norm_num
  apply eq_of_descendAut_eq hn3
  have htrans := standard_automorphism_transport (K := F) (n := 4)
  rw [map_mul, map_mul]
  exact htrans.2.2.2.2.1 A

theorem slGraph_sq (n : ℕ) :
    CatalogueBGraphForm.slGraphAut n F * CatalogueBGraphForm.slGraphAut n F = 1 := by
  ext g : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [MulAut.mul_apply, CatalogueBGraphForm.toGL_slGraphAut, CatalogueBGraphForm.toGL_slGraphAut]
  exact GeneralLinearGroup.inverseTranspose_inverseTranspose _



theorem ringChar_ne_two_of_mod_four [Finite F] (hF : Nat.card F % 4 = 3) : ringChar F ≠ 2 := by
  have := Fintype.ofFinite F
  intro h
  have h1 := (FiniteField.even_card_iff_char_two (F := F)).1 h
  rw [Fintype.card_eq_nat_card] at h1
  omega

theorem exists_pow_four_of_isSquare [Finite F] (hF : Nat.card F % 4 = 3) {x : F} (hx : x ≠ 0)
    (hsq : IsSquare x) : ∃ ν : F, ν ≠ 0 ∧ ν ^ 4 = x := by
  classical
  have := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_mod_four hF
  have hx1 : x ^ (Fintype.card F / 2) = 1 := (FiniteField.isSquare_iff hchar hx).1 hsq
  rw [Fintype.card_eq_nat_card] at hx1
  obtain ⟨t, ht⟩ : ∃ t, Nat.card F = 4 * t + 3 := ⟨Nat.card F / 4, by omega⟩
  rw [ht, show (4 * t + 3) / 2 = 2 * t + 1 by omega] at hx1
  obtain ⟨μ, hμ⟩ := hsq
  have hμ0 : μ ≠ 0 := by rintro rfl; apply hx; rw [hμ]; simp
  refine ⟨μ ^ (t + 1), pow_ne_zero _ hμ0, ?_⟩
  have h2 : x = x ^ (2 * t + 2) := by
    calc x = x ^ (2 * t + 1) * x := by rw [hx1, one_mul]
      _ = x ^ (2 * t + 2) := by rw [← pow_succ]
  rw [h2, hμ]
  ring

theorem slConj_eq_conj_of_isSquare [Finite F] (hF : Nat.card F % 4 = 3) (A : GL (Fin 4) F)
    (h : IsSquare (A : Matrix (Fin 4) (Fin 4) F).det) :
    ∃ s : SL(4, F), CatalogueBHigherLinearAction.slConjugation 4 F A = MulAut.conj s := by
  have hdet0 : (A : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
  obtain ⟨ν, hν0, hν⟩ := exists_pow_four_of_isSquare hF hdet0 h
  let c : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 ν⁻¹ (inv_ne_zero hν0))
  let M : Matrix (Fin 4) (Fin 4) F := (ν⁻¹) • (A : Matrix (Fin 4) (Fin 4) F)
  have hM : M.det = 1 := by
    rw [Matrix.det_smul, ← hν]
    simp only [Fintype.card_fin]
    field_simp
  let s : SL(4, F) := ⟨M, hM⟩
  refine ⟨s, ?_⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = c * A := by
    apply Units.ext
    simp [c, s, M, Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul]
    rfl
  have hcc : ∀ g : GL (Fin 4) F, c * g = g * c := fun g => by
    apply Units.ext
    ext i j
    simp [c, Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_mul, Matrix.mul_diagonal,
      mul_comm]
  ext g : 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul, map_inv,
    hs]
  have hX := hcc (A * Matrix.SpecialLinearGroup.toGL g * A⁻¹)
  calc A * Matrix.SpecialLinearGroup.toGL g * A⁻¹
      = (A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ * c) * c⁻¹ := by group
    _ = c * (A * Matrix.SpecialLinearGroup.toGL g * A⁻¹) * c⁻¹ := by rw [hX]
    _ = _ := by group




noncomputable def rWSub (n : ℕ) (F : Type) [Field F] : Subgroup (MulAut (projectiveSL n F)) where
  carrier := {x | ∃ (B : GL (Fin n) F) (e : ℕ), e ≤ 1 ∧ x = conjAut n F B * dualAut n F ^ e}
  mul_mem' := by
    rintro _ _ ⟨B, e, he, rfl⟩ ⟨C, f, hf, rfl⟩
    have htrans := standard_automorphism_transport (K := F) (n := n)
    have hδ2 : dualAut n F * dualAut n F = 1 := htrans.2.2.2.1
    have hδc : ∀ A : GL (Fin n) F, dualAut n F * conjAut n F A * dualAut n F =
      conjAut n F (GeneralLinearGroup.inverseTranspose A) := htrans.2.2.2.2.1
    have hcc : ∀ A B : GL (Fin n) F, conjAut n F A * conjAut n F B = conjAut n F (A * B) :=
      htrans.1
    have hδc' : ∀ A : GL (Fin n) F, dualAut n F * conjAut n F A =
        conjAut n F (GeneralLinearGroup.inverseTranspose A) * dualAut n F := by
      intro A
      calc dualAut n F * conjAut n F A = dualAut n F * conjAut n F A * (dualAut n F * dualAut n F) := by
            rw [hδ2, mul_one]
        _ = (dualAut n F * conjAut n F A * dualAut n F) * dualAut n F := by simp only [mul_assoc]
        _ = _ := by rw [hδc]
    interval_cases e <;> interval_cases f
    · refine ⟨B * C, 0, by norm_num, ?_⟩
      simp only [pow_zero, mul_one]
      exact hcc B C
    · refine ⟨B * C, 1, by norm_num, ?_⟩
      simp only [pow_zero, pow_one, mul_one]
      rw [← hcc B C]
      simp only [mul_assoc]
    · refine ⟨B * GeneralLinearGroup.inverseTranspose C, 1, by norm_num, ?_⟩
      simp only [pow_one, pow_zero, mul_one]
      calc conjAut n F B * dualAut n F * conjAut n F C
          = conjAut n F B * (dualAut n F * conjAut n F C) := by simp only [mul_assoc]
        _ = conjAut n F B * (conjAut n F (GeneralLinearGroup.inverseTranspose C) * dualAut n F) := by
            rw [hδc']
        _ = conjAut n F B * conjAut n F (GeneralLinearGroup.inverseTranspose C) * dualAut n F := by
            simp only [mul_assoc]
        _ = _ := by rw [hcc]
    · refine ⟨B * GeneralLinearGroup.inverseTranspose C, 0, by norm_num, ?_⟩
      simp only [pow_one, pow_zero, mul_one]
      calc conjAut n F B * dualAut n F * (conjAut n F C * dualAut n F)
          = conjAut n F B * (dualAut n F * conjAut n F C) * dualAut n F := by simp only [mul_assoc]
        _ = conjAut n F B * (conjAut n F (GeneralLinearGroup.inverseTranspose C) * dualAut n F) *
              dualAut n F := by rw [hδc']
        _ = conjAut n F B * conjAut n F (GeneralLinearGroup.inverseTranspose C) *
              (dualAut n F * dualAut n F) := by simp only [mul_assoc]
        _ = _ := by rw [hδ2, mul_one, hcc]
  one_mem' := ⟨1, 0, by norm_num, by simp⟩
  inv_mem' := by
    rintro _ ⟨B, e, he, rfl⟩
    have htrans := standard_automorphism_transport (K := F) (n := n)
    have hδ2 : dualAut n F * dualAut n F = 1 := htrans.2.2.2.1
    have hδc : ∀ A : GL (Fin n) F, dualAut n F * conjAut n F A * dualAut n F =
      conjAut n F (GeneralLinearGroup.inverseTranspose A) := htrans.2.2.2.2.1
    have hδc' : ∀ A : GL (Fin n) F, dualAut n F * conjAut n F A =
        conjAut n F (GeneralLinearGroup.inverseTranspose A) * dualAut n F := by
      intro A
      calc dualAut n F * conjAut n F A = dualAut n F * conjAut n F A * (dualAut n F * dualAut n F) := by
            rw [hδ2, mul_one]
        _ = (dualAut n F * conjAut n F A * dualAut n F) * dualAut n F := by simp only [mul_assoc]
        _ = _ := by rw [hδc]
    have hδinv : (dualAut n F)⁻¹ = dualAut n F := inv_eq_of_mul_eq_one_right hδ2
    interval_cases e
    · exact ⟨B⁻¹, 0, by norm_num, by simp⟩
    · refine ⟨GeneralLinearGroup.inverseTranspose B⁻¹, 1, by norm_num, ?_⟩
      simp only [pow_one]
      calc (conjAut n F B * dualAut n F)⁻¹ = (dualAut n F)⁻¹ * (conjAut n F B)⁻¹ :=
            _root_.mul_inv_rev _ _
        _ = dualAut n F * conjAut n F B⁻¹ := by rw [hδinv, ← map_inv]
        _ = _ := hδc' B⁻¹


theorem rconj_pow_mem {R : Type*} [Group R] (W : Subgroup R) (g : R)
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∀ (k : ℕ) (w : R), w ∈ W → g ^ k * w * (g ^ k)⁻¹ ∈ W := by
  intro k
  induction k with
  | zero => intro w hw; simpa using hw
  | succ k ih =>
    intro w hw
    have := hg _ (ih w hw)
    have e : g ^ (k + 1) * w * (g ^ (k + 1))⁻¹ = g * (g ^ k * w * (g ^ k)⁻¹) * g⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]; group
    rw [e]; exact this

theorem rmul_pow_mem {R : Type*} [Group R] (W : Subgroup R) (g : R)
    (hg : ∀ w ∈ W, g * w * g⁻¹ ∈ W) (w : R) (hw : w ∈ W) (k : ℕ) :
    ∃ w' ∈ W, (w * g) ^ k = w' * g ^ k := by
  induction k with
  | zero => exact ⟨1, W.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨w', hw', h⟩ := ih
    refine ⟨w' * (g ^ k * w * (g ^ k)⁻¹), W.mul_mem hw' (rconj_pow_mem W g hg k w hw), ?_⟩
    rw [pow_succ, h]; group



theorem mem_wSub_of_form {n : ℕ} [Finite F] (hodd : Odd (Nat.card (F ≃+* F)))
    (A : GL (Fin n) F) (σ : F ≃+* F) (ε : ℕ) (hε : ε ≤ 1) (m : ℕ)
    (hm : (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε) ^ (2 ^ m) = 1) :
    conjAut n F A * fieldAut n F σ * dualAut n F ^ ε ∈ rWSub n F := by
  have htrans := standard_automorphism_transport (K := F) (n := n)
  have hδ2 : dualAut n F * dualAut n F = 1 := htrans.2.2.2.1
  have hδf : ∀ σ : F ≃+* F, dualAut n F * fieldAut n F σ * dualAut n F = fieldAut n F σ :=
    htrans.2.2.2.2.2.1
  have hδfc : ∀ σ : F ≃+* F, fieldAut n F σ * dualAut n F = dualAut n F * fieldAut n F σ := by
    intro σ
    calc fieldAut n F σ * dualAut n F
        = (dualAut n F * dualAut n F) * fieldAut n F σ * dualAut n F := by rw [hδ2, one_mul]
      _ = dualAut n F * (dualAut n F * fieldAut n F σ * dualAut n F) := by simp only [mul_assoc]
      _ = _ := by rw [hδf]
  set g : MulAut (projectiveSL n F) := fieldAut n F σ with hg
  set w : MulAut (projectiveSL n F) := conjAut n F A * dualAut n F ^ ε with hw
  have hwW : w ∈ rWSub n F := ⟨A, ε, hε, rfl⟩
  have hgn : ∀ x ∈ rWSub n F, g * x * g⁻¹ ∈ rWSub n F := by
    rintro _ ⟨B, e, he, rfl⟩
    refine ⟨GeneralLinearGroup.map (σ : F →+* F) B, e, he, ?_⟩
    have hδe : ∀ e : ℕ, g * dualAut n F ^ e = dualAut n F ^ e * g := by
      intro e
      induction e with
      | zero => simp
      | succ e ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hδfc σ, ← mul_assoc, ← pow_succ] 
    calc g * (conjAut n F B * dualAut n F ^ e) * g⁻¹
        = (g * conjAut n F B * g⁻¹) * (g * dualAut n F ^ e * g⁻¹) := by group
      _ = _ := by rw [htrans.2.2.1 σ B, hδe e]; group
  have hx : conjAut n F A * fieldAut n F σ * dualAut n F ^ ε = w * g := by
    have hδe : ∀ e : ℕ, fieldAut n F σ * dualAut n F ^ e = dualAut n F ^ e * fieldAut n F σ := by
      intro e
      induction e with
      | zero => simp
      | succ e ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hδfc σ, ← mul_assoc, ← pow_succ]
    rw [hw, hg, mul_assoc, hδe ε]; simp only [mul_assoc]
  rw [hx] at hm ⊢
  set x := w * g with hxdef
  obtain ⟨w', hw', hwk⟩ := rmul_pow_mem (rWSub n F) g hgn w hwW (Nat.card (F ≃+* F))
  have hgN : g ^ Nat.card (F ≃+* F) = 1 := by
    rw [hg, ← map_pow, pow_card_eq_one', map_one]
  have hxN : x ^ Nat.card (F ≃+* F) ∈ rWSub n F := by
    rw [hxdef, hwk, hgN, mul_one]; exact hw'
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp at hm; rw [hm]; exact (rWSub n F).one_mem
  · have hcop : Nat.Coprime (Nat.card (F ≃+* F)) (2 ^ m) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
      (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hmpos))
    have hxu : x = (x ^ Nat.card (F ≃+* F)) ^ u := by
      rw [← pow_mul]
      have h1 : Nat.card (F ≃+* F) * u = 1 + 2 ^ m * (Nat.card (F ≃+* F) * u / 2 ^ m) := by
        have := Nat.div_add_mod (Nat.card (F ≃+* F) * u) (2 ^ m)
        rw [hu] at this
        omega
      rw [h1, pow_add, pow_mul, hm, one_pow, mul_one, pow_one]
    rw [hxu]
    exact (rWSub n F).pow_mem hxN u



theorem odd_card_ringEquiv [Finite F] (hF : Nat.card F % 4 = 3) :
    Odd (Nat.card (F ≃+* F)) := by
  by_contra h
  have hev : 2 ∣ Nat.card (F ≃+* F) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ]; exact pow_orderOf_eq_one σ
  have := eq_one_of_mul_self_eq_one hF σ hσ2
  rw [this, orderOf_one] at hσ
  omega

theorem aut2_lin_form [Finite F] (hF : Nat.card F % 4 = 3) (β : MulAut SL(4, F)) (m : ℕ)
    (hβ : β ^ (2 ^ m) = 1) :
    ∃ (A : GL (Fin 4) F) (e : ℕ), e ≤ 1 ∧
      β = CatalogueBHigherLinearAction.slConjugation 4 F A *
        CatalogueBGraphForm.slGraphAut 4 F ^ e := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨A, σ, ε, hε, hP⟩ :=
    (LinearFlag.automorphism_generation (K := F) (n := 4) hn3).2 (descendAut 4 F β)
  have hm : (descendAut 4 F β) ^ (2 ^ m) = 1 := by rw [← map_pow, hβ, map_one]
  rw [hP] at hm
  have hW := mem_wSub_of_form (n := 4) (odd_card_ringEquiv hF) A σ ε hε m hm
  rw [← hP] at hW
  obtain ⟨B, e, he, hBe⟩ := hW
  refine ⟨B, e, he, ?_⟩
  apply eq_of_descendAut_eq hn3
  rw [hBe, map_mul, map_pow]
  rfl




theorem rblk4_transpose (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y)ᵀ = blk4 Xᵀ Yᵀ := by
  rw [blk4_eq_reindex, blk4_eq_reindex]
  simp [Matrix.coe_reindexAlgEquiv, Matrix.fromBlocks_transpose]

@[expose] def J2mat : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

theorem J2mat_transpose : (J2mat : Matrix (Fin 2) (Fin 2) F)ᵀ = -J2mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2mat]

theorem J2mat_mul_self : (J2mat : Matrix (Fin 2) (Fin 2) F) * J2mat = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J2mat, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_J2mat : (J2mat : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [J2mat, Matrix.det_fin_two]

theorem mul_J2mat_mul_transpose (X : Matrix (Fin 2) (Fin 2) F) :
    X * J2mat * Xᵀ = X.det • J2mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J2mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

@[expose] def Jsl : SL(4, F) :=
  ⟨blk4 J2mat J2mat, by rw [det_blk4, det_J2mat, one_mul]⟩

theorem Jsl_val : ((Jsl : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = blk4 J2mat J2mat := rfl

@[expose] def rNegOne : SL(4, F) :=
  ⟨-1, by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩

theorem Jsl_sq : (Jsl : SL(4, F)) * Jsl = rNegOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Jsl_val, blk4_mul, J2mat_mul_self]
  have : (blk4 (-1) (-1) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rw [show (-1 : Matrix (Fin 2) (Fin 2) F) = -(1 : Matrix (Fin 2) (Fin 2) F) from rfl,
      blk4_neg, blk4_one]
  exact this



theorem rNegOne_val : ((rNegOne : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := rfl

theorem rNegOne_sq : (rNegOne : SL(4, F)) * rNegOne = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rNegOne_val, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem rNegOne_inv : (rNegOne : SL(4, F))⁻¹ = rNegOne := inv_eq_of_mul_eq_one_right rNegOne_sq

theorem conj_rNegOne : (MulAut.conj (rNegOne : SL(4, F)) : MulAut SL(4, F)) = 1 := by
  ext g : 1
  apply Subtype.ext
  rw [MulAut.conj_apply, rNegOne_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, rNegOne_val, MulAut.one_apply]
  simp

theorem Jsl_inv : (Jsl : SL(4, F))⁻¹ = Jsl * rNegOne := by
  apply inv_eq_of_mul_eq_one_right
  calc Jsl * (Jsl * rNegOne) = (Jsl * Jsl) * rNegOne := by rw [mul_assoc]
    _ = 1 := by rw [Jsl_sq, rNegOne_sq]

theorem slGraph_conj_slGraph [Finite F] (s : SL(4, F)) :
    CatalogueBGraphForm.slGraphAut 4 F * MulAut.conj s * CatalogueBGraphForm.slGraphAut 4 F =
      MulAut.conj (CatalogueBGraphForm.slGraphAut 4 F s) := by
  have h := slGraph_slConj_slGraph (F := F) (Matrix.SpecialLinearGroup.toGL s)
  rw [slConj_toGL] at h
  rw [h]
  have h2 : GeneralLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.SpecialLinearGroup.toGL (CatalogueBGraphForm.slGraphAut 4 F s) :=
    (CatalogueBGraphForm.toGL_slGraphAut 4 F s).symm
  rw [h2, slConj_toGL]

theorem slGraph_Jsl : CatalogueBGraphForm.slGraphAut 4 F (Jsl : SL(4, F)) = Jsl := by
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, Jsl_inv, Matrix.SpecialLinearGroup.coe_mul, Jsl_val]
  simp only [rNegOne]
  rw [Matrix.mul_neg, Matrix.mul_one, Matrix.transpose_neg, rblk4_transpose, J2mat_transpose,
    ← blk4_neg, neg_neg]

@[expose] def tauJ (F : Type) [Field F] : MulAut SL(4, F) :=
  MulAut.conj (Jsl : SL(4, F)) * CatalogueBGraphForm.slGraphAut 4 F

theorem tauJ_apply (k : SL(4, F)) :
    tauJ F k = Jsl * CatalogueBGraphForm.slGraphAut 4 F k * Jsl⁻¹ := rfl

theorem tauJ_sq [Finite F] : tauJ F * tauJ F = 1 := by
  have h1 : tauJ F * tauJ F = MulAut.conj (Jsl : SL(4, F)) *
      (CatalogueBGraphForm.slGraphAut 4 F * MulAut.conj (Jsl : SL(4, F)) *
        CatalogueBGraphForm.slGraphAut 4 F) := by
    unfold tauJ; simp only [mul_assoc]
  rw [h1, slGraph_conj_slGraph, slGraph_Jsl, ← map_mul, Jsl_sq, conj_rNegOne]

theorem tauJ_fix (k : SL(4, F))
    (hk : (k : Matrix (Fin 4) (Fin 4) F) * blk4 J2mat J2mat * (k : Matrix (Fin 4) (Fin 4) F)ᵀ =
      blk4 J2mat J2mat) : tauJ F k = k := by
  have hQP : ((k⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have key : Jsl * CatalogueBGraphForm.slGraphAut 4 F k = k * Jsl := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      CatalogueBGraphForm.slGraphAut_matrix, Jsl_val]
    calc blk4 J2mat J2mat * ((k⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ
        = ((k : Matrix (Fin 4) (Fin 4) F) * blk4 J2mat J2mat * (k : Matrix (Fin 4) (Fin 4) F)ᵀ) *
            ((k⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [hk]
      _ = (k : Matrix (Fin 4) (Fin 4) F) * blk4 J2mat J2mat *
            ((k : Matrix (Fin 4) (Fin 4) F)ᵀ * ((k⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (k : Matrix (Fin 4) (Fin 4) F) * blk4 J2mat J2mat *
            (((k⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F))ᵀ := by
          rw [Matrix.transpose_mul]
      _ = (k : Matrix (Fin 4) (Fin 4) F) * blk4 J2mat J2mat := by
          rw [hQP, Matrix.transpose_one, Matrix.mul_one]
  rw [tauJ_apply, key, mul_inv_cancel_right]

@[expose] def blkSL4 (A B : SL(2, F)) : SL(4, F) :=
  ⟨blk4 (A : Matrix (Fin 2) (Fin 2) F) (B : Matrix (Fin 2) (Fin 2) F), by
    rw [det_blk4, A.det_coe, B.det_coe, one_mul]⟩

theorem blkSL4_val (A B : SL(2, F)) :
    ((blkSL4 A B : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blk4 (A : Matrix (Fin 2) (Fin 2) F) (B : Matrix (Fin 2) (Fin 2) F) := rfl

theorem blkSL4_mul (A A' B B' : SL(2, F)) :
    blkSL4 A B * blkSL4 A' B' = blkSL4 (A * A') (B * B') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, blkSL4_val, blkSL4_val, blkSL4_val, blk4_mul]
  rfl

theorem blkSL4_one : blkSL4 (1 : SL(2, F)) 1 = 1 := by
  apply Subtype.ext
  simp only [blkSL4_val, Matrix.SpecialLinearGroup.coe_one]
  exact blk4_one

theorem blkSL4_inj {A B A' B' : SL(2, F)} (h : blkSL4 A B = blkSL4 A' B') : A = A' ∧ B = B' := by
  have h' := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) h
  simp only [blkSL4_val] at h'
  obtain ⟨h1, h2⟩ := blk4_inj h'
  exact ⟨Subtype.ext h1, Subtype.ext h2⟩

theorem blkSL4_fix (A B : SL(2, F)) : tauJ F (blkSL4 A B) = blkSL4 A B := by
  apply tauJ_fix
  rw [blkSL4_val, rblk4_transpose, blk4_mul, blk4_mul, mul_J2mat_mul_transpose,
    mul_J2mat_mul_transpose, A.det_coe, B.det_coe]
  simp only [one_smul]

theorem slGraph_ne_conj [Finite F] (s : SL(4, F)) :
    CatalogueBGraphForm.slGraphAut 4 F ≠ MulAut.conj s := by
  intro h
  have hn3 : 3 ≤ 4 := by norm_num
  apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F) hn3
  have h1 : dualAut 4 F = conjAut 4 F (Matrix.SpecialLinearGroup.toGL s) := by
    unfold dualAut CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
    rw [h, MonoidHom.comp_apply, slConj_toGL]
  rw [h1]
  exact Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨_, rfl⟩))

theorem tauJ_ne_conj [Finite F] (s : SL(4, F)) : tauJ F ≠ MulAut.conj s := by
  intro h
  apply slGraph_ne_conj (Jsl⁻¹ * s)
  have h3 : CatalogueBGraphForm.slGraphAut 4 F = MulAut.conj ((Jsl : SL(4, F))⁻¹) * tauJ F := by
    unfold tauJ
    rw [map_inv, inv_mul_cancel_left]
  rw [h3, h, ← map_mul]

theorem center_pow_four (z : SL(4, F)) (hz : z ∈ Subgroup.center SL(4, F)) : z ^ 4 = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrz]
  simp only [Fintype.card_fin] at hr
  rw [← map_pow, hr]
  simp

end CFSG.GH74.Generic.S1

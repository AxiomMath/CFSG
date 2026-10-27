module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Struct

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap Matrix
open scoped MatrixGroups


section Scalar

variable {F : Type} [Field F]

theorem scalar_of_commute_uv (N : Matrix (Fin 2) (Fin 2) F)
    (hu : N * ((uSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((uSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) * N)
    (hv : N * ((vSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((vSL (1 : F) : SL2 F) : Matrix (Fin 2) (Fin 2) F) * N) :
    ∃ c : F, N = c • 1 := by
  have e00 := congrFun (congrFun hu 0) 1
  have e01 := congrFun (congrFun hu 1) 1
  have e10 := congrFun (congrFun hu 1) 0
  have f00 := congrFun (congrFun hv 0) 0
  have f01 := congrFun (congrFun hv 0) 1
  have f10 := congrFun (congrFun hv 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_uSL, coe_vSL] at e00 e01 e10 f00 f01 f10
  refine ⟨N 0 0, ?_⟩
  rw [Matrix.eta_fin_two N]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using f00
  · simpa using e01
  · simp
    linear_combination -e00

theorem exists_scalar_of_glConjSL_eq {D E : GL (Fin 2) F}
    (h : ∀ C : SL2 F, glConjSL D C = glConjSL E C) :
    ∃ c : F, c ≠ 0 ∧ (E : Matrix (Fin 2) (Fin 2) F) = c • (D : Matrix (Fin 2) (Fin 2) F) := by
  set Dm : Matrix (Fin 2) (Fin 2) F := (D : Matrix (Fin 2) (Fin 2) F) with hDm
  set Em : Matrix (Fin 2) (Fin 2) F := (E : Matrix (Fin 2) (Fin 2) F) with hEm
  set Di : Matrix (Fin 2) (Fin 2) F := ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hDi
  set Ei : Matrix (Fin 2) (Fin 2) F := ((E⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hEi
  have hDDi : Dm * Di = 1 := gl_mul_inv D
  have hDiD : Di * Dm = 1 := gl_inv_mul D
  have hEEi : Em * Ei = 1 := gl_mul_inv E
  have hEiE : Ei * Em = 1 := gl_inv_mul E
  have hcomm : ∀ C : SL2 F, (Ei * Dm) * (C : Matrix (Fin 2) (Fin 2) F) =
      (C : Matrix (Fin 2) (Fin 2) F) * (Ei * Dm) := by
    intro C
    have h1 : Dm * (C : Matrix (Fin 2) (Fin 2) F) * Di = Em * (C : Matrix (Fin 2) (Fin 2) F) * Ei :=
      congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F)) (h C)
    calc Ei * Dm * (C : Matrix (Fin 2) (Fin 2) F)
        = Ei * (Dm * (C : Matrix (Fin 2) (Fin 2) F) * Di) * Dm := by
          simp only [Matrix.mul_assoc, hDiD, Matrix.mul_one]
      _ = Ei * (Em * (C : Matrix (Fin 2) (Fin 2) F) * Ei) * Dm := by rw [h1]
      _ = (C : Matrix (Fin 2) (Fin 2) F) * (Ei * Dm) := by
          calc Ei * (Em * (C : Matrix (Fin 2) (Fin 2) F) * Ei) * Dm
              = (Ei * Em) * (C : Matrix (Fin 2) (Fin 2) F) * (Ei * Dm) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hEiE, Matrix.one_mul]
  obtain ⟨l, hl⟩ := scalar_of_commute_uv (Ei * Dm) (hcomm (uSL 1)) (hcomm (vSL 1))
  have hDeq : Dm = l • Em := by
    calc Dm = Em * (Ei * Dm) := by rw [← Matrix.mul_assoc, hEEi, Matrix.one_mul]
      _ = l • Em := by rw [hl, Matrix.mul_smul, Matrix.mul_one]
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hDeq
    have : (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by rw [← hDDi, hDeq, Matrix.zero_mul]
    have h01 := congrFun (congrFun this 0) 0
    simp at h01
  refine ⟨l⁻¹, inv_ne_zero hl0, ?_⟩
  rw [hDeq, smul_smul, inv_mul_cancel₀ hl0, one_smul]

end Scalar

section Prelim

variable {F : Type} [Field F]

theorem rootChar_g2vec (b : Fin Tag.G2.rank → Fˣ) (x y : ℤ) :
    rootChar b (g2vec x y) = b g2i0 ^ x * b g2i1 ^ y := by
  rw [rootChar, prod_univ_g2]
  rfl

end Prelim

section ChartConj

variable {F : Type} [Field F] [Finite F]

theorem prod_conj_chartA (hodd : Odd (Nat.card F)) (b : Fin Tag.G2.rank → Fˣ) (A B C : SL2 F) :
    (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) * g2ChartA F C *
      (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B)⁻¹ =
      g2ChartA F (glConjSL (diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A) C) := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have h1 : g2ChartB F B * g2ChartA F C * (g2ChartB F B)⁻¹ = g2ChartA F C := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hcomm C B).symm
  have h2 := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) 1 g2i1 b
    (A * C * A⁻¹)
  rw [one_smul, g2_single_1] at h2
  change rootDiagUnit Tag.G2 b * g2ChartA F (A * C * A⁻¹) * (rootDiagUnit Tag.G2 b)⁻¹ =
    g2ChartA F (glConjSL (diagGL (rootChar b (g2vec 0 1))) (A * C * A⁻¹)) at h2
  rw [rootChar_g2vec] at h2
  simp only [zpow_zero, zpow_one, one_mul] at h2
  rw [glConjSL_mul, glConjSL_toGL, ← h2, map_mul, map_mul, map_inv]
  calc rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B * g2ChartA F C *
        (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B)⁻¹
      = rootDiagUnit Tag.G2 b * g2ChartA F A *
          (g2ChartB F B * g2ChartA F C * (g2ChartB F B)⁻¹) * (g2ChartA F A)⁻¹ *
          (rootDiagUnit Tag.G2 b)⁻¹ := by group
    _ = _ := by rw [h1]; group

end ChartConj

section Tori

variable {F : Type} [Field F]

@[expose] def g2tup (x y : Fˣ) : Fin Tag.G2.rank → Fˣ := ![x, y]

theorem g2tup_0 (x y : Fˣ) : g2tup x y g2i0 = x := rfl

theorem g2tup_1 (x y : Fˣ) : g2tup x y g2i1 = y := rfl

theorem g2tup_ext {b c : Fin Tag.G2.rank → Fˣ} (h0 : b g2i0 = c g2i0) (h1 : b g2i1 = c g2i1) :
    b = c := g2_funext h0 h1

theorem rootDiagUnit_g2tup_mul (x y x' y' : Fˣ) :
    rootDiagUnit Tag.G2 (g2tup x y) * rootDiagUnit Tag.G2 (g2tup x' y') =
      rootDiagUnit Tag.G2 (g2tup (x * x') (y * y')) := by
  rw [← rootDiagUnit_mul]
  congr 1
  exact g2tup_ext rfl rfl

theorem g2ChartA_HSL (u : Fˣ) :
    g2ChartA F (HSL u) = rootDiagUnit Tag.G2 (g2tup ((u⁻¹) ^ 3) (u ^ 2)) := by
  change rootChart Tag.G2 F 1 g2i1 (HSL u) = _
  rw [rootChart_one, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]
  congr 1
  refine g2tup_ext ?_ ?_
  · show u ^ Tag.G2.cartan g2i1 g2i0 = (u⁻¹) ^ 3
    rw [g2_cartan_10]
    group
  · show u ^ Tag.G2.cartan g2i1 g2i1 = u ^ 2
    rw [g2_cartan_11]
    rfl

theorem g2ChartB_HSL (u : Fˣ) :
    g2ChartB F (HSL u) = rootDiagUnit Tag.G2 (g2tup u 1) := by
  change rootChart Tag.G2 F g2WeylU g2i0 (HSL u) = _
  rw [rootChart_apply, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit,
    canonicalRep_conj_rootDiagUnit]
  congr 1
  rw [g2WeylU, ← weylTuple_weylTuple]
  refine g2tup_ext ?_ ?_
  · rw [g2tup_0, weylTuple_simple_g0_zero, weylTuple_simple_g1_zero]
    rw [g2_cartan_00, g2_cartan_01]
    group
  · rw [g2tup_1, weylTuple_simple_g0_one, weylTuple_simple_g1_zero, weylTuple_simple_g1_one]
    rw [g2_cartan_00, g2_cartan_01]
    group

end Tori

section Invol

variable {F : Type} [Field F]

theorem sl2_sq_eq_one_of_two_ne_zero (h2 : (2 : F) ≠ 0) (M : SL2 F) (h : M * M = 1) :
    M = 1 ∨ M = -1 := by
  have hdet := det_SL2 M
  have e00 := congrArg (fun N : SL2 F => (N : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun N : SL2 F => (N : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have e10 := congrArg (fun N : SL2 F => (N : Matrix (Fin 2) (Fin 2) F) 1 0) h
  have e11 := congrArg (fun N : SL2 F => (N : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set p := (M : Matrix (Fin 2) (Fin 2) F) 0 0 with hp
  set q := (M : Matrix (Fin 2) (Fin 2) F) 0 1 with hq
  set r := (M : Matrix (Fin 2) (Fin 2) F) 1 0 with hr
  set s := (M : Matrix (Fin 2) (Fin 2) F) 1 1 with hs
  have hps : p + s ≠ 0 := by
    intro hps
    have hsp : s = -p := by linear_combination hps
    rw [hsp] at hdet e11
    apply h2
    linear_combination -hdet - e00
  have hq0 : q = 0 := by
    have : q * (p + s) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hps
  have hr0 : r = 0 := by
    have : r * (p + s) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hps
  have hpp : p * p = 1 := by rw [hq0] at e00; linear_combination e00
  have hsp : s = p := by
    rw [hq0, hr0] at hdet
    have : (s - p) * p = 0 := by linear_combination hdet - hpp
    have hp0 : p ≠ 0 := fun h0 => by rw [h0] at hpp; simp at hpp
    have := (mul_eq_zero.mp this).resolve_right hp0
    linear_combination this
  have hp1 : p = 1 ∨ p = -1 := by
    have : (p - 1) * (p + 1) = 0 := by linear_combination hpp
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h1)
  have hq0' : (M : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := hq0
  have hr0' : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hr0
  have hsp' : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = (M : Matrix (Fin 2) (Fin 2) F) 0 0 := hsp
  rcases hp1 with h1 | h1
  · have h1' : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := h1
    left
    apply SL2_ext <;> simp [hq0', hr0', hsp', h1']
  · have h1' : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = -1 := h1
    right
    apply SL2_ext <;> simp [hq0', hr0', hsp', h1']

end Invol

section Scalar

variable {F : Type} [Field F] [Finite F]

theorem g2ChartA_neg_one (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) : g2ChartA F (-1) = rootDiagUnit Tag.G2 a := by
  obtain ⟨hasq, hane, hker, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hγ : g2vec 0 1 ∈ rootCharKernel a := by rw [hker]; simp
  exact rootChart_neg_one hodd hasq hane hγ (w := 1) (i := g2i1)
    (by rw [one_smul, g2_single_1])

theorem g2ChartB_neg_one (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) : g2ChartB F (-1) = rootDiagUnit Tag.G2 a := by
  obtain ⟨hasq, hane, hker, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hγ : g2vec 2 3 ∈ rootCharKernel a := by rw [hker]; simp
  exact rootChart_neg_one hodd hasq hane hγ (w := g2WeylU) (i := g2i0) g2WeylU_smul_single

theorem prod_conj_chartB (hodd : Odd (Nat.card F)) (b : Fin Tag.G2.rank → Fˣ) (A B C : SL2 F) :
    (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) * g2ChartB F C *
      (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B)⁻¹ =
      g2ChartB F (glConjSL (diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) *
        Matrix.SpecialLinearGroup.toGL B) C) := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have h1 : g2ChartA F A * g2ChartB F (B * C * B⁻¹) * (g2ChartA F A)⁻¹ =
      g2ChartB F (B * C * B⁻¹) := by
    rw [mul_inv_eq_iff_eq_mul]; exact hcomm A _
  have h2 := rootDiagUnit_conj_rootChart (K := F) (τ := Tag.G2) g2WeylU g2i0 b (B * C * B⁻¹)
  rw [g2WeylU_smul_single] at h2
  change rootDiagUnit Tag.G2 b * g2ChartB F (B * C * B⁻¹) * (rootDiagUnit Tag.G2 b)⁻¹ =
    g2ChartB F (glConjSL (diagGL (rootChar b (g2vec 2 3))) (B * C * B⁻¹)) at h2
  rw [rootChar_g2vec] at h2
  simp only [zpow_ofNat] at h2
  rw [glConjSL_mul, glConjSL_toGL, ← h2, map_mul, map_mul, map_inv]
  calc rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B * g2ChartB F C *
        (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B)⁻¹
      = rootDiagUnit Tag.G2 b *
          (g2ChartA F A * (g2ChartB F B * g2ChartB F C * (g2ChartB F B)⁻¹) *
            (g2ChartA F A)⁻¹) * (rootDiagUnit Tag.G2 b)⁻¹ := by group
    _ = _ := by
        have h1' : g2ChartA F A * (g2ChartB F B * g2ChartB F C * (g2ChartB F B)⁻¹) *
            (g2ChartA F A)⁻¹ = g2ChartB F B * g2ChartB F C * (g2ChartB F B)⁻¹ := by
          have := h1
          simp only [map_mul, map_inv] at this
          exact this
        rw [h1']

theorem eq_one_or_eq_of_scalar_chartA (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) (b : Fin Tag.G2.rank → Fˣ) (A B : SL2 F)
    (hz2 : (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) *
      (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) = 1)
    (hscal : ∃ c : F, ((diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = c • 1) :
    rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = 1 ∨
      rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = rootDiagUnit Tag.G2 a := by
  obtain ⟨c, hc⟩ := hscal
  have hs0 : ((b g2i1 : Fˣ) : F) ≠ 0 := (b g2i1).ne_zero
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 A
  have hdet' : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [e01] at hdet; simpa using hdet
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  set u : Fˣ := Units.mk0 _ hA00 with hu
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((u⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right hdet'
  have hAu : A = HSL u := by
    apply SL2_ext
    · simp [coe_HSL, hu]
    · simp [coe_HSL, e01]
    · simp [coe_HSL, e10]
    · rw [hA11]; simp [coe_HSL]
  have hsu : b g2i1 = u⁻¹ * u⁻¹ := by
    have h1 : b g2i1 * u = u⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, ← hA11, hu, Units.val_mk0, e00, e11]
    exact eq_mul_inv_of_mul_eq h1
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_nat_card hodd)
  set b' : Fin Tag.G2.rank → Fˣ := b * g2tup ((u⁻¹) ^ 3) (u ^ 2) with hb'
  have hb'1 : b' g2i1 = 1 := by
    show b g2i1 * u ^ 2 = 1
    rw [hsu]; group
  have hb'eq : b' = g2tup (b' g2i0) 1 := g2tup_ext rfl hb'1
  have hz : rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B =
      g2ChartB F (HSL (b' g2i0) * B) := by
    rw [hAu, g2ChartA_HSL, map_mul, g2ChartB_HSL, ← rootDiagUnit_mul, ← hb'eq]
  have hM : (HSL (b' g2i0) * B) * (HSL (b' g2i0) * B) = 1 := by
    apply g2ChartB_injective hodd
    rw [map_mul, map_one, ← hz]
    exact hz2
  rcases sl2_sq_eq_one_of_two_ne_zero h2 _ hM with h | h
  · left; rw [hz, h, map_one]
  · right; rw [hz, h, g2ChartB_neg_one hodd ha]

theorem eq_one_or_eq_of_scalar_chartB (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) (b : Fin Tag.G2.rank → Fˣ) (A B : SL2 F)
    (hz2 : (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) *
      (rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B) = 1)
    (hscal : ∃ c : F, ((diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) *
      Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c • 1) :
    rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = 1 ∨
      rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = rootDiagUnit Tag.G2 a := by
  obtain ⟨c, hc⟩ := hscal
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have hs0 : ((b g2i0 ^ 2 * b g2i1 ^ 3 : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 B
  have hdet' : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [e01] at hdet; simpa using hdet
  have hB00 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  set v : Fˣ := Units.mk0 _ hB00 with hv
  have hB11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = ((v⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, hv, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right hdet'
  have hBv : B = HSL v := by
    apply SL2_ext
    · simp [coe_HSL, hv]
    · simp [coe_HSL, e01]
    · simp [coe_HSL, e10]
    · rw [hB11]; simp [coe_HSL]
  have hsv : b g2i0 ^ 2 * b g2i1 ^ 3 = v⁻¹ * v⁻¹ := by
    have h1 : (b g2i0 ^ 2 * b g2i1 ^ 3) * v = v⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, ← hB11, hv, Units.val_mk0]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [e00, e11]
    exact eq_mul_inv_of_mul_eq h1
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_nat_card hodd)
  set b' : Fin Tag.G2.rank → Fˣ := b * g2tup v 1 with hb'
  have hrel : b' g2i0 ^ 2 * b' g2i1 ^ 3 = 1 := by
    show (b g2i0 * v) ^ 2 * (b g2i1 * 1) ^ 3 = 1
    calc (b g2i0 * v) ^ 2 * (b g2i1 * 1) ^ 3 = (b g2i0 ^ 2 * b g2i1 ^ 3) * v ^ 2 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
          ring
      _ = 1 := by rw [hsv]; group
  set w : Fˣ := (b' g2i0 * b' g2i1)⁻¹ with hw
  have hb'eq : b' = g2tup ((w⁻¹) ^ 3) (w ^ 2) := by
    have hrelF : ((b' g2i0 : Fˣ) : F) ^ 2 * ((b' g2i1 : Fˣ) : F) ^ 3 = 1 := by
      have := congrArg Units.val hrel
      simpa using this
    refine g2tup_ext ?_ ?_
    · show b' g2i0 = (w⁻¹) ^ 3
      apply Units.ext
      simp only [hw, inv_inv, Units.val_pow_eq_pow_val, Units.val_mul]
      linear_combination (-((b' g2i0 : Fˣ) : F)) * hrelF
    · show b' g2i1 = w ^ 2
      apply Units.ext
      have h0 : ((b' g2i0 : Fˣ) : F) ≠ 0 := Units.ne_zero _
      have h1 : ((b' g2i1 : Fˣ) : F) ≠ 0 := Units.ne_zero _
      simp only [hw, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hrelF
  have hz : rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B =
      g2ChartA F (HSL w * A) := by
    have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd A (HSL v)
    rw [hBv, mul_assoc, hcomm, ← mul_assoc, g2ChartB_HSL, ← rootDiagUnit_mul, map_mul,
      g2ChartA_HSL, ← hb'eq]
  have hM : (HSL w * A) * (HSL w * A) = 1 := by
    apply g2ChartA_injective hodd
    rw [map_mul, map_one, ← hz]
    exact hz2
  rcases sl2_sq_eq_one_of_two_ne_zero h2 _ hM with h | h
  · left; rw [hz, h, map_one]
  · right; rw [hz, h, g2ChartA_neg_one hodd ha]

end Scalar

section Antidiag

variable {F : Type} [Field F]

theorem exists_HSL_mul_WSL (s : Fˣ) (A : SL2 F) (β γ : F)
    (h : (!![(s : F), 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) =
      !![0, β; γ, 0]) : ∃ u : Fˣ, A = HSL u * WSL := by
  have hs0 : (s : F) ≠ 0 := s.ne_zero
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 A
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := e00
  rw [hA00, e11] at hdet
  have hA01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := fun h0 => by
    rw [h0] at hdet; simp at hdet
  refine ⟨Units.mk0 _ hA01, ?_⟩
  apply SL2_ext
  · simp [coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hA00]
  · simp [coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  · simp [coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    have : (A : Matrix (Fin 2) (Fin 2) F) 0 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0 = -1 := by
      linear_combination -hdet
    field_simp
    linear_combination this
  · simp [coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, e11]

end Antidiag

section ConjX

variable {F : Type} [Field F] [Finite F]

theorem conj_chartA_of_conj (hodd : Odd (Nat.card F)) {z : ModGL Tag.G2 F} {g : GL (Fin 2) F}
    (hz : ∀ C : SL2 F, z * g2ChartA F C * z⁻¹ = g2ChartA F (glConjSL g C)) (R S : SL2 F)
    (C : SL2 F) :
    ((g2ChartA F R * g2ChartB F S) * z * (g2ChartA F R * g2ChartB F S)⁻¹) * g2ChartA F C *
      ((g2ChartA F R * g2ChartB F S) * z * (g2ChartA F R * g2ChartB F S)⁻¹)⁻¹ =
      g2ChartA F (glConjSL (Matrix.SpecialLinearGroup.toGL R * g *
        (Matrix.SpecialLinearGroup.toGL R)⁻¹) C) := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have hxc : ∀ (R' S' C' : SL2 F), (g2ChartA F R' * g2ChartB F S') * g2ChartA F C' *
      (g2ChartA F R' * g2ChartB F S')⁻¹ = g2ChartA F (R' * C' * R'⁻¹) := by
    intro R' S' C'
    have h1 : g2ChartB F S' * g2ChartA F C' * (g2ChartB F S')⁻¹ = g2ChartA F C' := by
      rw [mul_inv_eq_iff_eq_mul]; exact (hcomm C' S').symm
    calc (g2ChartA F R' * g2ChartB F S') * g2ChartA F C' *
          (g2ChartA F R' * g2ChartB F S')⁻¹
        = g2ChartA F R' * (g2ChartB F S' * g2ChartA F C' * (g2ChartB F S')⁻¹) *
            (g2ChartA F R')⁻¹ := by group
      _ = _ := by rw [h1, ← map_inv, ← map_mul, ← map_mul]
  have hinv : (g2ChartA F R * g2ChartB F S)⁻¹ = g2ChartA F R⁻¹ * g2ChartB F S⁻¹ := by
    rw [_root_.mul_inv_rev, ← map_inv (g2ChartA F), ← map_inv (g2ChartB F)]
    exact (hcomm R⁻¹ S⁻¹).symm
  have hxinv : (g2ChartA F R * g2ChartB F S) =
      (g2ChartA F R⁻¹ * g2ChartB F S⁻¹)⁻¹ := by
    rw [← hinv, inv_inv]
  set x := g2ChartA F R * g2ChartB F S with hx
  have hxc' : x⁻¹ * g2ChartA F C * x = g2ChartA F (R⁻¹ * C * R) := by
    have := hxc R⁻¹ S⁻¹ C
    rw [← hxinv, inv_inv] at this
    rw [hinv]
    simpa [hx] using this
  calc x * z * x⁻¹ * g2ChartA F C * (x * z * x⁻¹)⁻¹
      = x * (z * (x⁻¹ * g2ChartA F C * x) * z⁻¹) * x⁻¹ := by group
    _ = _ := by
      rw [hxc', hz, hx, hxc R S, glConjSL_mul, glConjSL_mul, ← map_inv, glConjSL_toGL,
        glConjSL_toGL, inv_inv]

theorem conj_chartB_of_conj (hodd : Odd (Nat.card F)) {z : ModGL Tag.G2 F} {g : GL (Fin 2) F}
    (hz : ∀ C : SL2 F, z * g2ChartB F C * z⁻¹ = g2ChartB F (glConjSL g C)) (R S : SL2 F)
    (C : SL2 F) :
    ((g2ChartA F R * g2ChartB F S) * z * (g2ChartA F R * g2ChartB F S)⁻¹) * g2ChartB F C *
      ((g2ChartA F R * g2ChartB F S) * z * (g2ChartA F R * g2ChartB F S)⁻¹)⁻¹ =
      g2ChartB F (glConjSL (Matrix.SpecialLinearGroup.toGL S * g *
        (Matrix.SpecialLinearGroup.toGL S)⁻¹) C) := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  have hxc : ∀ (R' S' C' : SL2 F), (g2ChartA F R' * g2ChartB F S') * g2ChartB F C' *
      (g2ChartA F R' * g2ChartB F S')⁻¹ = g2ChartB F (S' * C' * S'⁻¹) := by
    intro R' S' C'
    calc (g2ChartA F R' * g2ChartB F S') * g2ChartB F C' * (g2ChartA F R' * g2ChartB F S')⁻¹
        = g2ChartA F R' * (g2ChartB F S' * g2ChartB F C' * (g2ChartB F S')⁻¹) *
            (g2ChartA F R')⁻¹ := by group
      _ = g2ChartA F R' * g2ChartB F (S' * C' * S'⁻¹) * (g2ChartA F R')⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = g2ChartB F (S' * C' * S'⁻¹) := by
          rw [mul_inv_eq_iff_eq_mul]; exact hcomm R' _
  have hinv : (g2ChartA F R * g2ChartB F S)⁻¹ = g2ChartA F R⁻¹ * g2ChartB F S⁻¹ := by
    rw [_root_.mul_inv_rev, ← map_inv (g2ChartA F), ← map_inv (g2ChartB F)]
    exact (hcomm R⁻¹ S⁻¹).symm
  have hxinv : (g2ChartA F R * g2ChartB F S) =
      (g2ChartA F R⁻¹ * g2ChartB F S⁻¹)⁻¹ := by
    rw [← hinv, inv_inv]
  set x := g2ChartA F R * g2ChartB F S with hx
  have hxc' : x⁻¹ * g2ChartB F C * x = g2ChartB F (S⁻¹ * C * S) := by
    have := hxc R⁻¹ S⁻¹ C
    rw [← hxinv, inv_inv] at this
    rw [hinv]
    simpa [hx] using this
  calc x * z * x⁻¹ * g2ChartB F C * (x * z * x⁻¹)⁻¹
      = x * (z * (x⁻¹ * g2ChartB F C * x) * z⁻¹) * x⁻¹ := by group
    _ = _ := by
      rw [hxc', hz, hx, hxc R S, glConjSL_mul, glConjSL_mul, ← map_inv, glConjSL_toGL,
        glConjSL_toGL, inv_inv]

end ConjX

section Class

variable {F : Type} [Field F] [Finite F]

theorem g2ChartA_mem_toralCentralizer (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) (A : SL2 F) : g2ChartA F A ∈ toralCentralizer Tag.G2 F a := by
  obtain ⟨-, -, hker, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hγ : g2vec 0 1 ∈ rootCharKernel a := by rw [hker]; simp
  have := rootPair_le_toralCentralizer (K := F) hγ
  rw [← g2ChartA_range] at this
  exact this ⟨A, rfl⟩

theorem g2ChartB_mem_toralCentralizer (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) (B : SL2 F) : g2ChartB F B ∈ toralCentralizer Tag.G2 F a := by
  obtain ⟨-, -, hker, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hγ : g2vec 2 3 ∈ rootCharKernel a := by rw [hker]; simp
  have := rootPair_le_toralCentralizer (K := F) hγ
  rw [← g2ChartB_range] at this
  exact this ⟨B, rfl⟩

omit [Finite F] in
theorem g2ChartA_HSL_mem_torusGroup (u : Fˣ) : g2ChartA F (HSL u) ∈ torusGroup Tag.G2 F := by
  rw [g2ChartA_HSL]; exact g2_rootDiagUnit_mem_torusGroup _

omit [Finite F] in
theorem g2ChartB_HSL_mem_torusGroup (u : Fˣ) : g2ChartB F (HSL u) ∈ torusGroup Tag.G2 F := by
  rw [g2ChartB_HSL]; exact g2_rootDiagUnit_mem_torusGroup _

end Class

section Main

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem sq_scalar_of_chart {G : Type*} [Group G] {Φ : SL2 F →* G} (hΦ : Function.Injective Φ)
    {z : G} {g : GL (Fin 2) F} (hz2 : z * z = 1)
    (hzg : ∀ C : SL2 F, z * Φ C * z⁻¹ = Φ (glConjSL g C)) :
    ∃ l : F, l ≠ 0 ∧ ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) =
      l • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h : ∀ C : SL2 F, glConjSL (1 : GL (Fin 2) F) C = glConjSL (g * g) C := by
    intro C
    apply hΦ
    have e1 : z * (z * Φ C * z⁻¹) * z⁻¹ = Φ C := by
      calc z * (z * Φ C * z⁻¹) * z⁻¹ = (z * z) * Φ C * (z * z)⁻¹ := by group
        _ = Φ C := by rw [hz2]; group
    rw [hzg, hzg, ← glConjSL_mul] at e1
    rw [glConjSL_one]
    exact e1.symm
  obtain ⟨c, hc0, hc⟩ := exists_scalar_of_glConjSL_eq h
  refine ⟨c, hc0, ?_⟩
  have := hc
  rw [Units.val_mul, Units.val_one] at this
  exact this

theorem exists_conj_to_torus_mul (hodd : Odd (Nat.card F)) {a : Fin Tag.G2.rank → Fˣ}
    (ha : a = ![-1, 1]) {z : ModGL Tag.G2 F} (hzX : z ∈ toralCentralizer Tag.G2 F a)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzd : z ≠ rootDiagUnit Tag.G2 a) :
    ∃ x ∈ toralCentralizer Tag.G2 F a, ∃ t ∈ torusGroup Tag.G2 F,
      x * z * x⁻¹ = t * (g2ChartA F WSL * g2ChartB F WSL) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_nat_card hodd)
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hzX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set z := rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B with hz
  set gA : GL (Fin 2) F := diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A with hgA
  set gB : GL (Fin 2) F := diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) *
    Matrix.SpecialLinearGroup.toGL B with hgB
  have hzA : ∀ C : SL2 F, z * g2ChartA F C * z⁻¹ = g2ChartA F (glConjSL gA C) :=
    fun C => prod_conj_chartA hodd b A B C
  have hzB : ∀ C : SL2 F, z * g2ChartB F C * z⁻¹ = g2ChartB F (glConjSL gB C) :=
    fun C => prod_conj_chartB hodd b A B C
  obtain ⟨lA, hlA0, hlA⟩ := sq_scalar_of_chart (g2ChartA_injective hodd) hz2 hzA
  obtain ⟨lB, hlB0, hlB⟩ := sq_scalar_of_chart (g2ChartB_injective hodd) hz2 hzB
  by_cases hsA : ∃ c : F, (gA : Matrix (Fin 2) (Fin 2) F) = c • 1
  · exfalso
    exact (eq_one_or_eq_of_scalar_chartA hodd ha b A B hz2 hsA).elim hz1 hzd
  by_cases hsB : ∃ c : F, (gB : Matrix (Fin 2) (Fin 2) F) = c • 1
  · exfalso
    exact (eq_one_or_eq_of_scalar_chartB hodd ha b A B hz2 hsB).elim hz1 hzd
  obtain ⟨RA, bA, cA, hbA, hcA, hRA⟩ := exists_antidiag_conj h2 (gA : Matrix (Fin 2) (Fin 2) F)
    hlA hlA0 (fun c hc => hsA ⟨c, hc⟩)
  obtain ⟨RB, bB, cB, hbB, hcB, hRB⟩ := exists_antidiag_conj h2 (gB : Matrix (Fin 2) (Fin 2) F)
    hlB hlB0 (fun c hc => hsB ⟨c, hc⟩)
  set x : ModGL Tag.G2 F := g2ChartA F RA * g2ChartB F RB with hx
  have hxX : x ∈ toralCentralizer Tag.G2 F a :=
    mul_mem (g2ChartA_mem_toralCentralizer hodd ha RA) (g2ChartB_mem_toralCentralizer hodd ha RB)
  refine ⟨x, hxX, ?_⟩
  have hz''X : x * z * x⁻¹ ∈ toralCentralizer Tag.G2 F a :=
    mul_mem (mul_mem hxX hzX) (inv_mem hxX)
  obtain ⟨t'', ht'', A'', B'', hz''⟩ := toralCentralizer_le_prod hodd ha hz''X
  obtain ⟨b'', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht''
  have hDA : ((Matrix.SpecialLinearGroup.toGL RA * gA * (Matrix.SpecialLinearGroup.toGL RA)⁻¹ :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, bA; cA, 0] := by
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hRA
  have hDB : ((Matrix.SpecialLinearGroup.toGL RB * gB * (Matrix.SpecialLinearGroup.toGL RB)⁻¹ :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, bB; cB, 0] := by
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact hRB
  have hA1 := conj_chartA_of_conj hodd hzA RA RB
  have hA2 : ∀ C : SL2 F, (x * z * x⁻¹) * g2ChartA F C * (x * z * x⁻¹)⁻¹ =
      g2ChartA F (glConjSL (diagGL (b'' g2i1) * Matrix.SpecialLinearGroup.toGL A'') C) := by
    intro C
    rw [hz'']
    exact prod_conj_chartA hodd b'' A'' B'' C
  have hB1 := conj_chartB_of_conj hodd hzB RA RB
  have hB2 : ∀ C : SL2 F, (x * z * x⁻¹) * g2ChartB F C * (x * z * x⁻¹)⁻¹ =
      g2ChartB F (glConjSL (diagGL (b'' g2i0 ^ 2 * b'' g2i1 ^ 3) *
        Matrix.SpecialLinearGroup.toGL B'') C) := by
    intro C
    rw [hz'']
    exact prod_conj_chartB hodd b'' A'' B'' C
  obtain ⟨cA', -, hcA'⟩ := exists_scalar_of_glConjSL_eq
    (D := Matrix.SpecialLinearGroup.toGL RA * gA * (Matrix.SpecialLinearGroup.toGL RA)⁻¹)
    (E := diagGL (b'' g2i1) * Matrix.SpecialLinearGroup.toGL A'')
    (fun C => g2ChartA_injective hodd ((hA1 C).symm.trans (hA2 C)))
  obtain ⟨cB', -, hcB'⟩ := exists_scalar_of_glConjSL_eq
    (D := Matrix.SpecialLinearGroup.toGL RB * gB * (Matrix.SpecialLinearGroup.toGL RB)⁻¹)
    (E := diagGL (b'' g2i0 ^ 2 * b'' g2i1 ^ 3) * Matrix.SpecialLinearGroup.toGL B'')
    (fun C => g2ChartB_injective hodd ((hB1 C).symm.trans (hB2 C)))
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hDA] at hcA'
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hDB] at hcB'
  obtain ⟨u, hu⟩ := exists_HSL_mul_WSL (b'' g2i1) A'' (cA' * bA) (cA' * cA) (by
    rw [hcA']; ext i j; fin_cases i <;> fin_cases j <;> simp)
  obtain ⟨v, hv⟩ := exists_HSL_mul_WSL (b'' g2i0 ^ 2 * b'' g2i1 ^ 3) B'' (cB' * bB) (cB' * cB) (by
    rw [hcB']; ext i j; fin_cases i <;> fin_cases j <;> simp)
  refine ⟨rootDiagUnit Tag.G2 b'' * g2ChartA F (HSL u) * g2ChartB F (HSL v),
    mul_mem (mul_mem (g2_rootDiagUnit_mem_torusGroup _) (g2ChartA_HSL_mem_torusGroup u))
      (g2ChartB_HSL_mem_torusGroup v), ?_⟩
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd WSL (HSL v)
  rw [hz'', hu, hv, map_mul, map_mul]
  calc rootDiagUnit Tag.G2 b'' * (g2ChartA F (HSL u) * g2ChartA F WSL) *
        (g2ChartB F (HSL v) * g2ChartB F WSL)
      = rootDiagUnit Tag.G2 b'' * g2ChartA F (HSL u) *
          (g2ChartA F WSL * g2ChartB F (HSL v)) * g2ChartB F WSL := by group
    _ = rootDiagUnit Tag.G2 b'' * g2ChartA F (HSL u) *
          (g2ChartB F (HSL v) * g2ChartA F WSL) * g2ChartB F WSL := by rw [hcomm]
    _ = _ := by group

end Main


section Invert

variable {F : Type} [Field F]

theorem g2OmegaBeta_inv : g2OmegaBeta⁻¹ = g2OmegaBeta := by
  rw [g2OmegaBeta, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, simple_inv_eq', mul_assoc]

theorem g2_w0_inv_smul (v : Fin Tag.G2.rank → ℤ) :
    (simple Tag.G2 g2i1 * g2OmegaBeta)⁻¹ • v = -v := by
  rw [_root_.mul_inv_rev, g2OmegaBeta_inv, simple_inv_eq', mul_smul, g2_s1_smul,
    g2OmegaBeta_smul]
  refine g2vec_ext ?_ ?_
  · simp [g2vec_0]
  · simp [g2vec_1, g2vec_0]
    ring

theorem g2_m0_inverts {t : ModGL Tag.G2 F} (ht : t ∈ torusGroup Tag.G2 F) :
    (g2ChartA F WSL * g2ChartB F WSL) * t * (g2ChartA F WSL * g2ChartB F WSL)⁻¹ = t⁻¹ := by
  have hmA : MapsRootLines (g2ChartA F WSL) (simple Tag.G2 g2i1) := by
    have := rootChart_WSL_mapsRootLines (K := F) (1 : WeylGroup Tag.G2) g2i1
    simpa using this
  have hmB : MapsRootLines (g2ChartB F WSL) g2OmegaBeta :=
    rootChart_WSL_mapsRootLines (K := F) g2WeylU g2i0
  have hcA : g2ChartA F WSL ∈ torusWeylCosets Tag.G2 F :=
    rootChart_WSL_mem_torusWeylCosets (K := F) 1 g2i1
  have hcB : g2ChartB F WSL ∈ torusWeylCosets Tag.G2 F :=
    rootChart_WSL_mem_torusWeylCosets (K := F) g2WeylU g2i0
  obtain ⟨k, hk, hkm⟩ := exists_torus_mul_canonicalRep
    ((torusWeylCosets Tag.G2 F).mul_mem hcA hcB) (hmA.mul hmB)
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨b₂, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hwt : weylTuple (simple Tag.G2 g2i1 * g2OmegaBeta) b = b⁻¹ := by
    funext i
    simp only [weylTuple, g2_w0_inv_smul, Pi.inv_apply]
    rw [rootChar_neg_inv, rootChar_single_g2]
  calc (g2ChartA F WSL * g2ChartB F WSL) * rootDiagUnit Tag.G2 b *
        (g2ChartA F WSL * g2ChartB F WSL)⁻¹
      = rootDiagUnit Tag.G2 b₂ * (canonicalRep (coxeterSystem Tag.G2) F
          (simple Tag.G2 g2i1 * g2OmegaBeta) * rootDiagUnit Tag.G2 b *
          (canonicalRep (coxeterSystem Tag.G2) F (simple Tag.G2 g2i1 * g2OmegaBeta))⁻¹) *
          (rootDiagUnit Tag.G2 b₂)⁻¹ := by rw [hkm]; group
    _ = rootDiagUnit Tag.G2 b₂ * rootDiagUnit Tag.G2 b⁻¹ * (rootDiagUnit Tag.G2 b₂)⁻¹ := by
        rw [canonicalRep_conj_rootDiagUnit, hwt]
    _ = (rootDiagUnit Tag.G2 b)⁻¹ := by
        rw [rootDiagUnit_inv, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
        congr 1
        funext i
        simp only [Pi.mul_apply, Pi.inv_apply]
        rw [mul_comm (b₂ i), mul_assoc, mul_inv_cancel, mul_one]

end Invert


end CFSG.ClassicalInvolution.G2D4Models

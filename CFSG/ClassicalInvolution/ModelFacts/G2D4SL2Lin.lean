module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ClassicalInvolution.SL2Facts

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups commutatorElement

section Conj

variable {F : Type} [Field F]

theorem gl_mul_inv (D : GL (Fin 2) F) :
    (D : Matrix (Fin 2) (Fin 2) F) * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem gl_inv_mul (D : GL (Fin 2) F) :
    ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

@[expose] def glConjSL (D : GL (Fin 2) F) : SL2 F →* SL2 F where
  toFun A := ⟨(D : Matrix (Fin 2) (Fin 2) F) * A *
    ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
      rw [det_mul, det_mul, A.2, mul_one]
      have := congrArg det (gl_mul_inv D)
      rwa [det_mul, det_one] at this⟩
  map_one' := by
    apply Subtype.ext
    show (D : Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F) *
      ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [mul_one, gl_mul_inv]
  map_mul' A B := by
    apply Subtype.ext
    show (D : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * B) *
      ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((D : Matrix (Fin 2) (Fin 2) F) * A * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        ((D : Matrix (Fin 2) (Fin 2) F) * B * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    have h := gl_inv_mul D
    calc (D : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * B) *
          ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (D : Matrix (Fin 2) (Fin 2) F) * A * (1 : Matrix (Fin 2) (Fin 2) F) * B *
          ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          simp only [mul_one, Matrix.mul_assoc]
      _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]

theorem glConjSL_coe (D : GL (Fin 2) F) (A : SL2 F) :
    ((glConjSL D A : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      (D : Matrix (Fin 2) (Fin 2) F) * A * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem glConjSL_mul (D E : GL (Fin 2) F) (A : SL2 F) :
    glConjSL (D * E) A = glConjSL D (glConjSL E A) := by
  apply Subtype.ext
  simp only [glConjSL_coe, Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem glConjSL_one (A : SL2 F) : glConjSL 1 A = A := by
  apply Subtype.ext
  simp [glConjSL_coe]

theorem glConjSL_toGL (B A : SL2 F) :
    glConjSL (Matrix.SpecialLinearGroup.toGL B) A = B * A * B⁻¹ := by
  apply Subtype.ext
  rw [glConjSL_coe, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

@[expose] def diagGL (s : Fˣ) : GL (Fin 2) F :=
  ⟨!![(s : F), 0; 0, 1], !![((s⁻¹ : Fˣ) : F), 0; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[expose] def antiGL (κ : Fˣ) : GL (Fin 2) F :=
  ⟨!![0, 1; (κ : F), 0], !![0, ((κ⁻¹ : Fˣ) : F); 1, 0], by
    ext i j; fin_cases i <;> fin_cases j <;> simp, by
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem glConjSL_diag_uSL (s : Fˣ) (c : F) :
    glConjSL (diagGL s) (uSL c) = uSL ((s : F) * c) := by
  apply SL2_ext <;> simp [glConjSL_coe, diagGL, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem glConjSL_diag_vSL (s : Fˣ) (c : F) :
    glConjSL (diagGL s) (vSL c) = vSL (((s⁻¹ : Fˣ) : F) * c) := by
  apply SL2_ext <;> simp [glConjSL_coe, diagGL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem glConjSL_anti_uSL (κ : Fˣ) (c : F) :
    glConjSL (antiGL κ) (uSL c) = vSL ((κ : F) * c) := by
  apply SL2_ext <;> simp [glConjSL_coe, antiGL, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two]

theorem glConjSL_anti_vSL (κ : Fˣ) (c : F) :
    glConjSL (antiGL κ) (vSL c) = uSL (((κ⁻¹ : Fˣ) : F) * c) := by
  apply SL2_ext <;> simp [glConjSL_coe, antiGL, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

end Conj

section LinAct

variable {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def LinAct (Φ : SL2 F →* G) (x : G) : Prop :=
  ∃ D : GL (Fin 2) F, ∀ A : SL2 F, x * Φ A * x⁻¹ = Φ (glConjSL D A)

@[expose] def linActSubgroup (Φ : SL2 F →* G) : Subgroup G where
  carrier := {x | LinAct Φ x}
  one_mem' := ⟨1, fun A => by simp [glConjSL_one]⟩
  mul_mem' := by
    rintro x y ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D * E, fun A => ?_⟩
    rw [glConjSL_mul]
    calc x * y * Φ A * (x * y)⁻¹ = x * (y * Φ A * y⁻¹) * x⁻¹ := by group
      _ = x * Φ (glConjSL E A) * x⁻¹ := by rw [hE]
      _ = Φ (glConjSL D (glConjSL E A)) := hD _
  inv_mem' := by
    rintro x ⟨D, hD⟩
    refine ⟨D⁻¹, fun A => ?_⟩
    have h := hD (glConjSL D⁻¹ A)
    rw [← glConjSL_mul, mul_inv_cancel, glConjSL_one] at h
    rw [inv_inv]
    calc x⁻¹ * Φ A * x = x⁻¹ * (x * Φ (glConjSL D⁻¹ A) * x⁻¹) * x := by rw [h]
      _ = Φ (glConjSL D⁻¹ A) := by group

theorem mem_linActSubgroup {Φ : SL2 F →* G} {x : G} : x ∈ linActSubgroup Φ ↔ LinAct Φ x :=
  Iff.rfl

theorem linAct_of_mem_range {Φ : SL2 F →* G} {x : G} (hx : x ∈ Φ.range) : LinAct Φ x := by
  obtain ⟨B, rfl⟩ := hx
  exact ⟨Matrix.SpecialLinearGroup.toGL B, fun A => by
    rw [glConjSL_toGL, map_mul, map_mul, map_inv]⟩

theorem linAct_of_commutes {Φ : SL2 F →* G} {x : G} (h : ∀ A, x * Φ A = Φ A * x) :
    LinAct Φ x :=
  ⟨1, fun A => by rw [glConjSL_one, mul_inv_eq_iff_eq_mul]; exact h A⟩

theorem conj_eq_of_generators {Φ : SL2 F →* G} {x : G} (σ : SL2 F →* SL2 F)
    (hu : ∀ c, x * Φ (uSL c) * x⁻¹ = Φ (σ (uSL c)))
    (hv : ∀ c, x * Φ (vSL c) * x⁻¹ = Φ (σ (vSL c))) :
    ∀ A, x * Φ A * x⁻¹ = Φ (σ A) := by
  have key := MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F))
    (f := (MulAut.conj x).toMonoidHom.comp Φ) (g := Φ.comp σ) (by
      rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hu c
      · exact hv c)
  intro A
  exact DFunLike.congr_fun key A

theorem linAct_diag {Φ : SL2 F →* G} {x : G} (s : Fˣ)
    (hu : ∀ c, x * Φ (uSL c) * x⁻¹ = Φ (uSL ((s : F) * c)))
    (hv : ∀ c, x * Φ (vSL c) * x⁻¹ = Φ (vSL (((s⁻¹ : Fˣ) : F) * c))) : LinAct Φ x :=
  ⟨diagGL s, conj_eq_of_generators (glConjSL (diagGL s))
    (fun c => by rw [hu, glConjSL_diag_uSL]) (fun c => by rw [hv, glConjSL_diag_vSL])⟩

theorem linAct_anti {Φ : SL2 F →* G} {x : G} (κ : Fˣ)
    (hu : ∀ c, x * Φ (uSL c) * x⁻¹ = Φ (vSL ((κ : F) * c)))
    (hv : ∀ c, x * Φ (vSL c) * x⁻¹ = Φ (uSL (((κ⁻¹ : Fˣ) : F) * c))) : LinAct Φ x :=
  ⟨antiGL κ, conj_eq_of_generators (glConjSL (antiGL κ))
    (fun c => by rw [hu, glConjSL_anti_uSL]) (fun c => by rw [hv, glConjSL_anti_vSL])⟩

end LinAct

section Consistency

variable {F : Type} [Field F]

theorem weyl_sq : ((uSL 1 : SL2 F) * vSL (-1) * uSL 1) * (uSL 1 * vSL (-1) * uSL 1) = -1 := by
  apply SL2_ext <;> simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_eq_one_of_weyl_sq_diag {s s' : F} (h2 : (2 : F) ≠ 0)
    (h : ((uSL s : SL2 F) * vSL (-s') * uSL s) * (uSL s * vSL (-s') * uSL s) = -1) :
    s * s' = 1 := by
  have e00 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at e00
  have h3 : 2 * (s * s' - 1) ^ 2 = 0 := by linear_combination e00
  have h4 : (s * s' - 1) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h2
    · exact h
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h4
  linear_combination this

theorem mul_eq_one_of_weyl_sq_anti {κ κ' : F} (h2 : (2 : F) ≠ 0)
    (h : ((vSL κ : SL2 F) * uSL (-κ') * vSL κ) * (vSL κ * uSL (-κ') * vSL κ) = -1) :
    κ * κ' = 1 := by
  have e00 := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at e00
  have h3 : 2 * (κ * κ' - 1) ^ 2 = 0 := by linear_combination e00
  have h4 : (κ * κ' - 1) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h2
    · exact h
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h4
  linear_combination this

variable {G : Type*} [Group G]

theorem linAct_of_signs_diag {Φ : SL2 F →* G} (hΦ : Function.Injective Φ) (h2 : (2 : F) ≠ 0)
    {x : G} (hneg : x * Φ (-1) * x⁻¹ = Φ (-1)) {s s' : F}
    (hu : ∀ c, x * Φ (uSL c) * x⁻¹ = Φ (uSL (s * c)))
    (hv : ∀ c, x * Φ (vSL c) * x⁻¹ = Φ (vSL (s' * c))) : LinAct Φ x := by
  have hN : x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹ = Φ (uSL s * vSL (-s') * uSL s) := by
    calc x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹
        = (x * Φ (uSL 1) * x⁻¹) * (x * Φ (vSL (-1)) * x⁻¹) * (x * Φ (uSL 1) * x⁻¹) := by
          simp only [map_mul]; group
      _ = Φ (uSL (s * 1)) * Φ (vSL (s' * -1)) * Φ (uSL (s * 1)) := by rw [hu 1, hv (-1)]
      _ = Φ (uSL s * vSL (-s') * uSL s) := by
          rw [← map_mul, ← map_mul, mul_one, mul_neg_one]
  have hsq : Φ ((uSL s * vSL (-s') * uSL s) * (uSL s * vSL (-s') * uSL s)) = Φ (-1) := by
    have h1 : (x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹) * (x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹) =
        x * Φ ((uSL 1 * vSL (-1) * uSL 1) * (uSL 1 * vSL (-1) * uSL 1)) * x⁻¹ := by
      simp only [map_mul]; group
    rw [hN, ← map_mul, weyl_sq, hneg] at h1
    exact h1
  have hss : s * s' = 1 := mul_eq_one_of_weyl_sq_diag h2 (hΦ hsq)
  let U : Fˣ := ⟨s, s', hss, by rw [mul_comm]; exact hss⟩
  exact linAct_diag U hu hv

theorem linAct_of_signs_anti {Φ : SL2 F →* G} (hΦ : Function.Injective Φ) (h2 : (2 : F) ≠ 0)
    {x : G} (hneg : x * Φ (-1) * x⁻¹ = Φ (-1)) {κ κ' : F}
    (hu : ∀ c, x * Φ (uSL c) * x⁻¹ = Φ (vSL (κ * c)))
    (hv : ∀ c, x * Φ (vSL c) * x⁻¹ = Φ (uSL (κ' * c))) : LinAct Φ x := by
  have hN : x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹ = Φ (vSL κ * uSL (-κ') * vSL κ) := by
    calc x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹
        = (x * Φ (uSL 1) * x⁻¹) * (x * Φ (vSL (-1)) * x⁻¹) * (x * Φ (uSL 1) * x⁻¹) := by
          simp only [map_mul]; group
      _ = Φ (vSL (κ * 1)) * Φ (uSL (κ' * -1)) * Φ (vSL (κ * 1)) := by rw [hu 1, hv (-1)]
      _ = Φ (vSL κ * uSL (-κ') * vSL κ) := by
          rw [← map_mul, ← map_mul, mul_one, mul_neg_one]
  have hsq : Φ ((vSL κ * uSL (-κ') * vSL κ) * (vSL κ * uSL (-κ') * vSL κ)) = Φ (-1) := by
    have h1 : (x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹) * (x * Φ (uSL 1 * vSL (-1) * uSL 1) * x⁻¹) =
        x * Φ ((uSL 1 * vSL (-1) * uSL 1) * (uSL 1 * vSL (-1) * uSL 1)) * x⁻¹ := by
      simp only [map_mul]; group
    rw [hN, ← map_mul, weyl_sq, hneg] at h1
    exact h1
  have hκ : κ * κ' = 1 := mul_eq_one_of_weyl_sq_anti h2 (hΦ hsq)
  let U : Fˣ := ⟨κ, κ', hκ, by rw [mul_comm]; exact hκ⟩
  exact linAct_anti U hu hv

end Consistency

section Quaternion

variable {F : Type} [Field F]

theorem exists_sq_add_sq_eq_neg_one [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial F))
    (g := (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F)) (by simp)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; simp) hcard
  refine ⟨a, b, ?_⟩
  simp at h
  linear_combination h

@[expose] def quatI : SL2 F := ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

@[expose] def quatJ {a b : F} (h : a ^ 2 + b ^ 2 = -1) : SL2 F :=
  ⟨!![a, b; b, -a], by simp [det_fin_two]; linear_combination -h⟩

theorem quatI_mul_self : (quatI : SL2 F) * quatI = -1 := by
  refine Subtype.ext ?_
  show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem quatJ_mul_self {a b : F} (h : a ^ 2 + b ^ 2 = -1) : quatJ h * quatJ h = -1 := by
  refine Subtype.ext ?_
  show (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h | linear_combination (-1 : F) * h | ring1

theorem quatI_mul_quatJ {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    quatI * quatJ h = -1 * (quatJ h * quatI) := by
  refine Subtype.ext ?_
  show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![a, b; b, -a] =
    -1 * (!![a, b; b, -a] * !![0, -1; 1, 0])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_of_commute_quat {a b : F} (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hI : M * ((quatI : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((quatI : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M)
    (hJ : M * ((quatJ h : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      ((quatJ h : SL2 F) : Matrix (Fin 2) (Fin 2) F) * M) : ∃ μ : F, M = μ • 1 := by
  obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w : F, M = !![x, y; z, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two M⟩
  have i00 := congrFun (congrFun hI 0) 0
  have i01 := congrFun (congrFun hI 0) 1
  have j00 := congrFun (congrFun hJ 0) 0
  have j01 := congrFun (congrFun hJ 0) 1
  simp [quatI, quatJ, Matrix.mul_apply, Fin.sum_univ_two] at i00 i01 j00 j01
  have hzy : z = -y := by linear_combination i00
  have hwx : w = x := by linear_combination -i01
  subst hzy hwx
  have hy : y = 0 := by
    by_contra hy0
    have ha : a = 0 := by
      have : 2 * y * a = 0 := by linear_combination -j01
      rcases mul_eq_zero.mp this with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2
        · exact absurd h'' hy0
      · exact h'
    have hb : b = 0 := by
      have : 2 * y * b = 0 := by linear_combination j00
      rcases mul_eq_zero.mp this with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2
        · exact absurd h'' hy0
      · exact h'
    rw [ha, hb] at h
    norm_num at h
  subst hy
  exact ⟨w, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

end Quaternion

section Fix

variable {F : Type} [Field F]

theorem commute_conj_aux {R : Type*} [Monoid R] {ρ ρ' D i : R} (h1 : ρ' * ρ = 1)
    (h : D * (ρ * i * ρ') = (ρ * i * ρ') * D) : (ρ' * D * ρ) * i = i * (ρ' * D * ρ) := by
  have e : ρ * i * ρ' * ρ = ρ * i := by rw [mul_assoc (ρ * i), h1, mul_one]
  calc ρ' * D * ρ * i = ρ' * D * (ρ * i) := by simp only [mul_assoc]
    _ = ρ' * D * (ρ * i * ρ' * ρ) := by rw [e]
    _ = ρ' * (D * (ρ * i * ρ')) * ρ := by simp only [mul_assoc]
    _ = ρ' * ((ρ * i * ρ') * D) * ρ := by rw [h]
    _ = (ρ' * ρ) * i * (ρ' * D * ρ) := by simp only [mul_assoc]
    _ = i * (ρ' * D * ρ) := by rw [h1, one_mul]

theorem glConjSL_eq_of_fix_quaternion {a b : F} (h : a ^ 2 + b ^ 2 = -1) (h2 : (2 : F) ≠ 0)
    (ρ : SL2 F) {D : GL (Fin 2) F}
    (hI : glConjSL D (ρ * quatI * ρ⁻¹) = ρ * quatI * ρ⁻¹)
    (hJ : glConjSL D (ρ * quatJ h * ρ⁻¹) = ρ * quatJ h * ρ⁻¹) : ∀ A, glConjSL D A = A := by
  have hDD : (D : Matrix (Fin 2) (Fin 2) F) * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    1 := gl_mul_inv D
  have hDD' : ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (D : Matrix (Fin 2) (Fin 2) F) =
    1 := gl_inv_mul D
  have hρ : ((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * (ρ : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have hρ' : (ρ : Matrix (Fin 2) (Fin 2) F) * ((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have key : ∀ X : SL2 F, glConjSL D X = X →
      (D : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) =
        (X : Matrix (Fin 2) (Fin 2) F) * D := by
    intro X hX
    have := congrArg Subtype.val hX
    rw [glConjSL_coe] at this
    calc (D : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F)
        = (D : Matrix (Fin 2) (Fin 2) F) * X *
          (((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * D) := by rw [hDD', Matrix.mul_one]
      _ = ((D : Matrix (Fin 2) (Fin 2) F) * X * ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          * D := by simp only [Matrix.mul_assoc]
      _ = (X : Matrix (Fin 2) (Fin 2) F) * D := by rw [this]
  have hIm := commute_conj_aux hρ (by
    have := key _ hI
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this)
  have hJm := commute_conj_aux hρ (by
    have := key _ hJ
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this)
  obtain ⟨μ, hμ⟩ := scalar_of_commute_quat h h2 hIm hJm
  have hD : (D : Matrix (Fin 2) (Fin 2) F) = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    calc (D : Matrix (Fin 2) (Fin 2) F)
        = ((ρ : Matrix (Fin 2) (Fin 2) F) * ((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)) * D *
          ((ρ : Matrix (Fin 2) (Fin 2) F) * ((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F)) := by
          rw [hρ', Matrix.one_mul, Matrix.mul_one]
      _ = (ρ : Matrix (Fin 2) (Fin 2) F) * (((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) * D *
          (ρ : Matrix (Fin 2) (Fin 2) F)) * ((ρ⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) := by
          simp only [Matrix.mul_assoc]
      _ = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
          rw [hμ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hρ']
  intro A
  apply Subtype.ext
  rw [glConjSL_coe, hD]
  have hμinv : μ • ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := hDD
    rwa [hD, Matrix.smul_mul, Matrix.one_mul] at this
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hμinv, Matrix.mul_one]

end Fix

section Normal

variable {F : Type} [Field F]

theorem sl2_normal_le_center_or_eq_top [Finite F] (h4 : 4 ≤ Nat.card F) {N : Subgroup (SL2 F)}
    (hN : N.Normal) : N ≤ Subgroup.center (SL2 F) ∨ N = ⊤ := by
  have hs4 : ∃ s : Finset F, s.card = 4 := CFSG.LinearGroups.exists_finset_card_eq_four h4
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr hs4)
  let mk : SL2 F →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.mk' (Subgroup.center (SL2 F))
  have hmk : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have : (N.map mk).Normal := hN.map mk hmk
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map mk) with hbot | htop
  · left
    rw [Subgroup.map_eq_bot_iff] at hbot
    simpa [mk, QuotientGroup.ker_mk'] using hbot
  · right
    have hdecomp : ∀ q : SL2 F, ∃ n ∈ N, ∃ z ∈ Subgroup.center (SL2 F), q = n * z := by
      intro q
      have hq : mk q ∈ N.map mk := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := hq
      refine ⟨n, hn, n⁻¹ * q, ?_, by group⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center (SL2 F)), MonoidHom.mem_ker, map_mul, map_inv]
      change (mk n)⁻¹ * mk q = 1
      rw [hnq, inv_mul_cancel]
    have hperf : ⁅(⊤ : Subgroup (SL2 F)), ⊤⁆ = ⊤ :=
      (CFSG.ClassicalInvolution.sl2_isPerfect h4).commutator_eq_top
    refine eq_top_iff.mpr ?_
    rw [← hperf]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdecomp x
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdecomp y
    have hc₁ := Subgroup.mem_center_iff.mp hz₁
    have hc₂ := Subgroup.mem_center_iff.mp hz₂
    have : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
          = n₁ * (z₁ * n₂ * z₂ * z₁⁻¹) * n₁⁻¹ * (z₂⁻¹ * n₂⁻¹) := by group
        _ = n₁ * (n₂ * z₂) * n₁⁻¹ * (z₂⁻¹ * n₂⁻¹) := by
            rw [show z₁ * n₂ * z₂ * z₁⁻¹ = n₂ * z₂ by
              rw [← hc₁ n₂, mul_assoc, mul_assoc, ← mul_assoc z₁ z₂, ← hc₁ z₂, mul_assoc z₂ z₁,
                mul_inv_cancel, mul_one]]
        _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
            rw [show n₁ * (n₂ * z₂) * n₁⁻¹ * (z₂⁻¹ * n₂⁻¹) = n₁ * n₂ * (z₂ * n₁⁻¹ * z₂⁻¹) * n₂⁻¹ by
              group]
            rw [show z₂ * n₁⁻¹ * z₂⁻¹ = n₁⁻¹ by
              rw [← hc₂ n₁⁻¹, mul_assoc, mul_inv_cancel, mul_one]]
    rw [this]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

end Normal

end CFSG.ClassicalInvolution.G2D4Models

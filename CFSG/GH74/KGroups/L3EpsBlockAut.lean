module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

section Perfect

theorem perfect_commute_of_central_commutator {G H : Type*} [Group G] [Group H]
    (hH : Group.IsPerfect H) (f : H →* G) (a : G)
    (h : ∀ x : H, a * f x * a⁻¹ * (f x)⁻¹ ∈ Subgroup.center G) (x : H) : a * f x = f x * a := by
  let ρ : H →* Subgroup.center G :=
    { toFun := fun x => ⟨a * f x * a⁻¹ * (f x)⁻¹, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := Subgroup.mem_center_iff.1 (h y)
        have hconj : a * f (x * y) * a⁻¹ = (a * f x * a⁻¹) * (a * f y * a⁻¹) := by
          rw [map_mul]; group
        show a * f (x * y) * a⁻¹ * (f (x * y))⁻¹ =
          (a * f x * a⁻¹ * (f x)⁻¹) * (a * f y * a⁻¹ * (f y)⁻¹)
        rw [hconj, map_mul]
        calc a * f x * a⁻¹ * (a * f y * a⁻¹) * (f x * f y)⁻¹
            = (a * f x * a⁻¹ * (f x)⁻¹) * (f x * (a * f y * a⁻¹ * (f y)⁻¹) * (f x)⁻¹) := by group
          _ = (a * f x * a⁻¹ * (f x)⁻¹) * (a * f y * a⁻¹ * (f y)⁻¹) := by
            rw [hy (f x)]; group }
  have hker : commutator H ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hc : ρ x * ρ y = ρ y * ρ x :=
      Subtype.ext (Subgroup.mem_center_iff.1 (ρ y).2 (ρ x))
    exact commutatorElement_eq_one_iff_mul_comm.2 hc
  rw [Group.isPerfect_def.mp hH] at hker
  have h1 : ρ x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have h2 : a * f x * a⁻¹ * (f x)⁻¹ = 1 := congrArg Subtype.val h1
  calc a * f x = (a * f x * a⁻¹ * (f x)⁻¹) * (f x * a) := by group
    _ = f x * a := by rw [h2, one_mul]

end Perfect

section Form

@[expose] def tr1 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def tr2 : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def jSL : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem coe_tr1 : ((tr1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
theorem coe_tr2 : ((tr2 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
theorem coe_jSL : ((jSL : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem form_of_commute_bM {A : Matrix (Fin 3) (Fin 3) F}
    (h₁ : A * bM (tr1 : SL(2, F)).1 = bM (tr1 : SL(2, F)).1 * A)
    (h₂ : A * bM (tr2 : SL(2, F)).1 = bM (tr2 : SL(2, F)).1 * A) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = A 1 1 := by
  have a00 := congrFun (congrFun h₁ 0) 0
  have a01 := congrFun (congrFun h₁ 0) 1
  have a02 := congrFun (congrFun h₁ 0) 2
  have a20 := congrFun (congrFun h₁ 2) 0
  have a21 := congrFun (congrFun h₁ 2) 1
  have b00 := congrFun (congrFun h₂ 0) 0
  have b10 := congrFun (congrFun h₂ 1) 0
  have b12 := congrFun (congrFun h₂ 1) 2
  have b20 := congrFun (congrFun h₂ 2) 0
  simp [bM, coe_tr1, coe_tr2, Matrix.mul_apply, Fin.sum_univ_three] at a00 a01 a02 a20 a21 b00 b10 b12 b20
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact b00
  · exact a00
  · exact b12
  · exact a02
  · exact a21
  · exact b20
  · linear_combination a01

theorem form_of_commute_blocks {A : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ B : SL(2, F), A * bM (B : Matrix (Fin 2) (Fin 2) F) = bM (B : Matrix (Fin 2) (Fin 2) F) * A) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 2 = 0 ∧ A 1 2 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = A 1 1 :=
  form_of_commute_bM (h tr1) (h tr2)

end Form

section Conj

open CFSG.ComponentClassification

@[expose] def bGL : SL(2, F) →* GL (Fin 3) F := (Matrix.SpecialLinearGroup.toGL).comp bSL

theorem coe_bGL (B : SL(2, F)) : ((bGL B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    bM (B : Matrix (Fin 2) (Fin 2) F) := rfl

theorem slConj_toGL (A : GL (Fin 3) F) (g : SL(3, F)) :
    Matrix.SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 F A g) =
      A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact coe_slConjugation A g

theorem scalars_toGL_mem_center {z : SL(3, F)} (hz : z ∈ scalars 3 F) :
    Matrix.SpecialLinearGroup.toGL z ∈ Subgroup.center (GL (Fin 3) F) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  rw [Subgroup.mem_center_iff]
  intro B
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (B : Matrix (Fin 3) (Fin 3) F) * (z : Matrix (Fin 3) (Fin 3) F) =
    (z : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F)
  rw [hc]
  exact (Matrix.scalar_commute (c : F) (fun r => Commute.all _ _) _).symm

theorem central_of_proj_conj (A : GL (Fin 3) F) (g : SL(3, F))
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A g) = proj 3 F g) :
    A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ * (Matrix.SpecialLinearGroup.toGL g)⁻¹ ∈
      Subgroup.center (GL (Fin 3) F) := by
  have hz := scalars_toGL_mem_center (proj_eq_proj_iff.1 h)
  rw [map_mul, map_inv, slConj_toGL] at hz
  set w : GL (Fin 3) F := A * Matrix.SpecialLinearGroup.toGL g * A⁻¹ with hw
  set γ : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL g with hγ
  have hc : γ * (w⁻¹ * γ) = (w⁻¹ * γ) * γ := Subgroup.mem_center_iff.1 hz γ
  have hwγ : γ * w⁻¹ = w⁻¹ * γ := mul_right_cancel (by rw [mul_assoc, hc, mul_assoc])
  have : w * γ⁻¹ = (w⁻¹ * γ)⁻¹ := by
    have h' := congrArg (fun x => x⁻¹) hwγ
    simpa [_root_.mul_inv_rev] using h'
  rw [this]
  exact Subgroup.inv_mem _ hz

theorem commute_blocks_of_fixes [Finite F] (h4 : 4 ≤ Nat.card F) (A : GL (Fin 3) F)
    (hfix : ∀ B : SL(2, F), conjAut 3 F A (blockEmb B) = blockEmb B) (B : SL(2, F)) :
    (A : Matrix (Fin 3) (Fin 3) F) * bM (B : Matrix (Fin 2) (Fin 2) F) =
      bM (B : Matrix (Fin 2) (Fin 2) F) * A := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h4' : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4')
  have key := perfect_commute_of_central_commutator hperf bGL A (fun B => by
    have := central_of_proj_conj A (bSL B) (by
      rw [← conjAut_proj]
      exact hfix B)
    exact this) B
  exact congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) key


theorem slConj_toGL_eq (g h : SL(3, F)) :
    CatalogueBHigherLinearAction.slConjugation 3 F (Matrix.SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [slConj_toGL, map_mul, map_mul, map_inv]

theorem conjAut_toGL (g : SL(3, F)) :
    conjAut 3 F (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj (proj 3 F g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective 3 F x
  rw [conjAut_proj, slConj_toGL_eq, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem slConj_bGL (C B : SL(2, F)) :
    CatalogueBHigherLinearAction.slConjugation 3 F (bGL C) (bSL B) = bSL (C * B * C⁻¹) := by
  rw [bGL, MonoidHom.comp_apply, slConj_toGL_eq, map_mul, map_mul, map_inv]

theorem conjAut_bGL_blockEmb (C B : SL(2, F)) :
    conjAut 3 F (bGL C) (blockEmb B) = blockEmb (C * B * C⁻¹) := by
  rw [blockEmb_apply, conjAut_proj, slConj_bGL]
  rfl

theorem bM_transpose (X : Matrix (Fin 2) (Fin 2) F) : (bM X)ᵀ = bM Xᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bM]

theorem transpose_inv_sl2 (B : SL(2, F)) :
    ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)ᵀ = ((jSL * B * jSL⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_jSL, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem dualAut_blockEmb (B : SL(2, F)) :
    dualAut 3 F (blockEmb B) = blockEmb (jSL * B * jSL⁻¹) := by
  rw [blockEmb_apply, dualAut_proj, blockEmb_apply]
  congr 1
  rw [← map_inv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose]
  have h1 : ((bSL (B⁻¹) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      bM ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := rfl
  have h2 : ((bSL (jSL * B * jSL⁻¹) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      bM ((jSL * B * jSL⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := rfl
  rw [h1, h2, bM_transpose, transpose_inv_sl2]

end Conj

section Fixing

theorem coe_scalar_GL (u : Fˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  rw [smul_one_eq_diagonal]
  rfl

theorem det_ne_zero_GL (A : GL (Fin 3) F) : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A)).ne_zero

open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear in
theorem aut_fixing_blockSub [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) {σ : MulAut (projectiveSL 3 F)} (hσ2 : σ * σ = 1)
    (hfix : ∀ s ∈ (blockSub : Subgroup (projectiveSL 3 F)), σ s = s) :
    σ = 1 ∨ σ = MulAut.conj tInv := by
  rcases lin_involution_cases hp hFc hf h2 hσ2 with ⟨A, u, hAA, rfl⟩ | ⟨A, hAs, rfl⟩
  · have hcomm := commute_blocks_of_fixes h4 A (fun B => hfix _ (blockEmb_mem B))
    obtain ⟨h01, h10, h02, h12, h20, h21, h00⟩ := form_of_commute_blocks hcomm
    have e00 := congrFun (congrFun hAA 0) 0
    have e22 := congrFun (congrFun hAA 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h02, h12, h20, h21] at e00 e22
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    have ha0 : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
      intro h
      rw [h] at e00
      simp at e00
      exact hu0 e00.symm
    have hm : ((A : Matrix (Fin 3) (Fin 3) F) 2 2 - (A : Matrix (Fin 3) (Fin 3) F) 0 0) *
        ((A : Matrix (Fin 3) (Fin 3) F) 2 2 + (A : Matrix (Fin 3) (Fin 3) F) 0 0) = 0 := by
      linear_combination e22 - e00
    rcases mul_eq_zero.1 hm with hm | hm
    · left
      have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ ha0) := by
        apply Units.ext
        rw [coe_scalar_GL]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h10, h02, h12, h20, h21, h00]
        all_goals linear_combination hm + h00
      rw [hA, conjAut_scalar]
    · right
      have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (-(A : Matrix (Fin 3) (Fin 3) F) 0 0) (neg_ne_zero.2 ha0)) *
          Matrix.SpecialLinearGroup.toGL dNeg := by
        apply Units.ext
        rw [Units.val_mul, coe_scalar_GL]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [h01, h10, h02, h12, h20, h21, h00, coe_dNeg]
        all_goals first | linear_combination hm + h00 | linear_combination hm - h00
      rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
      rfl
  · exfalso
    set A₁ : GL (Fin 3) F := A * bGL jSL with hA₁
    have hfix₁ : ∀ B : SL(2, F), conjAut 3 F A₁ (blockEmb B) = blockEmb B := by
      intro B
      rw [hA₁, map_mul, MulAut.mul_apply, conjAut_bGL_blockEmb, ← dualAut_blockEmb]
      exact hfix _ (blockEmb_mem B)
    have hcomm := commute_blocks_of_fixes h4 A₁ hfix₁
    obtain ⟨h01, h10, h02, h12, h20, h21, h00⟩ := form_of_commute_blocks hcomm
    have hA₁m : (A₁ : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * bM (jSL : SL(2, F)).1 := by
      rw [hA₁, Units.val_mul]
      rfl
    rw [hA₁m] at h01 h10 h02 h00
    simp [Matrix.mul_apply, Fin.sum_univ_three, bM, coe_jSL] at h01 h10 h02 h00
    have hs01 := congrFun (congrFun hAs 0) 1
    simp only [Matrix.transpose_apply] at hs01
    have hA01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      have : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination -h00 - hs01
      exact (mul_eq_zero.1 this).resolve_left h2
    apply det_ne_zero_GL A
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    fin_cases j
    · exact h01
    · exact hA01
    · exact h02

end Fixing

section Solvable

theorem comm_aux {p q r s a b c d a' b' c' d' : F}
    (hX1 : b * r = q * c) (hX2 : q * (a - d) = b * (p - s)) (hX3 : r * (a - d) = c * (p - s))
    (hY1 : b' * r = q * c') (hY2 : q * (a' - d') = b' * (p - s)) (hY3 : r * (a' - d') = c' * (p - s))
    (hK : q ≠ 0 ∨ r ≠ 0 ∨ p - s ≠ 0) :
    b * c' = b' * c ∧ b' * (a - d) = b * (a' - d') ∧ c * (a' - d') = c' * (a - d) := by
  rcases hK with hq | hr | hk
  · have h2 : b' * (a - d) = b * (a' - d') := by
      apply mul_left_cancel₀ hq
      linear_combination b' * hX2 - b * hY2
    refine ⟨?_, h2, ?_⟩
    · apply mul_left_cancel₀ hq
      linear_combination (-b) * hY1 + b' * hX1
    · apply mul_left_cancel₀ hq
      linear_combination (-r) * h2 - (a' - d') * hX1 + (a - d) * hY1
  · have h1 : b * c' = b' * c := by
      apply mul_left_cancel₀ hr
      linear_combination c' * hX1 - c * hY1
    have h2 : b' * (a - d) = b * (a' - d') := by
      apply mul_left_cancel₀ hr
      linear_combination b' * hX3 - b * hY3 - (p - s) * h1
    refine ⟨h1, h2, ?_⟩
    apply mul_left_cancel₀ hr
    linear_combination c * hY3 - c' * hX3
  · have h2 : b' * (a - d) = b * (a' - d') := by
      apply mul_left_cancel₀ hk
      linear_combination (-(a - d)) * hY2 + (a' - d') * hX2
    have h3 : c * (a' - d') = c' * (a - d) := by
      apply mul_left_cancel₀ hk
      linear_combination (-(a' - d')) * hX3 + (a - d) * hY3
    refine ⟨?_, h2, h3⟩
    apply mul_left_cancel₀ hk
    linear_combination (-r) * h2 - b * hY3 + b' * hX3

theorem commute_of_commute_nonscalar {K X Y : Matrix (Fin 2) (Fin 2) F}
    (hK : ∀ c : F, K ≠ c • 1) (hX : X * K = K * X) (hY : Y * K = K * Y) : X * Y = Y * X := by
  have hKne : K 0 1 ≠ 0 ∨ K 1 0 ≠ 0 ∨ K 0 0 - K 1 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h01, h10, h00⟩ := hcon
    apply hK (K 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, sub_eq_zero.1 h00]
  have hX0 := congrFun (congrFun hX 0) 0
  have hX1 := congrFun (congrFun hX 0) 1
  have hX2 := congrFun (congrFun hX 1) 0
  have hY0 := congrFun (congrFun hY 0) 0
  have hY1 := congrFun (congrFun hY 0) 1
  have hY2 := congrFun (congrFun hY 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at hX0 hX1 hX2 hY0 hY1 hY2
  obtain ⟨e1, e2, e3⟩ := comm_aux (p := K 0 0) (q := K 0 1) (r := K 1 0) (s := K 1 1)
    (a := X 0 0) (b := X 0 1) (c := X 1 0) (d := X 1 1) (a' := Y 0 0) (b' := Y 0 1) (c' := Y 1 0)
    (d' := Y 1 1) (by linear_combination hX0) (by linear_combination hX1)
    (by linear_combination -hX2) (by linear_combination hY0) (by linear_combination hY1)
    (by linear_combination -hY2) hKne
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp
    linear_combination e1
  · simp
    linear_combination e2
  · simp
    linear_combination e3
  · simp
    linear_combination -e1


@[expose] def cenSL (K : Matrix (Fin 2) (Fin 2) F) : Subgroup SL(2, F) where
  carrier := {X | (X : Matrix (Fin 2) (Fin 2) F) * K = K * X}
  one_mem' := by simp
  mul_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  inv_mem' := by
    intro X hX
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (X : Matrix (Fin 2) (Fin 2) F) * ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * K
        = ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * K * ((X : Matrix (Fin 2) (Fin 2) F) *
            ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := by rw [h2, Matrix.mul_one]
      _ = ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (K * X) *
            ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by simp only [Matrix.mul_assoc]
      _ = ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (X * K) *
            ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by rw [hX]
      _ = K * ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
          calc _ = (((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X) * K *
                ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by simp only [Matrix.mul_assoc]
            _ = K * ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by rw [h1, Matrix.one_mul]

theorem mem_cenSL {K : Matrix (Fin 2) (Fin 2) F} {X : SL(2, F)} :
    X ∈ cenSL K ↔ (X : Matrix (Fin 2) (Fin 2) F) * K = K * X := Iff.rfl

theorem twist_mul {K X Y : Matrix (Fin 2) (Fin 2) F} {a b : F} (hX : K * X = a • (X * K))
    (hY : K * Y = b • (Y * K)) : K * (X * Y) = (a * b) • ((X * Y) * K) := by
  calc K * (X * Y) = (K * X) * Y := by rw [Matrix.mul_assoc]
    _ = a • (X * K * Y) := by rw [hX, Matrix.smul_mul]
    _ = a • (X * (K * Y)) := by rw [Matrix.mul_assoc]
    _ = a • (X * (b • (Y * K))) := by rw [hY]
    _ = (a * b) • ((X * Y) * K) := by rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]

theorem twist_inv {K X X' : Matrix (Fin 2) (Fin 2) F} {a : F} (ha : a ≠ 0)
    (hX : K * X = a • (X * K)) (h1 : X' * X = 1) (h2 : X * X' = 1) : K * X' = a⁻¹ • (X' * K) := by
  have e1 : X' * (K * X) * X' = X' * K := by
    calc X' * (K * X) * X' = X' * (K * (X * X')) := by simp only [Matrix.mul_assoc]
      _ = X' * K := by rw [h2, Matrix.mul_one]
  have e2 : X' * (a • (X * K)) * X' = a • (K * X') := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc X' * (X * K) * X' = (X' * X) * K * X' := by simp only [Matrix.mul_assoc]
      _ = K * X' := by rw [h1, Matrix.one_mul]
  have e3 : X' * K = a • (K * X') := by
    rw [← e1, hX]
    exact e2
  rw [e3, smul_smul, inv_mul_cancel₀ ha, one_smul]


theorem commutator_mem_cenSL {K : Matrix (Fin 2) (Fin 2) F} {B C : SL(2, F)}
    (hB : ∃ ε : F, ε * ε = 1 ∧ K * (B : Matrix (Fin 2) (Fin 2) F) = ε • ((B : Matrix (Fin 2) (Fin 2) F) * K))
    (hC : ∃ ε : F, ε * ε = 1 ∧ K * (C : Matrix (Fin 2) (Fin 2) F) = ε • ((C : Matrix (Fin 2) (Fin 2) F) * K)) :
    ⁅B, C⁆ ∈ cenSL K := by
  obtain ⟨a, ha, hBa⟩ := hB
  obtain ⟨b, hb, hCb⟩ := hC
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have inv1 : ∀ X : SL(2, F), ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * X = 1 := fun X => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have inv2 : ∀ X : SL(2, F), (X : Matrix (Fin 2) (Fin 2) F) * ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 :=
    fun X => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBi := twist_inv ha0 hBa (inv1 B) (inv2 B)
  have hCi := twist_inv hb0 hCb (inv1 C) (inv2 C)
  have key := twist_mul (twist_mul (twist_mul hBa hCb) hBi) hCi
  have hab : a * b * a⁻¹ * b⁻¹ = 1 := by field_simp
  rw [hab, one_smul] at key
  rw [mem_cenSL, commutatorElement_def]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  exact key.symm

theorem isSolvable_of_twisted {K : Matrix (Fin 2) (Fin 2) F} (hK : ∀ c : F, K ≠ c • 1)
    (P : Subgroup SL(2, F))
    (hP : ∀ B ∈ P, ∃ ε : F, ε * ε = 1 ∧
      K * (B : Matrix (Fin 2) (Fin 2) F) = ε • ((B : Matrix (Fin 2) (Fin 2) F) * K)) :
    Group.IsSolvable ↥P := by
  rw [Group.isSolvable_def]
  refine ⟨2, ?_⟩
  have h1 : derivedSeries ↥P 1 ≤ (cenSL K).comap P.subtype := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact commutator_mem_cenSL (hP _ x.2) (hP _ y.2)
  rw [eq_bot_iff, derivedSeries_succ, Subgroup.commutator_le]
  intro x hx y hy
  have hx' := h1 hx
  have hy' := h1 hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  have hcomm := commute_of_commute_nonscalar hK hx' hy'
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h2 := congrFun (congrFun hcomm i) j
  simpa [Matrix.SpecialLinearGroup.coe_mul] using h2

end Solvable

section B3

theorem mem_zpowers_involution {G : Type*} [Group G] {t x : G} (ht : t * t = 1)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [← hk, hm, _root_.zpow_mul, ht2, _root_.one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [← hk, hm, _root_.zpow_add, _root_.zpow_mul, ht2, _root_.one_zpow, one_mul, zpow_one]

theorem dNeg_inv_transpose : ((dNeg : SL(3, F))⁻¹).transpose = dNeg := by
  rw [inv_eq_of_mul_eq_one_right (dNeg_mul_self (F := F))]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose]
  fin_cases i <;> fin_cases j <;> simp [coe_dNeg]

open CFSG.ComponentClassification in
theorem conj_scalar_relation (A : GL (Fin 3) F) {g g' : SL(3, F)}
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A g') = proj 3 F g) :
    ∃ c : F, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      ((A : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F)) * Matrix.scalar (Fin 3) c := by
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  refine ⟨c, ?_, ?_⟩
  · have := congrArg (fun u : Fˣ => (u : F)) hc3
    simpa using this
  set w := CatalogueBHigherLinearAction.slConjugation 3 F A g' with hwdef
  have key : g = w * (w⁻¹ * g) := by group
  have hw : (w : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    coe_slConjugation A g'
  have hD : (g : Matrix (Fin 3) (Fin 3) F) = (w : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) := by
    have h' : ((w * (w⁻¹ * g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        (w : Matrix (Fin 3) (Fin 3) F) * ((w⁻¹ * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) :=
      Matrix.SpecialLinearGroup.coe_mul _ _
    rw [← key] at h'
    rw [h', hc]
  have hAi : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hscal : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) =
      Matrix.scalar (Fin 3) (c : F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    (Matrix.scalar_commute (c : F) (fun r => Commute.all _ _) _).symm
  calc (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
      = ((w : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F)) * (A : Matrix (Fin 3) (Fin 3) F) := by
        rw [← hD]
    _ = ((A : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F)) *
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F)) *
          (A : Matrix (Fin 3) (Fin 3) F) := by rw [hw]; simp only [Matrix.mul_assoc]
    _ = ((A : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F)) * Matrix.scalar (Fin 3) (c : F) *
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) := by
        rw [hscal]; simp only [Matrix.mul_assoc]
    _ = ((A : Matrix (Fin 3) (Fin 3) F) * (g' : Matrix (Fin 3) (Fin 3) F)) * Matrix.scalar (Fin 3) (c : F) := by
        rw [hAi, Matrix.mul_one]

open CFSG.ComponentClassification in
theorem commute_dNeg_of_proj (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F)
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A dNeg) = proj 3 F dNeg) :
    (A : Matrix (Fin 3) (Fin 3) F) * (dNeg : SL(3, F)).1 = (dNeg : SL(3, F)).1 * A := by
  obtain ⟨c, hc3, hM⟩ := conj_scalar_relation A h
  have hA0 : (A : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    intro h0
    apply det_ne_zero_GL A
    rw [h0]
    simp
  have hc1 := eq_one_of_dNeg_scalar h2 hA0 hc3 hM
  rw [hc1] at hM
  simp only [map_one, Matrix.mul_one] at hM
  exact hM.symm


theorem det_GL_eq (A : GL (Fin 3) F) (h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (A : Matrix (Fin 3) (Fin 3) F).det = ((A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 1 1 -
      (A : Matrix (Fin 3) (Fin 3) F) 0 1 * (A : Matrix (Fin 3) (Fin 3) F) 1 0) * (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  rw [Matrix.det_fin_three, h02, h12, h20, h21]
  ring

open CFSG.ComponentClassification in
theorem block_relation {A : GL (Fin 3) F} (h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) {B₀ B' : SL(2, F)}
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A (bSL B')) = proj 3 F (bSL B₀)) :
    (B₀ : Matrix (Fin 2) (Fin 2) F) *
        !![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 1;
          (A : Matrix (Fin 3) (Fin 3) F) 1 0, (A : Matrix (Fin 3) (Fin 3) F) 1 1] =
      !![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 1;
          (A : Matrix (Fin 3) (Fin 3) F) 1 0, (A : Matrix (Fin 3) (Fin 3) F) 1 1] *
        (B' : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc3, hrel⟩ := conj_scalar_relation A h
  have hdet := det_ne_zero_GL A
  rw [det_GL_eq A h02 h12 h20 h21] at hdet
  have hA22 : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := fun h0 => hdet (by rw [h0, mul_zero])
  have e22 := congrFun (congrFun hrel 2) 2
  simp [coe_bSL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply, h20, h21] at e22
  have hc1 : c = 1 := by
    have : (A : Matrix (Fin 3) (Fin 3) F) 2 2 * (c - 1) = 0 := by linear_combination -e22
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hA22)
  subst hc1
  simp only [map_one, Matrix.mul_one] at hrel
  have e00 := congrFun (congrFun hrel 0) 0
  have e01 := congrFun (congrFun hrel 0) 1
  have e10 := congrFun (congrFun hrel 1) 0
  have e11 := congrFun (congrFun hrel 1) 1
  simp [coe_bSL, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination e11


open CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear CFSG.ComponentClassification in
theorem graph_fixing_solvable [Finite F] {p f : ℕ} (hp : p.Prime) (hFc : Nat.card F = p ^ f) (hf : Odd f)
    (h2 : (2 : F) ≠ 0) {σ : MulAut (projectiveSL 3 F)} (hσ2 : σ * σ = 1)
    (hout : σ ∉ inner (projectiveSL 3 F)) (hσt : σ tInv = tInv)
    {P : Subgroup (projectiveSL 3 F)} (hPS : P ≤ blockSub)
    (hP : ∀ s ∈ P, σ s * s⁻¹ ∈ Subgroup.zpowers tInv) : Group.IsSolvable ↥P := by
  obtain ⟨A, hAs, rfl⟩ := lin_involution_form hp hFc hf h2 hσ2 hout
  have hcomm : (A : Matrix (Fin 3) (Fin 3) F) * (dNeg : SL(3, F)).1 = (dNeg : SL(3, F)).1 * A := by
    apply commute_dNeg_of_proj h2 A
    have h1 : (conjAut 3 F A * dualAut 3 F) tInv = tInv := hσt
    rw [MulAut.mul_apply, tInv, dualAut_proj, dNeg_inv_transpose, conjAut_proj] at h1
    exact h1
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_commute_dNeg h2 hcomm
  have hsym : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = (A : Matrix (Fin 3) (Fin 3) F) 0 1 := by
    have := congrFun (congrFun hAs 0) 1
    simpa [Matrix.transpose_apply] using this
  set M : Matrix (Fin 2) (Fin 2) F := !![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 1;
    (A : Matrix (Fin 3) (Fin 3) F) 1 0, (A : Matrix (Fin 3) (Fin 3) F) 1 1] with hM
  set K : Matrix (Fin 2) (Fin 2) F := M * (jSL : SL(2, F)).1 with hK
  have hKns : ∀ c : F, K ≠ c • 1 := by
    intro c hc
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e10 := congrFun (congrFun hc 1) 0
    have e11 := congrFun (congrFun hc 1) 1
    simp [hK, hM, coe_jSL] at e00 e01 e10 e11
    have hA01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      have : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by linear_combination -e00 + e11 - hsym
      exact (mul_eq_zero.1 this).resolve_left h2
    apply det_ne_zero_GL A
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    fin_cases j
    · exact e01
    · exact hA01
    · exact h02
  have hrel : ∀ B : SL(2, F), blockEmb B ∈ P → ∃ ε : F, ε * ε = 1 ∧
      K * (B : Matrix (Fin 2) (Fin 2) F) = ε • ((B : Matrix (Fin 2) (Fin 2) F) * K) := by
    intro B hB
    have hs := hP _ hB
    set B' : SL(2, F) := jSL * B * jSL⁻¹ with hB'
    have hσB : (conjAut 3 F A * dualAut 3 F) (blockEmb B) =
        proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A (bSL B')) := by
      rw [MulAut.mul_apply, dualAut_blockEmb, blockEmb_apply, conjAut_proj]
    have hBJ : (B' : Matrix (Fin 2) (Fin 2) F) * (jSL : SL(2, F)).1 = (jSL : SL(2, F)).1 * (B : Matrix (Fin 2) (Fin 2) F) := by
      have : B' * jSL = jSL * B := by rw [hB']; group
      have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) this
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
    rcases mem_zpowers_involution tInv_mul_self hs with h | h
    · have hσs : (conjAut 3 F A * dualAut 3 F) (blockEmb B) = blockEmb B := mul_inv_eq_one.1 h
      refine ⟨1, by norm_num, ?_⟩
      rw [hσB, blockEmb_apply] at hσs
      have hr := block_relation h02 h12 h20 h21 hσs
      rw [← hM] at hr
      calc K * (B : Matrix (Fin 2) (Fin 2) F) = M * ((jSL : SL(2, F)).1 * (B : Matrix (Fin 2) (Fin 2) F)) := by
            rw [hK, Matrix.mul_assoc]
        _ = M * ((B' : Matrix (Fin 2) (Fin 2) F) * (jSL : SL(2, F)).1) := by rw [hBJ]
        _ = (M * (B' : Matrix (Fin 2) (Fin 2) F)) * (jSL : SL(2, F)).1 := by rw [Matrix.mul_assoc]
        _ = ((B : Matrix (Fin 2) (Fin 2) F) * M) * (jSL : SL(2, F)).1 := by rw [hr]
        _ = (1 : F) • ((B : Matrix (Fin 2) (Fin 2) F) * K) := by
            rw [one_smul, hK, Matrix.mul_assoc]
    · have hσs : (conjAut 3 F A * dualAut 3 F) (blockEmb B) = blockEmb ((-1 : SL(2, F)) * B) := by
        rw [map_mul, blockEmb_neg_one, ← h]
        group
      refine ⟨-1, by norm_num, ?_⟩
      rw [hσB, blockEmb_apply] at hσs
      have hr := block_relation h02 h12 h20 h21 hσs
      rw [← hM] at hr
      have hneg : (((-1 : SL(2, F)) * B : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -(B : Matrix (Fin 2) (Fin 2) F) := by
        simp
      rw [hneg] at hr
      calc K * (B : Matrix (Fin 2) (Fin 2) F) = M * ((jSL : SL(2, F)).1 * (B : Matrix (Fin 2) (Fin 2) F)) := by
            rw [hK, Matrix.mul_assoc]
        _ = M * ((B' : Matrix (Fin 2) (Fin 2) F) * (jSL : SL(2, F)).1) := by rw [hBJ]
        _ = (M * (B' : Matrix (Fin 2) (Fin 2) F)) * (jSL : SL(2, F)).1 := by rw [Matrix.mul_assoc]
        _ = (-(B : Matrix (Fin 2) (Fin 2) F) * M) * (jSL : SL(2, F)).1 := by rw [hr]
        _ = (-1 : F) • ((B : Matrix (Fin 2) (Fin 2) F) * K) := by
            rw [hK, Matrix.mul_assoc, neg_smul, one_smul, Matrix.neg_mul]
  have hsolv : Group.IsSolvable ↥(P.comap (blockEmb : SL(2, F) →* projectiveSL 3 F)) :=
    isSolvable_of_twisted hKns _ (fun B hB => hrel B hB)
  let φ : ↥(P.comap (blockEmb : SL(2, F) →* projectiveSL 3 F)) →* ↥P :=
    ((blockEmb : SL(2, F) →* projectiveSL 3 F).comp
      (P.comap (blockEmb : SL(2, F) →* projectiveSL 3 F)).subtype).codRestrict P (fun B => B.2)
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨B, hB⟩ := hPS s.2
    exact ⟨⟨B, by rw [Subgroup.mem_comap]; exact hB ▸ s.2⟩, Subtype.ext hB⟩
  exact Group.isSolvable_of_surjective hφ

end B3

end CFSG.GH74.KGroups.L3Eps

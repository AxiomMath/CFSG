module

public import CFSG.LargeExtraspecial.A2ModSL
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F]

abbrev SL3 (F : Type) [Field F] := Matrix.SpecialLinearGroup (Fin 3) F

abbrev e0 : Fin 3 → F := Pi.single 0 1

@[expose] def levMat (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![X.det⁻¹, 0, 0; 0, X 0 0, X 0 1; 0, X 1 0, X 1 1]

theorem levMat_det {X : Matrix (Fin 2) (Fin 2) F} (hX : X.det ≠ 0) : (levMat X).det = 1 := by
  have h := hX
  rw [Matrix.det_fin_two] at h
  rw [levMat, Matrix.det_fin_three, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.tail_cons]
  field_simp
  ring

theorem levMat_mul (X Y : Matrix (Fin 2) (Fin 2) F) :
    levMat (X * Y) = levMat X * levMat Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [levMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_mul]; try ring)

@[expose] noncomputable def levSL (X : GL (Fin 2) F) : SL3 F :=
  ⟨levMat (X : Matrix (Fin 2) (Fin 2) F), levMat_det (by
    rw [← isUnit_iff_ne_zero]
    exact (Matrix.isUnit_det_of_invertible _))⟩

theorem coe_levSL (X : GL (Fin 2) F) :
    ((levSL X : SL3 F) : Matrix (Fin 3) (Fin 3) F) = levMat (X : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] noncomputable def lev : GL (Fin 2) F →* SL3 F where
  toFun := levSL
  map_one' := by
    refine Subtype.ext ?_
    rw [coe_levSL, Units.val_one, SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levMat]
  map_mul' X Y := by
    refine Subtype.ext ?_
    rw [SpecialLinearGroup.coe_mul, coe_levSL, coe_levSL, coe_levSL, Units.val_mul, levMat_mul]

theorem coe_lev (X : GL (Fin 2) F) :
    ((lev X : SL3 F) : Matrix (Fin 3) (Fin 3) F) = levMat (X : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem lev_injective : Function.Injective (lev : GL (Fin 2) F →* SL3 F) := by
  intro X Y h
  have h' := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_lev] at h'
  refine Units.ext ?_
  ext i j
  have := congrFun (congrFun h' i.succ) j.succ
  fin_cases i <;> fin_cases j <;> simpa [levMat] using this

@[expose] def P1 : Subgroup (SL3 F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    simp only [Set.mem_ofPred_eq, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
    rw [hg1, hg2, hh1, hh2]
    simp
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    simp only [Set.mem_ofPred_eq, SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [hg1, hg2]

theorem mem_P1 {g : SL3 F} :
    g ∈ P1 ↔ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 :=
  Iff.rfl

theorem mulVec_e0 (g : Matrix (Fin 3) (Fin 3) F) : g *ᵥ e0 = fun i => g i 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mem_P1_iff_exists {g : SL3 F} :
    g ∈ P1 ↔ ∃ c : F, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ e0 = c • e0 := by
  rw [mem_P1, mulVec_e0]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(g : Matrix (Fin 3) (Fin 3) F) 0 0, ?_⟩
    funext i
    fin_cases i <;> simp [h1, h2]
  · rintro ⟨c, hc⟩
    have h1 := congrFun hc 1
    have h2 := congrFun hc 2
    simp at h1 h2
    exact ⟨h1, h2⟩

theorem lev_mem_P1 (X : GL (Fin 2) F) : lev X ∈ P1 := by
  rw [mem_P1, coe_lev]
  simp [levMat]

theorem P1_det_eq {g : SL3 F} (hg : g ∈ P1) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 *
      ((g : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ).det = 1 := by
  obtain ⟨h1, h2⟩ := hg
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [h1, h2] at hdet
  linear_combination hdet

theorem P1_block_det_ne_zero {g : SL3 F} (hg : g ∈ P1) :
    ((g : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ).det ≠ 0 := by
  intro h
  have := P1_det_eq hg
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem P1_block_mul {g h : SL3 F} (hg : g ∈ P1) :
    ((g * h : SL3 F) : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ =
      (g : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ *
        (h : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ := by
  obtain ⟨h1, h2⟩ := hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      h1, h2]

@[expose] noncomputable def rho1 : (P1 : Subgroup (SL3 F)) →* GL (Fin 2) F where
  toFun g := GeneralLinearGroup.mkOfDetNeZero
    (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ)
    (P1_block_det_ne_zero g.2)
  map_one' := by
    refine Units.ext ?_
    ext i j
    simp [GeneralLinearGroup.mkOfDetNeZero, Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := by
    refine Units.ext ?_
    simp only [GeneralLinearGroup.mkOfDetNeZero, Subgroup.coe_mul, Units.val_mul]
    exact P1_block_mul g.2

theorem coe_rho1 (g : (P1 : Subgroup (SL3 F))) :
    ((rho1 g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F).submatrix Fin.succ Fin.succ :=
  rfl

theorem rho1_lev (X : GL (Fin 2) F) : rho1 ⟨lev X, lev_mem_P1 X⟩ = X := by
  refine Units.ext ?_
  rw [coe_rho1, coe_lev]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat]

theorem rho1_surjective : Function.Surjective (rho1 (F := F)) :=
  fun X => ⟨⟨lev X, lev_mem_P1 X⟩, rho1_lev X⟩

theorem rho1_mulVec (g : (P1 : Subgroup (SL3 F))) (v : Fin 3 → F) :
    ((rho1 g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => v i.succ) =
      fun i => (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i.succ := by
  obtain ⟨h1, h2⟩ := g.2
  funext i
  rw [coe_rho1]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, h1, h2]

abbrev Q1 : Subgroup (SL3 F) := pointGroup (e0 (F := F))

theorem Q1_le_P1 : (Q1 : Subgroup (SL3 F)) ≤ P1 := by
  intro g hg
  obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp hg
  rw [mem_P1_iff_exists]
  exact ⟨1, by rw [tv_mulVec hφ, hφ, zero_smul, add_zero, one_smul]⟩

theorem mem_ker_rho1 {g : (P1 : Subgroup (SL3 F))} : rho1 g = 1 ↔ (g : SL3 F) ∈ Q1 := by
  constructor
  · intro h
    have hb := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F)) h
    simp only [coe_rho1, Units.val_one] at hb
    obtain ⟨h1, h2⟩ := g.2
    have hb11 := congrFun (congrFun hb 0) 0
    have hb12 := congrFun (congrFun hb 0) 1
    have hb21 := congrFun (congrFun hb 1) 0
    have hb22 := congrFun (congrFun hb 1) 1
    simp only [Matrix.submatrix_apply, Matrix.one_apply] at hb11 hb12 hb21 hb22
    simp at hb11 hb12 hb21 hb22
    have hdet := P1_det_eq g.2
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.submatrix_apply] at hdet
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hb11 hb12 hb21 hb22 hdet
    rw [hb11, hb12, hb21, hb22] at hdet
    simp at hdet
    set φ : Fin 3 → F := ![0, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 1,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 2]
    have hφ : φ ⬝ᵥ e0 = 0 := by simp [φ, dotProduct, Fin.sum_univ_three]
    refine mem_pointGroup.mpr ⟨φ, hφ, ?_⟩
    refine Subtype.ext ?_
    rw [coe_tv hφ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [φ, Pi.single_apply, h1, h2, hb11, hb12,
        hb21, hb22, hdet]
  · intro hg'
    obtain ⟨φ, hφ, hg⟩ := mem_pointGroup.mp hg'
    have hφ0 : φ 0 = 0 := by simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using hφ
    refine Units.ext ?_
    rw [coe_rho1, ← hg, coe_tv hφ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply]

theorem ker_rho1 : (rho1 (F := F)).ker = (Q1 : Subgroup (SL3 F)).subgroupOf P1 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ker_rho1]

theorem card_Q1 : Nat.card (Q1 : Subgroup (SL3 F)) = Nat.card F ^ 2 := by
  classical
  set f : F × F → (Q1 : Subgroup (SL3 F)) := fun bc =>
    ⟨tv e0 ![0, bc.1, bc.2], tv_mem_pointGroup _ _⟩
  have hφ : ∀ bc : F × F, (![0, bc.1, bc.2] : Fin 3 → F) ⬝ᵥ e0 = 0 := fun bc => by
    simp [dotProduct, Fin.sum_univ_three]
  have hinj : Function.Injective f := by
    intro bc bc' h
    have h' := congrArg (fun g : (Q1 : Subgroup (SL3 F)) =>
      (((g : SL3 F)) : Matrix (Fin 3) (Fin 3) F)) h
    simp only [f, coe_tv (hφ bc), coe_tv (hφ bc')] at h'
    have h1 := congrFun (congrFun h' 0) 1
    have h2 := congrFun (congrFun h' 0) 2
    simp at h1 h2
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨φ, hφ', rfl⟩ := mem_pointGroup.mp hg
    have hφ0 : φ 0 = 0 := by simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using hφ'
    refine ⟨(φ 1, φ 2), Subtype.ext ?_⟩
    simp only [f]
    congr 1
    funext i
    fin_cases i <;> simp [hφ0]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, pow_two]

theorem card_P1 :
    Nat.card (P1 : Subgroup (SL3 F)) = Nat.card F ^ 2 * Nat.card (GL (Fin 2) F) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (rho1 (F := F)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ rho1_surjective).toEquiv,
    ker_rho1] at h
  rw [h, mul_comm, ← card_Q1]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q1_le_P1).toEquiv

theorem card_SL3_eq [Finite F] :
    Nat.card (SL3 F) = (Nat.card F ^ 2 + Nat.card F + 1) * Nat.card (P1 : Subgroup (SL3 F)) := by
  classical
  have := Fintype.ofFinite F
  have hq' : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  rw [card_P1, Matrix.card_GL_field, Matrix.card_SL_field, hq', Fin.prod_univ_two,
    Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have h1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 3 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5 : q ≤ q ^ 2 := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hkey : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * ((q ^ 2 + q + 1) * (q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 - q)))) := by
    zify [h1, h2, h3, h4, h5, hq1.le]
    ring
  rw [hkey, Nat.mul_div_cancel_left _ (by omega)]

theorem index_P1 [Finite F] :
    (P1 : Subgroup (SL3 F)).index = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := (P1 : Subgroup (SL3 F)).index_mul_card
  rw [card_SL3_eq] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

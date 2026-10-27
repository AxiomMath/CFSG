module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Torus

public section

namespace CFSG.AGLEmbedding.U62ThreeCent

open Matrix Equiv
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

noncomputable abbrev diagGL6 : (Fin 6 → F4ˣ) →* GL (Fin 6) F4 :=
  CFSG.RankThree.PartTwo.Sec4.Census.diagHom

theorem coe_diagGL6 (d : Fin 6 → F4ˣ) :
    (diagGL6 d : Matrix (Fin 6) (Fin 6) F4) = diagonal fun i => (d i : F4) :=
  rfl

@[expose] noncomputable def permGL : Perm (Fin 6) →* GL (Fin 6) F4 :=
  Matrix.permMatrixHom.toHomUnits

theorem coe_permGL (σ : Perm (Fin 6)) :
    ((permGL σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = (σ⁻¹).permMatrix F4 :=
  rfl

theorem coe_permGL_inv (σ : Perm (Fin 6)) :
    (((permGL σ)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = σ.permMatrix F4 := by
  rw [← map_inv, coe_permGL, inv_inv]

theorem permGL_mul_diagHom_mul_inv (σ : Perm (Fin 6)) (d : Fin 6 → F4ˣ) :
    permGL σ * diagGL6 d * (permGL σ)⁻¹ = diagGL6 (fun i => d (σ⁻¹ i)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL_inv, coe_permGL, coe_diagGL6, coe_diagGL6]
  ext i k
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

theorem permGL_mem (σ : Perm (Fin 6)) : permGL σ ∈ gramSU uData M6 := by
  have hmap : ((σ⁻¹).permMatrix F4).map uData.bar = (σ⁻¹).permMatrix F4 := by
    ext i j
    simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [coe_permGL, hmap, M6_eq_one, Matrix.mul_one, transpose_permMatrix, ← permMatrix_mul,
      mul_inv_cancel, permMatrix_one]
  · rw [coe_permGL, det_permutation]
    rcases Int.units_eq_one_or (Perm.sign σ⁻¹) with h | h
    · simp [h]
    · have hm1 : (-1 : F4) = 1 := by linear_combination (-1 : F4) * two_eq_zero_F4
      simp [h, hm1]

theorem exists_offDiag_permGL {σ : Perm (Fin 6)} (hσ : σ ≠ 1) :
    ∃ i j : Fin 6, i ≠ j ∧ ((permGL σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) i j = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, σ⁻¹ i ≠ i := by
    by_contra h
    push Not at h
    apply hσ
    have : σ⁻¹ = 1 := Equiv.ext h
    simpa using this
  refine ⟨i, σ⁻¹ i, fun h => hi h.symm, ?_⟩
  rw [coe_permGL]
  simp [PEquiv.toMatrix_apply]

theorem units_pow_three (c : F4ˣ) : c ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, pow_three_F4 c.ne_zero, Units.val_one])

theorem diagGL6_mem (d : Fin 6 → F4ˣ) (hd : ∏ i, d i = 1) : diagGL6 d ∈ gramSU uData M6 := by
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL6, Matrix.diagonal_map (map_zero _), diagonal_transpose, M6_eq_one,
      Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply]
    calc ((d i : F4ˣ) : F4) ^ 2 ^ 1 * (d i : F4ˣ) = ((d i : F4ˣ) : F4) ^ 3 := by ring
      _ = 1 := pow_three_F4 (d i).ne_zero
  · rw [coe_diagGL6, det_diagonal]
    have h1 := congrArg Units.val hd
    rwa [Units.coe_prod, Units.val_one] at h1

@[expose] noncomputable def diagSU6 (d : Fin 6 → F4ˣ) (hd : ∏ i, d i = 1) : gramSU uData M6 :=
  ⟨diagGL6 d, diagGL6_mem d hd⟩

theorem coe_diagSU6 (d : Fin 6 → F4ˣ) (hd : ∏ i, d i = 1) :
    ((diagSU6 d hd : gramSU uData M6) : GL (Fin 6) F4) = diagGL6 d :=
  rfl

theorem prod_const_units (c : F4ˣ) : ∏ _i : Fin 6, c = 1 := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_pow_three, one_pow]

@[expose] noncomputable def scalarSU6 (c : F4ˣ) : gramSU uData M6 :=
  diagSU6 (fun _ => c) (prod_const_units c)

theorem coe_scalarSU6 (c : F4ˣ) :
    ((scalarSU6 c : gramSU uData M6) : GL (Fin 6) F4) = GeneralLinearGroup.scalar (Fin 6) c := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, scalar_apply]
  rfl

theorem scalar_eq_diagGL6 (c : F4ˣ) :
    GeneralLinearGroup.scalar (Fin 6) c = diagGL6 (fun _ => c) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_diagGL6]

theorem mk_scalarSU6 (c : F4ˣ) : ((scalarSU6 c : gramSU uData M6) : P6) = 1 := by
  rw [QuotientGroup.eq_one_iff]
  refine ⟨c, norm_eq_one c, ?_, coe_scalarSU6 c⟩
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, units_pow_three, one_pow]

theorem diag_last_eq (d : Fin 6 → F4ˣ) (hd : ∏ i, d i = 1) :
    d 4 = d 5 * ((d 0 * (d 5)⁻¹) * (d 1 * (d 5)⁻¹) * (d 2 * (d 5)⁻¹) * (d 3 * (d 5)⁻¹))⁻¹ := by
  have hd' : d 0 * d 1 * d 2 * d 3 * d 4 * d 5 = 1 := by
    simpa [Fin.prod_univ_six] using hd
  have h5 : d 5 ^ 3 = 1 := units_pow_three _
  apply Units.ext
  have hd'' := congrArg Units.val hd'
  have h5' := congrArg Units.val h5
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_one] at hd'' h5' ⊢
  have hne : ∀ i, ((d i : F4ˣ) : F4) ≠ 0 := fun i => (d i).ne_zero
  field_simp
  apply mul_right_cancel₀ (hne 5)
  linear_combination hd'' - (((d 5 : F4ˣ) : F4) ^ 3 + 1) * h5'

theorem mk_diagSU6_mem_range (d : Fin 6 → F4ˣ) (hd : ∏ i, d i = 1) :
    ((diagSU6 d hd : gramSU uData M6) : P6) ∈ torusP6.range := by
  set z : Fin 4 → F4ˣ := fun i => d (Fin.castLE (by norm_num) i) * (d 5)⁻¹ with hz
  refine ⟨z, ?_⟩
  have hfun : d = fun i => d 5 * CFSG.RankThree.PartTwo.Sec4.Census.torus6 z i := by
    funext i
    fin_cases i
    · simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6, hz]
    · simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6, hz]
    · simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6, hz]
    · simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6, hz]
    · have h4 := diag_last_eq d hd
      simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6, hz]
      exact h4
    · simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6]
  have key : diagSU6 d hd = scalarSU6 (d 5) * torusSU6 z := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_diagSU6, coe_scalarSU6, coe_torusSU6]
    change diagGL6 d = GeneralLinearGroup.scalar (Fin 6) (d 5) *
      diagGL6 (CFSG.RankThree.PartTwo.Sec4.Census.torus6 z)
    rw [scalar_eq_diagGL6, ← map_mul]
    exact congrArg diagGL6 hfun
  show torusP6 z = ((diagSU6 d hd : gramSU uData M6) : P6)
  rw [key, QuotientGroup.mk_mul, mk_scalarSU6, one_mul]
  rfl

theorem prod_torus6 (z : Fin 4 → F4ˣ) :
    ∏ i, CFSG.RankThree.PartTwo.Sec4.Census.torus6 z i = 1 := by
  rw [Fin.prod_univ_six]
  simp [CFSG.RankThree.PartTwo.Sec4.Census.torus6]

theorem conj6_gramSU (g : gramSU uData M6) (e : P6) :
    conj6 ⟨(g : GL (Fin 6) F4), g.2.1⟩ e = (g : P6) * e * (g : P6)⁻¹ := by
  induction e using QuotientGroup.induction_on with
  | H h =>
    rw [primeFormConjHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl

theorem exists_y (a : gramSU uData M6) (δ : Fin 6 → F4ˣ) (hδ : (a : GL (Fin 6) F4) = diagGL6 δ)
    (σ : Perm (Fin 6)) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (lam : F4ˣ)
    (hlam : ∀ i, δ (σ i) = lam * δ i) :
    ∃ y : P6, y ∈ Subgroup.centralizer ({(a : P6)} : Set P6) ∧
      y ∈ Subgroup.normalizer (torusP6.range : Set P6) ∧ y ∉ torusP6.range ∧ y ^ 3 = 1 := by
  set πg : gramSU uData M6 := ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩ with hπ
  have hconjGL : ∀ d : Fin 6 → F4ˣ,
      permGL σ⁻¹ * diagGL6 d * (permGL σ⁻¹)⁻¹ = diagGL6 (fun i => d (σ i)) := by
    intro d
    rw [permGL_mul_diagHom_mul_inv]
    simp only [inv_inv]
  refine ⟨(πg : P6), ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : πg * a * πg⁻¹ = scalarSU6 lam * a := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, coe_scalarSU6, hδ]
      change permGL σ⁻¹ * diagGL6 δ * (permGL σ⁻¹)⁻¹ =
        GeneralLinearGroup.scalar (Fin 6) lam * diagGL6 δ
      rw [hconjGL, scalar_eq_diagGL6, ← map_mul]
      congr 1
      funext i
      exact hlam i
    have h2 : (πg : P6) * (a : P6) * (πg : P6)⁻¹ = (a : P6) := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1,
        QuotientGroup.mk_mul, mk_scalarSU6, one_mul]
    exact mul_inv_eq_iff_eq_mul.1 h2
  ·
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨z, rfl⟩ := hn
    have hprod : ∏ i, CFSG.RankThree.PartTwo.Sec4.Census.torus6 z (σ i) = 1 := by
      rw [Equiv.prod_comp σ (fun i => CFSG.RankThree.PartTwo.Sec4.Census.torus6 z i)]
      exact prod_torus6 z
    have h3 : πg * torusSU6 z * πg⁻¹ =
        diagSU6 (fun i => CFSG.RankThree.PartTwo.Sec4.Census.torus6 z (σ i)) hprod := by
      apply Subtype.ext
      change permGL σ⁻¹ * diagGL6 (CFSG.RankThree.PartTwo.Sec4.Census.torus6 z) *
        (permGL σ⁻¹)⁻¹ = diagGL6 (fun i => CFSG.RankThree.PartTwo.Sec4.Census.torus6 z (σ i))
      exact hconjGL _
    have h4 : (πg : P6) * torusP6 z * (πg : P6)⁻¹ =
        ((diagSU6 (fun i => CFSG.RankThree.PartTwo.Sec4.Census.torus6 z (σ i)) hprod :
          gramSU uData M6) : P6) := by
      rw [← h3, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
    exact h4 ▸ mk_diagSU6_mem_range _ hprod
  ·
    rintro ⟨z, hz⟩
    have hmem : πg⁻¹ * torusSU6 z ∈ normOneScalars uData (gramSU uData M6) 6 :=
      QuotientGroup.eq.1 hz.symm
    obtain ⟨c, -, -, hc⟩ := hmem
    have hc' : (permGL σ⁻¹)⁻¹ * torusGL6 z = GeneralLinearGroup.scalar (Fin 6) c := hc
    have hT : torusGL6 z = permGL σ⁻¹ * GeneralLinearGroup.scalar (Fin 6) c := by
      rw [← hc', mul_inv_cancel_left]
    obtain ⟨i, j, hij, hP⟩ := exists_offDiag_permGL (inv_ne_one.2 hσ1)
    have h5 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) i j) hT
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
      Matrix.mul_diagonal, hP, one_mul, coe_torusGL6, diagonal_apply_ne _ hij] at h5
    exact c.ne_zero h5.symm
  ·
    have h6 : πg ^ 3 = 1 := by
      apply Subtype.ext
      change (permGL σ⁻¹) ^ 3 = 1
      rw [← map_pow, inv_pow, hσ3, inv_one, map_one]
    rw [← QuotientGroup.mk_pow, h6]
    rfl

end CFSG.AGLEmbedding.U62ThreeCent

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Layer
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

open Matrix
open scoped MatrixGroups

variable (F : Type*) [Field F]

theorem coe_SL_mul {n : ℕ} (A B : SL(n, F)) :
    ((A * B : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) := rfl

theorem coe_SL_inv {n : ℕ} (A : SL(n, F)) :
    ((A⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = adjugate (A : Matrix (Fin n) (Fin n) F) :=
  rfl

theorem coe_SL_one {n : ℕ} : ((1 : SL(n, F)) : Matrix (Fin n) (Fin n) F) = 1 := rfl

theorem coe_SL_pow {n : ℕ} (A : SL(n, F)) (k : ℕ) :
    ((A ^ k : SL(n, F)) : Matrix (Fin n) (Fin n) F) = (A : Matrix (Fin n) (Fin n) F) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, coe_SL_mul, ih, pow_succ]

@[expose] def mkSL {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (h : M.det = 1) : SL(n, F) := ⟨M, h⟩

theorem coe_mkSL {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (h : M.det = 1) :
    ((mkSL F M h : SL(n, F)) : Matrix (Fin n) (Fin n) F) = M := rfl

@[expose] def triSL2 [CharP F 2] : SL(2, F) :=
  mkSL F !![0, 1; 1, 1] (by simp [det_fin_two, CharTwo.neg_eq])

theorem orderOf_tri [CharP F 2] : orderOf (triSL2 F) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [coe_SL_pow, triSL2, coe_mkSL, coe_SL_one, pow_succ, pow_succ, pow_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro h
    have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [triSL2, coe_mkSL, coe_SL_one] at this
    simp at this

theorem three_dvd_card_SL2 [CharP F 2] [Finite F] : 3 ∣ Nat.card SL(2, F) := by
  rw [← orderOf_tri F]
  exact orderOf_dvd_natCard _

@[expose] def upperSL2 : SL(2, F) := mkSL F !![1, 1; 0, 1] (by simp [det_fin_two])

@[expose] def lowerSL2 : SL(2, F) := mkSL F !![1, 0; 1, 1] (by simp [det_fin_two])

theorem SL2_nonabelian : ∃ a b : SL(2, F), a * b ≠ b * a := by
  refine ⟨upperSL2 F, lowerSL2 F, fun h => ?_⟩
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp only [coe_SL_mul, upperSL2, lowerSL2, coe_mkSL] at this
  simp [mul_apply, Fin.sum_univ_two] at this

theorem center_SL2_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h0 : (r - 1) ^ 2 = 0 := by rw [sub_pow_char, hr, one_pow, sub_self]
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  rw [Subgroup.mem_bot]
  rw [hr1, map_one] at hA'
  exact Subtype.ext hA'.symm

theorem isSimpleGroup_SL2 [CharP F 2] (h4 : 4 ≤ Nat.card F) : IsSimpleGroup SL(2, F) := by
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact ((QuotientGroup.quotientMulEquivOfEq (center_SL2_eq_bot F)).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

@[expose] def diagSL2 : Fˣ →* SL(2, F) where
  toFun t := mkSL F !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] (by
    rw [det_fin_two_of, mul_zero, sub_zero, Units.mul_inv])
  map_one' := by
    apply Subtype.ext
    rw [coe_mkSL, coe_SL_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' s t := by
    apply Subtype.ext
    rw [coe_SL_mul, coe_mkSL, coe_mkSL, coe_mkSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]

theorem card_units_dvd_card_SL2 [Finite F] : Nat.card Fˣ ∣ Nat.card SL(2, F) := by
  refine Subgroup.card_dvd_of_injective (diagSL2 F) fun s t hst => ?_
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hst
  simp only [diagSL2, MonoidHom.coe_mk, OneHom.coe_mk, coe_mkSL] at this
  exact Units.ext (by simpa using this)

@[expose] def parA : Subgroup SL(3, F) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩ <;>
    · rw [coe_SL_mul]
      simp only [mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]
      ring
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> · rw [coe_SL_one]; simp
  inv_mem' := by
    rintro A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩ <;> · rw [coe_SL_inv, adjugate_fin_three]; simp [h1, h2]

theorem mem_parA {A : SL(3, F)} :
    A ∈ parA F ↔ (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 :=
  Iff.rfl

@[expose] def cornerA : parA F →* F where
  toFun A := ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0
  map_one' := by rw [Subgroup.coe_one, coe_SL_one]; simp
  map_mul' A B := by
    obtain ⟨hA1, hA2⟩ := (mem_parA F).1 A.2
    rw [Subgroup.coe_mul, coe_SL_mul]
    simp [mul_apply, Fin.sum_univ_three, hA1, hA2]

theorem cornerA_apply (A : parA F) :
    cornerA F A = ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0 := rfl

@[expose] def blockA : parA F →* Matrix (Fin 2) (Fin 2) F where
  toFun A := !![((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 1,
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 2;
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 1,
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2]
  map_one' := by
    rw [Subgroup.coe_one, coe_SL_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    obtain ⟨hB1, hB2⟩ := (mem_parA F).1 B.2
    rw [Subgroup.coe_mul, coe_SL_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hB1, hB2]

theorem blockA_apply (A : parA F) :
    blockA F A = !![((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 1,
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 2;
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 1,
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2] := rfl

theorem det_eq_cornerA_mul (A : parA F) : cornerA F A * (blockA F A).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_parA F).1 A.2
  have hdet : ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).det = 1 := (A : SL(3, F)).2
  rw [det_fin_three, h1, h2] at hdet
  rw [cornerA_apply, blockA_apply, det_fin_two_of]
  linear_combination hdet

@[expose] def leviA : parA F →* F × Matrix (Fin 2) (Fin 2) F := (cornerA F).prod (blockA F)

theorem sq_eq_one_of_mem_ker_leviA [CharP F 2] {A : parA F} (hA : leviA F A = 1) :
    A * A = 1 := by
  obtain ⟨h1, h2⟩ := (mem_parA F).1 A.2
  have hc : cornerA F A = 1 := congrArg Prod.fst hA
  have hb : blockA F A = 1 := congrArg Prod.snd hA
  rw [cornerA_apply] at hc
  rw [blockA_apply] at hb
  have e11 := congrFun (congrFun hb 0) 0
  have e12 := congrFun (congrFun hb 0) 1
  have e21 := congrFun (congrFun hb 1) 0
  have e22 := congrFun (congrFun hb 1) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e11 e12 e21 e22
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, coe_SL_mul, coe_SL_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h1, h2, hc, e11, e12, e21, e22, CharTwo.add_self_eq_zero]

@[expose] def embedA (M : SL(2, F)) : parA F :=
  ⟨mkSL F !![1, 0, 0; 0, (M : Matrix (Fin 2) (Fin 2) F) 0 0, (M : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (M : Matrix (Fin 2) (Fin 2) F) 1 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1] (by
    have h := M.2
    rw [det_fin_two] at h
    simp [det_fin_three]
    linear_combination h), by
    refine ⟨?_, ?_⟩ <;> · rw [coe_mkSL]; simp⟩

theorem cornerA_embedA (M : SL(2, F)) : cornerA F (embedA F M) = 1 := by
  rw [cornerA_apply, embedA]
  simp only [coe_mkSL]
  simp

theorem blockA_embedA (M : SL(2, F)) : blockA F (embedA F M) = M := by
  rw [blockA_apply, embedA]
  simp only [coe_mkSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def parB : Subgroup SL(3, F) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0}
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨?_, ?_⟩ <;>
    · rw [coe_SL_mul]
      simp only [mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]
      ring
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> · rw [coe_SL_one]; simp
  inv_mem' := by
    rintro A ⟨h1, h2⟩
    refine ⟨?_, ?_⟩ <;> · rw [coe_SL_inv, adjugate_fin_three]; simp [h1, h2]

theorem mem_parB {A : SL(3, F)} :
    A ∈ parB F ↔ (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 :=
  Iff.rfl

@[expose] def cornerB : parB F →* F where
  toFun A := ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2
  map_one' := by rw [Subgroup.coe_one, coe_SL_one]; simp
  map_mul' A B := by
    obtain ⟨hB1, hB2⟩ := (mem_parB F).1 B.2
    rw [Subgroup.coe_mul, coe_SL_mul]
    simp [mul_apply, Fin.sum_univ_three, hB1, hB2]

theorem cornerB_apply (A : parB F) :
    cornerB F A = ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 2 2 := rfl

@[expose] def blockB : parB F →* Matrix (Fin 2) (Fin 2) F where
  toFun A := !![((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0,
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 1;
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 0,
    ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 1]
  map_one' := by
    rw [Subgroup.coe_one, coe_SL_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    obtain ⟨hA1, hA2⟩ := (mem_parB F).1 A.2
    rw [Subgroup.coe_mul, coe_SL_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hA1, hA2]

theorem blockB_apply (A : parB F) :
    blockB F A = !![((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 0,
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 0 1;
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 0,
      ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) 1 1] := rfl

theorem det_eq_cornerB_mul (A : parB F) : cornerB F A * (blockB F A).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_parB F).1 A.2
  have hdet : ((A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).det = 1 := (A : SL(3, F)).2
  rw [det_fin_three, h1, h2] at hdet
  rw [cornerB_apply, blockB_apply, det_fin_two_of]
  linear_combination hdet

@[expose] def leviB : parB F →* F × Matrix (Fin 2) (Fin 2) F := (cornerB F).prod (blockB F)

theorem sq_eq_one_of_mem_ker_leviB [CharP F 2] {A : parB F} (hA : leviB F A = 1) :
    A * A = 1 := by
  obtain ⟨h1, h2⟩ := (mem_parB F).1 A.2
  have hc : cornerB F A = 1 := congrArg Prod.fst hA
  have hb : blockB F A = 1 := congrArg Prod.snd hA
  rw [cornerB_apply] at hc
  rw [blockB_apply] at hb
  have e11 := congrFun (congrFun hb 0) 0
  have e12 := congrFun (congrFun hb 0) 1
  have e21 := congrFun (congrFun hb 1) 0
  have e22 := congrFun (congrFun hb 1) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e11 e12 e21 e22
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, coe_SL_mul, coe_SL_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, h1, h2, hc, e11, e12, e21, e22, CharTwo.add_self_eq_zero]

@[expose] def embedB (M : SL(2, F)) : parB F :=
  ⟨mkSL F !![(M : Matrix (Fin 2) (Fin 2) F) 0 0, (M : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
      (M : Matrix (Fin 2) (Fin 2) F) 1 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] (by
    have h := M.2
    rw [det_fin_two] at h
    simp [det_fin_three]
    linear_combination h), by
    refine ⟨?_, ?_⟩ <;> · rw [coe_mkSL]; simp⟩

theorem cornerB_embedB (M : SL(2, F)) : cornerB F (embedB F M) = 1 := by
  rw [cornerB_apply, embedB]
  simp only [coe_mkSL]
  simp

theorem blockB_embedB (M : SL(2, F)) : blockB F (embedB F M) = M := by
  rw [blockB_apply, embedB]
  simp only [coe_mkSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {F}

theorem le_pPrimeCore_three_of_sq {X : Type*} [Group X] [Finite X] {U : Subgroup X}
    [hU : U.Normal] (h2 : ∀ u ∈ U, u * u = 1) : U ≤ CFSG.pPrimeCore 3 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 U := fun u => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (h2 u u.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  refine le_sSup ⟨hU, ?_⟩
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem card_SL2_dvd_pLayer_A [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {X : Type*}
    [Group X] [Finite X] (φ : X ≃* parA F) : Nat.card SL(2, F) ∣ Nat.card (CFSG.pLayer X 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup SL(2, F) := isSimpleGroup_SL2 F h4
  set Y : Subgroup X := ((cornerA F).comp φ.toMonoidHom).ker with hY
  set U : Subgroup X := ((leviA F).comp φ.toMonoidHom).ker with hU
  haveI : Y.Normal := MonoidHom.normal_ker _
  haveI : U.Normal := MonoidHom.normal_ker _
  have hYc : ∀ y : Y, cornerA F (φ y) = 1 := fun y => MonoidHom.mem_ker.1 y.2
  let ψ : Y →* SL(2, F) :=
    { toFun := fun y => mkSL F (blockA F (φ y)) (by
        have := det_eq_cornerA_mul F (φ y)
        rwa [hYc y, one_mul] at this)
      map_one' := Subtype.ext (by rw [coe_mkSL, coe_SL_one]; simp)
      map_mul' := fun y z => Subtype.ext (by
        rw [coe_SL_mul, coe_mkSL, coe_mkSL, coe_mkSL]
        simp [map_mul]) }
  have hψ : Function.Surjective ψ := by
    intro M
    refine ⟨⟨φ.symm (embedA F M), ?_⟩, ?_⟩
    · rw [hY, MonoidHom.mem_ker]
      change cornerA F (φ (φ.symm (embedA F M))) = 1
      rw [φ.apply_symm_apply]
      exact cornerA_embedA F M
    · apply Subtype.ext
      change blockA F (φ (φ.symm (embedA F M))) = _
      rw [φ.apply_symm_apply, blockA_embedA]
  have hker : ∀ y : Y, ψ y = 1 → (y : X) ∈ CFSG.pPrimeCore 3 X := by
    intro y hy
    have hb : blockA F (φ y) = 1 := by
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hy
      exact this
    have hyU : (y : X) ∈ U := by
      rw [hU, MonoidHom.mem_ker]
      exact Prod.ext (hYc y) hb
    refine le_pPrimeCore_three_of_sq (U := U) (fun u hu => ?_) hyU
    apply φ.injective
    rw [map_mul, map_one]
    exact sq_eq_one_of_mem_ker_leviA F (MonoidHom.mem_ker.1 hu)
  exact card_dvd_card_pLayer 3 Y (SL2_nonabelian F) (three_dvd_card_SL2 F) ψ hψ hker

theorem card_SL2_dvd_pLayer_B [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {X : Type*}
    [Group X] [Finite X] (φ : X ≃* parB F) : Nat.card SL(2, F) ∣ Nat.card (CFSG.pLayer X 3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup SL(2, F) := isSimpleGroup_SL2 F h4
  set Y : Subgroup X := ((cornerB F).comp φ.toMonoidHom).ker with hY
  set U : Subgroup X := ((leviB F).comp φ.toMonoidHom).ker with hU
  haveI : Y.Normal := MonoidHom.normal_ker _
  haveI : U.Normal := MonoidHom.normal_ker _
  have hYc : ∀ y : Y, cornerB F (φ y) = 1 := fun y => MonoidHom.mem_ker.1 y.2
  let ψ : Y →* SL(2, F) :=
    { toFun := fun y => mkSL F (blockB F (φ y)) (by
        have := det_eq_cornerB_mul F (φ y)
        rwa [hYc y, one_mul] at this)
      map_one' := Subtype.ext (by rw [coe_mkSL, coe_SL_one]; simp)
      map_mul' := fun y z => Subtype.ext (by
        rw [coe_SL_mul, coe_mkSL, coe_mkSL, coe_mkSL]
        simp [map_mul]) }
  have hψ : Function.Surjective ψ := by
    intro M
    refine ⟨⟨φ.symm (embedB F M), ?_⟩, ?_⟩
    · rw [hY, MonoidHom.mem_ker]
      change cornerB F (φ (φ.symm (embedB F M))) = 1
      rw [φ.apply_symm_apply]
      exact cornerB_embedB F M
    · apply Subtype.ext
      change blockB F (φ (φ.symm (embedB F M))) = _
      rw [φ.apply_symm_apply, blockB_embedB]
  have hker : ∀ y : Y, ψ y = 1 → (y : X) ∈ CFSG.pPrimeCore 3 X := by
    intro y hy
    have hb : blockB F (φ y) = 1 := by
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) hy
      exact this
    have hyU : (y : X) ∈ U := by
      rw [hU, MonoidHom.mem_ker]
      exact Prod.ext (hYc y) hb
    refine le_pPrimeCore_three_of_sq (U := U) (fun u hu => ?_) hyU
    apply φ.injective
    rw [map_mul, map_one]
    exact sq_eq_one_of_mem_ker_leviB F (MonoidHom.mem_ker.1 hu)
  exact card_dvd_card_pLayer 3 Y (SL2_nonabelian F) (three_dvd_card_SL2 F) ψ hψ hker

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K136

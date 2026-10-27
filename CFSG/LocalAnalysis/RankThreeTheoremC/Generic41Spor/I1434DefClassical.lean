module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434DefCount
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Proj
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.RankThree.PartOne.S11c.UnitaryFiveData

public section

open CFSG.Open
open CFSG.EvenSmallLie.CatalogOrders (lieExp lieMin pow_lieExp_dvd card_eq_lieOrd_of_classical)
open scoped commutatorElement

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

theorem charP_five_of_card_eq_five_pow {F : Type} [Field F] [Finite F] {m : ℕ}
    (h : Nat.card F = 5 ^ m) : CharP F 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem fiveExpLe_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] [CharP F 5] (H : Subgroup (GL ι F)) {k : ℕ} (hk : Fintype.card ι ≤ 5 ^ k) :
    FiveExpLe (StatedProj H) k :=
  FiveExpLe.of_surjective (QuotientGroup.mk'_surjective _) ((fiveExpLe_GL hk).subgroup H)

theorem mul_lieExp_le_factorization_five {K : Type} [Group K] [Finite K] {t : StatedLieTag}
    {n f : ℕ} (hM : StatedClassicalModel K t n 5 f) (hn : lieMin t ≤ n) :
    f * lieExp t n ≤ (Nat.card K).factorization 5 := by
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have h1 : 5 ^ (f * lieExp t n) ∣ Nat.card K := by
    rw [pow_mul, card_eq_lieOrd_of_classical hM]
    exact pow_lieExp_dvd hn _
  exact (Nat.prime_five.pow_dvd_iff_le_factorization hK0).1 h1

theorem Data.false_of_classicalModel {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) {t : StatedLieTag} {n f : ℕ}
    (hM : StatedClassicalModel K t n 5 f) (hn : lieMin t ≤ n) {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 5] {H : Subgroup (GL ι F)}
    (e : K ≃* StatedProj H) {k : ℕ} (hk : Fintype.card ι ≤ 5 ^ k)
    (hlt : 3 * k < f * lieExp t n) : False :=
  hD.false_of_fiveExpLe ((fiveExpLe_statedProj H hk).of_mulEquiv e.symm)
    (hlt.trans_le (mul_lieExp_le_factorization_five hM hn))

private theorem four_mul_add_five_le (m : ℕ) : 4 * m + 5 ≤ 5 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

private theorem lt_mul_of_lt_of_one_le {a N f : ℕ} (h : a < N) (hf : 1 ≤ f) : a < f * N :=
  h.trans_le (Nat.le_mul_of_pos_left _ (by omega))

private theorem three_mul_lt_linear (m f : ℕ) (hf : 1 ≤ f) :
    3 * (m + 1) < f * ((m + 4 - 1) * (m + 4) / 2) := by
  refine lt_mul_of_lt_of_one_le ?_ hf
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by norm_num),
    show m + 4 - 1 = m + 3 from rfl]
  nlinarith

section SL3

variable {F : Type} [Field F]

@[expose] def sl3TransA : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def sl3TransB : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def sl3TransC : Matrix (Fin 3) (Fin 3) F := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

theorem sl3Trans_AC :
    (sl3TransA : Matrix (Fin 3) (Fin 3) F) * sl3TransC = sl3TransC * sl3TransA := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl3TransA, sl3TransC, Matrix.mul_apply, Fin.sum_univ_three]

theorem sl3Trans_BC :
    (sl3TransB : Matrix (Fin 3) (Fin 3) F) * sl3TransC = sl3TransC * sl3TransB := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl3TransB, sl3TransC, Matrix.mul_apply, Fin.sum_univ_three]

theorem sl3Trans_AB :
    (sl3TransA : Matrix (Fin 3) (Fin 3) F) * sl3TransB = sl3TransC * (sl3TransB * sl3TransA) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3TransA, sl3TransB, sl3TransC, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_sl3TransA : (sl3TransA : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [sl3TransA, Matrix.det_fin_three]

theorem det_sl3TransB : (sl3TransB : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [sl3TransB, Matrix.det_fin_three]

theorem det_sl3TransC : (sl3TransC : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [sl3TransC, Matrix.det_fin_three]

variable [CharP F 5]

theorem sl3TransA_pow : (sl3TransA : Matrix (Fin 3) (Fin 3) F) ^ 5 = 1 := by
  have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3TransA, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num <;> exact h5

theorem sl3TransB_pow : (sl3TransB : Matrix (Fin 3) (Fin 3) F) ^ 5 = 1 := by
  have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3TransB, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num <;> exact h5

theorem sl3TransC_pow : (sl3TransC : Matrix (Fin 3) (Fin 3) F) ^ 5 = 1 := by
  have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl3TransC, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num <;> exact h5

@[expose] def glTransA : GL (Fin 3) F :=
  ⟨sl3TransA, sl3TransA ^ 4, by rw [← pow_succ', sl3TransA_pow],
    by rw [← pow_succ, sl3TransA_pow]⟩

@[expose] def glTransB : GL (Fin 3) F :=
  ⟨sl3TransB, sl3TransB ^ 4, by rw [← pow_succ', sl3TransB_pow],
    by rw [← pow_succ, sl3TransB_pow]⟩

@[expose] def glTransC : GL (Fin 3) F :=
  ⟨sl3TransC, sl3TransC ^ 4, by rw [← pow_succ', sl3TransC_pow],
    by rw [← pow_succ, sl3TransC_pow]⟩

theorem heisRel_glTrans : HeisRel (glTransA (F := F)) glTransB glTransC where
  ha := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact sl3TransA_pow)
  hb := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact sl3TransB_pow)
  hc := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact sl3TransC_pow)
  ac := Units.ext (by simp only [Units.val_mul]; exact sl3Trans_AC)
  bc := Units.ext (by simp only [Units.val_mul]; exact sl3Trans_BC)
  ab := Units.ext (by simp only [Units.val_mul]; exact sl3Trans_AB)

theorem glTransA_mem : (glTransA : GL (Fin 3) F) ∈ StatedSL 3 F :=
  Subgroup.subset_closure det_sl3TransA

theorem glTransB_mem : (glTransB : GL (Fin 3) F) ∈ StatedSL 3 F :=
  Subgroup.subset_closure det_sl3TransB

theorem glTransC_mem : (glTransC : GL (Fin 3) F) ∈ StatedSL 3 F :=
  Subgroup.subset_closure det_sl3TransC

theorem glTransC_not_mem_statedScalars : (glTransC : GL (Fin 3) F) ∉ StatedScalars (Fin 3) F := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 2) hu
  simp [glTransC, sl3TransC] at h

theorem hasNonabelianFiveSubgroup_statedProj_statedSL_three :
    HasNonabelianFiveSubgroup (StatedProj (StatedSL 3 F)) :=
  hasNonabelianFiveSubgroup_statedProj (StatedSL 3 F) glTransA_mem glTransB_mem glTransC_mem
    heisRel_glTrans glTransC_not_mem_statedScalars

end SL3

theorem hasNonabelianFiveSubgroup_of_classicalModel_PSU_three_five {B : Type} [Group B]
    (hB : StatedClassicalModel B .PSU 3 5 1) : HasNonabelianFiveSubgroup B := by
  obtain ⟨x, y, -, -, -, hx5, hy5, hcx, hcy, hz5, hz1, -⟩ :=
    CFSG.RankThree.PartOne.HNRed.unitary_three_five_heisenberg_data hB
  refine hasNonabelianFiveSubgroup_of_heis (a := y) (b := x) (c := ⁅y, x⁆)
    ⟨hy5, hx5, hz5, hcy.eq.symm, hcx.eq.symm, ?_⟩ hz1
  rw [commutatorElement_def]
  group

theorem classical_five_false {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n f : ℕ}
    (hM : StatedClassicalModel K t n 5 f) (hne : ¬ (t = .PSL ∧ n = 2))
    {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K} (hD : I1434.Data K Q x J₁ J₂) : False := by
  have hf : 1 ≤ f := hM.1.2.1
  cases t
  case PSL =>
    have hn : 2 ≤ n := hM.1.2.2.1
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow hF
    rcases Nat.lt_or_ge n 4 with h4 | h4
    ·
      obtain rfl : n = 3 := by
        have : n ≠ 2 := fun h => hne ⟨rfl, h⟩
        omega
      exact hD.false_of_hasNonabelianFiveSubgroup
        (HasNonabelianFiveSubgroup.of_mulEquiv e.symm
          (hasNonabelianFiveSubgroup_statedProj_statedSL_three (F := F)))
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      refine hD.false_of_classicalModel hM hn e (k := m + 1) ?_ (three_mul_lt_linear m f hf)
      simp only [Fintype.card_fin]
      have := four_mul_add_five_le m
      omega
  case PSU =>
    have hn : 3 ≤ n := hM.1.2.2.1
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow (m := f * 2) (by rw [hF, ← pow_mul])
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · obtain rfl : n = 3 := by omega
      rcases Nat.lt_or_ge f 2 with hf2 | hf2
      ·
        obtain rfl : f = 1 := by omega
        exact hD.false_of_hasNonabelianFiveSubgroup
          (hasNonabelianFiveSubgroup_of_classicalModel_PSU_three_five hM)
      · refine hD.false_of_classicalModel hM hn e (k := 1) (by simp) ?_
        show 3 * 1 < f * ((3 - 1) * 3 / 2)
        omega
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      refine hD.false_of_classicalModel hM hn e (k := m + 1) ?_ (three_mul_lt_linear m f hf)
      simp only [Fintype.card_fin]
      have := four_mul_add_five_le m
      omega
  case PSp =>
    have hn : 2 ≤ n := hM.1.2.2.1
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow hF
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    refine hD.false_of_classicalModel hM hn e (k := m + 1) ?_ ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      have := four_mul_add_five_le m
      omega
    · show 3 * (m + 1) < f * ((m + 2) * (m + 2))
      nlinarith
  case POmegaOdd =>
    have hn : 3 ≤ n := hM.1.2.2.1
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow hF
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    refine hD.false_of_classicalModel hM hn e (k := m + 2) ?_ ?_
    · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      have : 4 * (m + 1) + 5 ≤ 5 ^ (m + 2) := four_mul_add_five_le (m + 1)
      omega
    · show 3 * (m + 2) < f * ((m + 3) * (m + 3))
      nlinarith
  case POmegaPlus =>
    have hn : 4 ≤ n := hM.1.2.2
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow hF
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    refine hD.false_of_classicalModel hM hn e (k := m + 2) ?_ ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      have : 4 * (m + 1) + 5 ≤ 5 ^ (m + 2) := four_mul_add_five_le (m + 1)
      omega
    · show 3 * (m + 2) < f * ((m + 4) * (m + 4 - 1))
      refine lt_mul_of_lt_of_one_le ?_ hf
      rw [show m + 4 - 1 = m + 3 from rfl]
      nlinarith
  case POmegaMinus =>
    have hn : 4 ≤ n := hM.1.2.2
    obtain ⟨F, _, _, hF, b, c, -, ⟨e⟩⟩ := hM.2
    haveI := charP_five_of_card_eq_five_pow hF
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    refine hD.false_of_classicalModel hM hn e (k := m + 2) ?_ ?_
    · simp only [Fintype.card_sum, Fintype.card_fin]
      have : 4 * (m + 1) + 5 ≤ 5 ^ (m + 2) := four_mul_add_five_le (m + 1)
      omega
    · show 3 * (m + 2) < f * ((m + 4) * (m + 4 - 1))
      refine lt_mul_of_lt_of_one_le ?_ hf
      rw [show m + 4 - 1 = m + 3 from rfl]
      nlinarith
  all_goals exact (hM.2 : False).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

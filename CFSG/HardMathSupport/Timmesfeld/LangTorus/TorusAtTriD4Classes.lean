module

public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SLOrder
public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLift
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.PartOne.KGD.D4Weyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

theorem smul_one_four (q : ℤ) : (q • (1 : Matrix (Fin 4) (Fin 4) ℤ)) =
    !![q, 0, 0, 0; 0, q, 0, 0; 0, 0, q, 0; 0, 0, 0, q] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def d4PermList : List (List ℤ) := [[0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0], [1, 0, 0, 0]]

theorem toMat_d4PermList : toMat 4 d4PermList =
    Matrix.of (fun i j => if j = TwistTag.D4.perm i then (1 : ℤ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem permLattice_D4_symm_eq (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm.symm x = toMat 4 d4PermList *ᵥ x := by
  rw [toMat_d4PermList]
  funext i
  change x (TwistTag.D4.perm.symm.symm i) =
    ∑ j : Fin TwistTag.D4.tag.rank, (if j = TwistTag.D4.perm i then (1 : ℤ) else 0) * x j
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

theorem hw_of_word {word : List (Fin Tag.D4.rank)} {Wl : List (List ℤ)}
    {M : Matrix (Fin 4) (Fin 4) ℤ} (hW : wordMat Tag.D4 word = toMat 4 Wl)
    (hMQ : M * toMat 4 d4PermList = toMat 4 Wl) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd word) • x =
      M *ᵥ permLattice TwistTag.D4.perm.symm x := by
  have h1 := wordProd_smul_eq_wordMat_mulVec Tag.D4 word x
  rw [hW] at h1
  refine h1.trans ?_
  rw [permLattice_D4_symm_eq]
  have h2 := Matrix.mulVec_mulVec x M (toMat 4 d4PermList)
  exact (congrArg (fun A => A *ᵥ x) hMQ).symm.trans h2.symm

@[expose] def d4OneWord : List (Fin Tag.D4.rank) := []

@[expose] def d4OneM : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]

theorem d4One_wordMat : wordMat Tag.D4 d4OneWord = toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] :=
  wordMat_eq_toMat Tag.D4 _ (by decide +kernel)

theorem d4One_MQ : d4OneM * toMat 4 d4PermList = toMat 4 [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem d4One_pow : d4OneM ^ 3 = 1 := by decide +kernel

theorem d4One_det (q : ℤ) :
    (d4OneM - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det =
      ((cyclotomic 1 ℤ) ^ 2 * (cyclotomic 3 ℤ)).eval q := by
  rw [smul_one_four]
  simp [d4OneM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cyclotomic_one,
    cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq]
  ring

theorem d4One_hw (x : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord) • x =
      d4OneM *ᵥ permLattice TwistTag.D4.perm.symm x :=
  hw_of_word d4One_wordMat d4One_MQ x

@[expose] def d4TwoWord : List (Fin Tag.D4.rank) := [2, 1, 0, 2, 1, 0]

@[expose] def d4TwoM : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 1, 0, 0; 0, 1, 0, -1; 0, 2, -1, 0; 0, 1, 0, 0]

theorem d4Two_wordMat : wordMat Tag.D4 d4TwoWord = toMat 4 [[0, -1, 0, 1], [-1, 0, 0, 1], [0, 0, -1, 2], [0, 0, 0, 1]] :=
  wordMat_eq_toMat Tag.D4 _ (by decide +kernel)

theorem d4Two_MQ : d4TwoM * toMat 4 d4PermList = toMat 4 [[0, -1, 0, 1], [-1, 0, 0, 1], [0, 0, -1, 2], [0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem d4Two_pow : d4TwoM ^ 6 = 1 := by decide +kernel

theorem d4Two_det (q : ℤ) :
    (d4TwoM - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det =
      ((cyclotomic 2 ℤ) ^ 2 * (cyclotomic 6 ℤ)).eval q := by
  rw [smul_one_four]
  simp [d4TwoM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cyclotomic_one,
    cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq]
  ring

theorem d4Two_hw (x : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord) • x =
      d4TwoM *ᵥ permLattice TwistTag.D4.perm.symm x :=
  hw_of_word d4Two_wordMat d4Two_MQ x

@[expose] def d4ThreeWord : List (Fin Tag.D4.rank) := [1, 2, 3, 1, 0, 2, 1, 0]

@[expose] def d4ThreeM : Matrix (Fin 4) (Fin 4) ℤ := !![-1, 1, 0, 0; -1, 0, 0, 0; -1, 1, 0, -1; -1, 0, 1, -1]

theorem d4Three_wordMat : wordMat Tag.D4 d4ThreeWord = toMat 4 [[0, -1, 0, 1], [0, -1, 0, 0], [-1, -1, 0, 1], [-1, -1, 1, 0]] :=
  wordMat_eq_toMat Tag.D4 _ (by decide +kernel)

theorem d4Three_MQ : d4ThreeM * toMat 4 d4PermList = toMat 4 [[0, -1, 0, 1], [0, -1, 0, 0], [-1, -1, 0, 1], [-1, -1, 1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem d4Three_pow : d4ThreeM ^ 3 = 1 := by decide +kernel

theorem d4Three_det (q : ℤ) :
    (d4ThreeM - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det =
      ((cyclotomic 3 ℤ) ^ 2 * (1)).eval q := by
  rw [smul_one_four]
  simp [d4ThreeM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cyclotomic_one,
    cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq]
  ring

theorem d4Three_hw (x : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd d4ThreeWord) • x =
      d4ThreeM *ᵥ permLattice TwistTag.D4.perm.symm x :=
  hw_of_word d4Three_wordMat d4Three_MQ x

@[expose] def d4SixWord : List (Fin Tag.D4.rank) := [1, 2, 1, 0]

@[expose] def d4SixM : Matrix (Fin 4) (Fin 4) ℤ := !![0, 0, 1, -1; 0, 1, 0, -1; -1, 1, 1, -1; 0, 1, 0, 0]

theorem d4Six_wordMat : wordMat Tag.D4 d4SixWord = toMat 4 [[-1, 0, 1, 0], [-1, 0, 0, 1], [-1, -1, 1, 1], [0, 0, 0, 1]] :=
  wordMat_eq_toMat Tag.D4 _ (by decide +kernel)

theorem d4Six_MQ : d4SixM * toMat 4 d4PermList = toMat 4 [[-1, 0, 1, 0], [-1, 0, 0, 1], [-1, -1, 1, 1], [0, 0, 0, 1]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem d4Six_pow : d4SixM ^ 6 = 1 := by decide +kernel

theorem d4Six_det (q : ℤ) :
    (d4SixM - q • (1 : Matrix (Fin 4) (Fin 4) ℤ)).det =
      ((cyclotomic 6 ℤ) ^ 2 * (1)).eval q := by
  rw [smul_one_four]
  simp [d4SixM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, cyclotomic_one,
    cyclotomic_two, cyclotomic_three_eq, cyclotomic_six_eq]
  ring

theorem d4Six_hw (x : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd d4SixWord) • x =
      d4SixM *ᵥ permLattice TwistTag.D4.perm.symm x :=
  hw_of_word d4Six_wordMat d4Six_MQ x

theorem not_dvd_one_int {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := fun h =>
  hp.one_lt.ne' (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by exact_mod_cast h)))

theorem card_cat_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) =
      ordTrialityD4 (q.p ^ q.exponent) := by
  have hm := chevalleyModel_cat_trialityD4 hv
  by_cases h2 : q.p = 2
  · rw [h2] at hm ⊢
    exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  · exact CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two h2 hm

end CFSG.HardMathSupport.Timmesfeld.LangTorus

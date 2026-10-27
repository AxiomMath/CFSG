module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowWeyl
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Native.DerivedGenerators
public import CFSG.RankThree.PartOne.KE8F.Stab5Fix

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

set_option linter.unusedSectionVars false


section Words

@[expose] def g1Word : List (Fin Tag.E8.rank) := [0, 2, 3, 1]

@[expose] def g2Word : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4,
    3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4]

@[expose] def xWord : ℕ → List (Fin Tag.E8.rank)
  | 2 => [0, 3, 2]
  | 3 => [2, 0, 3]
  | 4 => [0, 2, 0, 1]
  | _ => []

theorem g1_eq : e8FiveG1 = (coxeterSystem Tag.E8).wordProd g1Word := rfl

theorem g2_eq : e8FiveG2 = (coxeterSystem Tag.E8).wordProd g2Word := rfl

theorem weylMatrix_g1 : weylMatrix e8FiveG1 = wordMat Tag.E8 g1Word := by
  rw [g1_eq]
  exact Four.weylMatrix_wordProd_E8 g1Word

theorem weylMatrix_g2 : weylMatrix e8FiveG2 = wordMat Tag.E8 g2Word := by
  rw [g2_eq]
  exact Four.weylMatrix_wordProd_E8 g2Word

end Words

section Griess

theorem wordMat_griessW :
    wordMat Tag.E8 griessWWord = wordMat Tag.E8 g1Word ^ 4 * wordMat Tag.E8 g2Word := by
  decide +kernel

theorem griessW_eq : griessW = e8FiveG1 ^ 4 * e8FiveG2 := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_pow, weylMatrix_g1, weylMatrix_g2]
  exact (Four.weylMatrix_wordProd_E8 griessWWord).trans wordMat_griessW

end Griess

section Conj

@[expose] def xElt (a : ℕ) : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd (xWord a)

theorem xElt_mul_g1 {a : ℕ} (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) :
    xElt a * e8FiveG1 = e8FiveG1 ^ a * xElt a := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_mul, weylMatrix_pow, weylMatrix_g1, xElt,
    Four.weylMatrix_wordProd_E8]
  rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

theorem xElt_mul_g2 {a : ℕ} (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) :
    xElt a * e8FiveG2 = e8FiveG2 * xElt a := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_mul, weylMatrix_g2, xElt, Four.weylMatrix_wordProd_E8]
  rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

theorem xElt_mul_g1_pow {a : ℕ} (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) (i : ℕ) :
    xElt a * e8FiveG1 ^ i = e8FiveG1 ^ (a * i) * xElt a := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, xElt_mul_g1 ha, ← mul_assoc, ← pow_add,
      show a * (i + 1) = a * i + a by ring]

theorem xElt_mul_g2_pow {a : ℕ} (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) (j : ℕ) :
    xElt a * e8FiveG2 ^ j = e8FiveG2 ^ j * xElt a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, xElt_mul_g2 ha, ← mul_assoc]

theorem xElt_conj {a : ℕ} (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) (i j : ℕ) :
    xElt a * (e8FiveG1 ^ i * e8FiveG2 ^ j) * (xElt a)⁻¹ = e8FiveG1 ^ (a * i) * e8FiveG2 ^ j := by
  rw [mul_inv_eq_iff_eq_mul, ← mul_assoc, xElt_mul_g1_pow ha, mul_assoc, xElt_mul_g2_pow ha,
    ← mul_assoc]

theorem exists_conj_griessW_pow {i j : ℕ} (hi : ¬ 5 ∣ i) (hj : ¬ 5 ∣ j) :
    ∃ a : ℕ, (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) ∧
      xElt a * (e8FiveG1 ^ i * e8FiveG2 ^ j) * (xElt a)⁻¹ = griessW ^ j := by
  have key : ∀ i' j' : Fin 5, i' ≠ 0 → j' ≠ 0 → ∃ a : Fin 5, a ≠ 0 ∧
      (a.val * (i' : ℕ)) % 5 = (4 * (j' : ℕ)) % 5 := by decide
  obtain ⟨a, ha0, hmod⟩ := key ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
    ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩
    (fun h => hi (Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)))
    (fun h => hj (Nat.dvd_of_mod_eq_zero (congrArg Fin.val h)))
  have ha : a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 := by
    have := a.isLt
    have h0 : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
    omega
  refine ⟨a.val, ha, ?_⟩
  rw [xElt_conj ha, griessW_eq]
  have hc0 : Commute e8FiveG1 e8FiveG2 := e8Five_comm
  have hc : Commute (e8FiveG1 ^ 4) e8FiveG2 := hc0.pow_left 4
  rw [hc.mul_pow, ← pow_mul]
  have e1 : (a.val * i) % 5 = (a.val * (i % 5)) % 5 := (Nat.mul_mod_mod a.val i 5).symm
  have e2 : (4 * j) % 5 = (4 * (j % 5)) % 5 := (Nat.mul_mod_mod 4 j 5).symm
  have hmain : (a.val * i) % 5 = (4 * j) % 5 := by
    rw [e1, e2]
    exact hmod
  rw [pow_eq_pow_mod (a.val * i) e8FiveG1_pow, pow_eq_pow_mod (4 * j) e8FiveG1_pow, hmain]

end Conj

section Fixed

theorem g1_pow_smul_single7 (n : ℕ) :
    e8FiveG1 ^ n • (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = Pi.single 7 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, g1_eq, wordProd_smul_eq_wordMat_mulVec]
    have : wordMat Tag.E8 g1Word *ᵥ (Pi.single 7 1 : Fin Tag.E8.rank → ℤ) = Pi.single 7 1 := by
      decide +kernel
    rw [this, ← g1_eq, ih]

theorem g2_pow_smul_single0 (n : ℕ) :
    e8FiveG2 ^ n • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = Pi.single 0 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, g2_eq, wordProd_smul_eq_wordMat_mulVec]
    have : wordMat Tag.E8 g2Word *ᵥ (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) = Pi.single 0 1 := by
      decide +kernel
    rw [this, ← g2_eq, ih]

end Fixed

section AFrame

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

theorem sigmaA_01 : sigmaRootE8A4 e8VA 0 1 = e8VA • (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) := by
  rw [sigmaRootE8A4_eq_smul]
  congr 1
  decide +kernel

theorem sigmaA_12 : sigmaRootE8A4 e8VA 1 2 = e8VA • (Pi.single 2 1 : Fin Tag.E8.rank → ℤ) := by
  rw [sigmaRootE8A4_eq_smul]
  congr 1
  decide +kernel

theorem sigmaA_23 : sigmaRootE8A4 e8VA 2 3 = e8VA • (Pi.single 3 1 : Fin Tag.E8.rank → ℤ) := by
  rw [sigmaRootE8A4_eq_smul]
  congr 1
  decide +kernel

theorem sigmaA_34 : sigmaRootE8A4 e8VA 3 4 = e8VA • (Pi.single 4 1 : Fin Tag.E8.rank → ℤ) := by
  rw [sigmaRootE8A4_eq_smul]
  congr 1
  decide +kernel

theorem e8VA_cox : e8VA * ((coxeterSystem Tag.E8).wordProd [0, 2, 3, 4]) =
    e8FiveG1 ^ 4 * e8VA := by
  apply weylMatrix_injective
  rw [weylMatrix_mul, weylMatrix_mul, weylMatrix_pow, weylMatrix_g1, e8VA,
    Four.weylMatrix_wordProd_E8, Four.weylMatrix_wordProd_E8]
  decide +kernel

theorem coxA_eq :
    rootReflection (sigmaRootE8A4 e8VA 0 1) * rootReflection (sigmaRootE8A4 e8VA 1 2) *
      rootReflection (sigmaRootE8A4 e8VA 2 3) * rootReflection (sigmaRootE8A4 e8VA 3 4) =
      e8FiveG1 ^ 4 := by
  rw [rootReflection_eq_conj sigmaA_01.symm, rootReflection_eq_conj sigmaA_12.symm,
    rootReflection_eq_conj sigmaA_23.symm, rootReflection_eq_conj sigmaA_34.symm]
  have h : e8VA * ((coxeterSystem Tag.E8).wordProd [0, 2, 3, 4]) * e8VA⁻¹ = e8FiveG1 ^ 4 := by
    rw [mul_inv_eq_iff_eq_mul, e8VA_cox]
  rw [← h]
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one]
  group

end AFrame

section FixedColumns

@[expose] def czCol : Fin Tag.E8.rank → ZMod 5 := fun i => (czVec i : ZMod 5)

@[expose] def cxCol : Fin Tag.E8.rank → ZMod 5 := fun i => (cxVec i : ZMod 5)

theorem mem_dualWeylStabilizer_of_dualMatrix {z : Fin Tag.E8.rank → ZMod 5} {w : WeylGroup Tag.E8}
    (h : (dualMatrix (ZMod 5) w).mulVec z = z) : w ∈ dualWeylStabilizer z := by
  intro x
  rw [← charVal_dualMatrix, h]

theorem griessW_pow_four : griessW ^ 4 = e8FiveH 4 := by
  have hc0 : Commute e8FiveG1 e8FiveG2 := e8Five_comm
  rw [griessW_eq, e8FiveH, (hc0.pow_left 4).mul_pow, ← pow_mul,
    show 4 * 4 = 5 * 3 + 1 by norm_num, pow_add, pow_mul, e8FiveG1_pow, one_pow, one_mul, pow_one]

theorem fixSet_griessW_subset : fixSet griessW ⊆ fixSet (e8FiveH 4) := fun z hz => by
  have h : griessW ^ 4 ∈ dualWeylStabilizer z := pow_mem hz 4
  rwa [griessW_pow_four] at h

theorem ncard_fixSet_griessW_le : (fixSet griessW).ncard ≤ 25 :=
  (Set.ncard_le_ncard fixSet_griessW_subset (Set.toFinite _)).trans
    (ncard_fixSet_le_of_param (fun z hz => fixSet_h4_param hz))

theorem czCol_mem_fixSet : czCol ∈ fixSet griessW := by
  apply mem_dualWeylStabilizer_of_dualMatrix
  rw [dualMatrix, griessW, Four.weylMatrix_wordProd_E8]
  decide +kernel

theorem cxCol_mem_fixSet : cxCol ∈ fixSet griessW := by
  apply mem_dualWeylStabilizer_of_dualMatrix
  rw [dualMatrix, griessW, Four.weylMatrix_wordProd_E8]
  decide +kernel

end FixedColumns

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

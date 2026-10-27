module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZPlane
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Weyl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Weyl

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TableBExc

open scoped Matrix

@[expose] def moveWord : List (Fin Tag.E7.rank) :=
  [2, 3, 4, 5, 3, 0, 2, 1, 3, 4, 3, 0, 2]

@[expose] def scalarCochar : Fin Tag.E7.rank → ℤ := ![0, 1, 0, 2, 0, 1, 2]

@[expose] def pairedCochar : Fin Tag.E7.rank → ℤ := ![1, 0, 0, 1, 0, 0, 1]

@[expose] def multiplicityCochar : Fin Tag.E7.rank → ℤ := ![0, 1, 0, 2, 3, 2, 1]

open CFSG.RankThree.E6

@[expose] noncomputable def move : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd moveWord

@[expose] noncomputable def gamma : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd [1, 3, 5, 6] *
    (rootReflection (kacE7.extRoot none) * (coxeterSystem .E7).wordProd [0]) ^ 2

@[expose] def moveMat : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  ![![0, 1, 0, 0, -1, 1, 0], ![1, 0, -1, 1, -1, 1, 0],
    ![1, 1, -1, 1, -2, 1, 1], ![1, 1, -2, 2, -2, 1, 1],
    ![1, 1, -2, 1, -1, 1, 1], ![1, 1, -1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1]]

@[expose] def gammaMat : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  ![![-2, 0, 1, 0, 0, 0, 0], ![-2, 0, 1, -1, 1, 0, 0],
    ![-3, 0, 1, 0, 0, 0, 0], ![-4, 1, 1, -1, 1, 0, 0],
    ![-3, 0, 0, 0, 1, 0, 0], ![-2, 0, 0, 0, 1, 0, -1],
    ![-1, 0, 0, 0, 0, 1, -1]]

theorem weylMatrix_move : weylMatrix move = moveMat := by
  apply Matrix.ext
  intro i j
  rw [weylMatrix_apply, move, CFSG.StandardType.TableBExc.wordProd_smul]
  fin_cases i <;> fin_cases j <;> rfl

theorem weylMatrix_gamma : weylMatrix gamma = gammaMat := by
  apply Matrix.ext
  intro i j
  rw [weylMatrix_apply]
  simp only [gamma, pow_two, mul_smul, CFSG.StandardType.TableBExc.wordProd_smul,
    rootReflection_smul (kacE7.isRoot_extRoot none)]
  rw [kacE7_extRoot]
  fin_cases i <;> fin_cases j <;> rfl

theorem gamma_pow_three : gamma ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_gamma, weylMatrix_one]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem gamma_ne_one : gamma ≠ 1 := by
  intro h
  have e := congrArg (fun w : WeylGroup .E7 => weylMatrix w 0 0) h
  rw [weylMatrix_gamma, weylMatrix_one] at e
  norm_num [gammaMat] at e

theorem orderOf_gamma : orderOf gamma = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime_iff.mpr ⟨gamma_pow_three, gamma_ne_one⟩

theorem move_pow_two : move ^ 2 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_move, weylMatrix_one]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem move_gamma_move : move * gamma * move = gamma ^ 2 := by
  refine ext_single fun j => ?_
  simp only [mul_smul, pow_two]
  simp only [← weylMatrix_mulVec, weylMatrix_move, weylMatrix_gamma]
  funext i
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem move_gamma_conj : move * gamma * move⁻¹ = gamma ^ 2 := by
  have hinv : move⁻¹ = move := by
    calc
      move⁻¹ = move⁻¹ * (move * move) := by rw [← pow_two, move_pow_two, mul_one]
      _ = move := by group
  simpa only [hinv] using move_gamma_move

theorem move_inv : move⁻¹ = move := by
  calc
    move⁻¹ = move⁻¹ * (move * move) := by rw [← pow_two, move_pow_two, mul_one]
    _ = move := by group

theorem gamma_inv : gamma⁻¹ = gamma ^ 2 := by
  calc
    gamma⁻¹ = gamma⁻¹ * gamma ^ 3 := by rw [gamma_pow_three, mul_one]
    _ = gamma ^ 2 := by group

@[expose] def a5CycleWord : List (Fin Tag.E7.rank) := [1, 3, 5, 6]

@[expose] noncomputable def a5Cycle : WeylGroup .E7 :=
  (coxeterSystem .E7).wordProd a5CycleWord

@[expose] def a5CycleMat : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, -1, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 1, 1, -1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0, -1],
    ![0, 0, 0, 0, 0, 1, -1]]

theorem weylMatrix_a5Cycle : weylMatrix a5Cycle = a5CycleMat := by
  apply Matrix.ext
  intro i j
  rw [weylMatrix_apply, a5Cycle, CFSG.StandardType.TableBExc.wordProd_smul]
  fin_cases i <;> fin_cases j <;> rfl

theorem a5Cycle_pow_three : a5Cycle ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_a5Cycle, weylMatrix_one]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem a5Cycle_gamma_commute : a5Cycle * gamma = gamma * a5Cycle := by
  refine ext_single fun j => ?_
  simp only [mul_smul, ← weylMatrix_mulVec, weylMatrix_a5Cycle, weylMatrix_gamma]
  funext i
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem a5Cycle_inv : a5Cycle⁻¹ = a5Cycle ^ 2 := by
  calc
    a5Cycle⁻¹ = a5Cycle⁻¹ * a5Cycle ^ 3 := by rw [a5Cycle_pow_three, mul_one]
    _ = a5Cycle ^ 2 := by group

section Field

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

@[expose] def cubeChar (ζ : Kˣ) (a : Fin Tag.E7.rank → ℤ) : Fin Tag.E7.rank → Kˣ :=
  fun i => ζ ^ a i

theorem cubeChar_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (a : Fin Tag.E7.rank → ℤ) : cubeChar ζ a ^ 3 = 1 := by
  funext i
  change (ζ ^ a i) ^ 3 = 1
  rw [← zpow_natCast, zpow_comm, zpow_natCast, hζ, _root_.one_zpow]

@[expose] def scalarExp : Fin Tag.E7.rank → ℤ := ![0, 0, 1, 0, 0, 0, 0]
@[expose] def pairedExp : Fin Tag.E7.rank → ℤ := ![2, 2, 1, 2, 2, 2, 2]
@[expose] def multiplicityExp : Fin Tag.E7.rank → ℤ := ![0, 0, 1, 0, 2, 0, 0]

theorem weylTuple_cubeChar_of_mod (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (w : WeylGroup .E7) (a b : Fin Tag.E7.rank → ℤ)
    (h : ∀ j, (∑ i, (w⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) i * a i) % 3 = b j % 3) :
    weylTuple w (cubeChar ζ a) = cubeChar ζ b := by
  funext j
  change rootChar (fun i => ζ ^ a i) (w⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) = ζ ^ b j
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootChar_zpow_tuple (τ := .E7) ζ a
    (w⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ))]
  calc
    ζ ^ (∑ i, (w⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) i * a i) =
        ζ ^ ((∑ i, (w⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) i * a i) % 3) :=
      zpow_eq_zpow_emod' _ hζ
    _ = ζ ^ (b j % 3) := by rw [h j]
    _ = ζ ^ b j := (zpow_eq_zpow_emod' _ hζ).symm

theorem weylTuple_move_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple move (cubeChar ζ scalarExp) = cubeChar ζ (-pairedExp) := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [move_inv, ← weylMatrix_apply, weylMatrix_move]
  fin_cases j <;> decide +kernel

theorem weylTuple_move_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple move (cubeChar ζ pairedExp) = cubeChar ζ (-scalarExp) := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [move_inv, ← weylMatrix_apply, weylMatrix_move]
  fin_cases j <;> decide +kernel

theorem weylTuple_move_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple move (cubeChar ζ multiplicityExp) = cubeChar ζ multiplicityExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [move_inv, ← weylMatrix_apply, weylMatrix_move]
  fin_cases j <;> decide +kernel

theorem weylTuple_gamma_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple gamma (cubeChar ζ scalarExp) = cubeChar ζ scalarExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [gamma_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_gamma]
  fin_cases j <;> decide +kernel

theorem weylTuple_gamma_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple gamma (cubeChar ζ pairedExp) = cubeChar ζ pairedExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [gamma_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_gamma]
  fin_cases j <;> decide +kernel

theorem weylTuple_gamma_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple gamma (cubeChar ζ multiplicityExp) = cubeChar ζ multiplicityExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [gamma_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_gamma]
  fin_cases j <;> decide +kernel

theorem weylTuple_a5Cycle_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple a5Cycle (cubeChar ζ scalarExp) = cubeChar ζ scalarExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [a5Cycle_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_a5Cycle]
  fin_cases j <;> decide +kernel

theorem weylTuple_a5Cycle_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple a5Cycle (cubeChar ζ pairedExp) = cubeChar ζ (fun i => pairedExp i + 2 * scalarExp i) := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [a5Cycle_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_a5Cycle]
  fin_cases j <;> decide +kernel

theorem weylTuple_a5Cycle_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    weylTuple a5Cycle (cubeChar ζ multiplicityExp) = cubeChar ζ multiplicityExp := by
  apply weylTuple_cubeChar_of_mod ζ hζ
  intro j
  simp only [a5Cycle_inv, ← weylMatrix_apply, weylMatrix_pow, weylMatrix_a5Cycle]
  fin_cases j <;> decide +kernel

theorem move_conj_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ scalarExp) *
      (canonicalRep (coxeterSystem .E7) K move)⁻¹ = rootDiagUnit .E7 (cubeChar ζ (-pairedExp)) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_move_scalar ζ hζ]

theorem move_conj_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ pairedExp) *
      (canonicalRep (coxeterSystem .E7) K move)⁻¹ = rootDiagUnit .E7 (cubeChar ζ (-scalarExp)) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_move_paired ζ hζ]

theorem move_conj_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) *
      (canonicalRep (coxeterSystem .E7) K move)⁻¹ = rootDiagUnit .E7 (cubeChar ζ multiplicityExp) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_move_multiplicity ζ hζ]

theorem gamma_conj_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ scalarExp) *
      (canonicalRep (coxeterSystem .E7) K gamma)⁻¹ = rootDiagUnit .E7 (cubeChar ζ scalarExp) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_gamma_scalar ζ hζ]

theorem gamma_conj_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ pairedExp) *
      (canonicalRep (coxeterSystem .E7) K gamma)⁻¹ = rootDiagUnit .E7 (cubeChar ζ pairedExp) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_gamma_paired ζ hζ]

theorem gamma_conj_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ multiplicityExp) *
      (canonicalRep (coxeterSystem .E7) K gamma)⁻¹ = rootDiagUnit .E7 (cubeChar ζ multiplicityExp) := by
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_gamma_multiplicity ζ hζ]

section CharTwo

variable [CharP K 2]

theorem nrep_gamma_pow_three : (CFSG.SectionRank.LargeRee.nrepHom .E7 K gamma) ^ 3 = 1 := by
  rw [← map_pow, gamma_pow_three, map_one]

theorem nrep_move_pow_two : (CFSG.SectionRank.LargeRee.nrepHom .E7 K move) ^ 2 = 1 := by
  rw [← map_pow, move_pow_two, map_one]

theorem nrep_move_gamma_conj :
    CFSG.SectionRank.LargeRee.nrepHom .E7 K move * CFSG.SectionRank.LargeRee.nrepHom .E7 K gamma *
      (CFSG.SectionRank.LargeRee.nrepHom .E7 K move)⁻¹ =
      (CFSG.SectionRank.LargeRee.nrepHom .E7 K gamma) ^ 2 := by
  have h := congrArg (CFSG.SectionRank.LargeRee.nrepHom .E7 K) move_gamma_conj
  simpa only [map_mul, map_inv, map_pow] using h

end CharTwo

end Field

end CFSG.LieType.Chevalley.E7Three.Weyl

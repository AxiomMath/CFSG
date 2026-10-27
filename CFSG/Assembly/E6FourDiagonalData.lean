module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDefs
public import CFSG.Assembly.E6FourCentChecker
public import CFSG.Assembly.E6FourCentMask

public section

namespace CFSG.Assembly.E6FourDiagonal

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration CFSG.Assembly.E6FourCentChk
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.N2E6Native
open scoped Matrix

@[expose] def toGammaWord : List (Fin Tag.E6.rank) := [1, 3, 4, 5, 2, 0]

theorem toGamma_conj_matrix :
    wordMat Tag.E6 toGammaWord * wordMat Tag.E6 e6TwoWord *
      wordMat Tag.E6 toGammaWord.reverse = e6NativeWMat := by
  decide +kernel

@[expose] def tableAxisWeight (i : Fin 4) : Fin Tag.E6.rank → ZMod 5 :=
  (![![4, 0, 2, 4, 0, 0], ![0, 2, 0, 4, 0, 0],
    ![0, 0, 0, 4, 2, 4], ![4, 0, 0, 1, 0, 4]] : Fin 4 → Fin Tag.E6.rank → ZMod 5) i

theorem tableAxisWeight_eq (i : Fin 4) :
    tableAxisWeight i = fun k => ∑ j : Fin Tag.E6.rank,
      ((wordMat Tag.E6 toGammaWord j k : ℤ) : ZMod 5) * (e6NativeChar (Pi.single i 1) j : ZMod 5) := by
  fin_cases i <;> decide +kernel

@[expose] def tablePairWeight (i j : Fin 4) (negative : Bool) :
    Fin Tag.E6.rank → ZMod 5 :=
  tableAxisWeight i + if negative then -tableAxisWeight j else tableAxisWeight j

theorem pair_table_check : ∀ i j : Fin 4, i ≠ j → ∀ negative : Bool,
    let v := tablePairWeight i j negative
    let c := e6SolMask v
    E6FourIsSol v ∧ v ≠ 0 ∧ popc c = 24 ∧ typedOK c c = true ∧
      closedOK adjLit c c = true ∧ compOf adjLit c c.log2 = c ∧ c ≠ 0 ∧
        mapMaskP permLit 72 c 0 = c := by
  unfold E6FourIsSol
  decide +kernel

theorem axis_table_check : ∀ i : Fin 4,
    let v := tableAxisWeight i
    let c := e6SolMask v
    E6FourIsSol v ∧ v ≠ 0 ∧ popc c = 30 ∧ typedOK c c = true ∧
      closedOK adjLit c c = true ∧ compOf adjLit c c.log2 = c ∧ c ≠ 0 ∧
        mapMaskP permLit 72 c 0 = c := by
  unfold E6FourIsSol
  decide +kernel

end CFSG.Assembly.E6FourDiagonal

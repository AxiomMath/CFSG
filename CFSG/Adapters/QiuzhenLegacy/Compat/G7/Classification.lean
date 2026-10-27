module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.GorensteinWalter

universe u

theorem hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic
    {G : Type u} [Group G] [Finite G]
    (hSylow : HasCyclicOrDihedralSylowTwo G)
    (hnotcyc : ¬ ∀ S : Sylow 2 G, IsCyclic S) :
    HasDihedralSylowTwo G := by
  push Not at hnotcyc
  rcases hnotcyc with ⟨S, hSnot⟩
  have hSdihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* DihedralGroup (2 ^ m)) :=
    (hSylow S).resolve_left hSnot
  rcases hSdihedral with ⟨m, hm, ⟨eS⟩⟩
  intro T
  refine ⟨m, hm, ⟨(Sylow.equiv S T).symm.trans eS⟩⟩

end CFSG.GorensteinWalter

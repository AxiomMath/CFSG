module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Swap

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem spGlobal_le_iSup_neighbourCore (hn : 3 ≤ n) (e : L ≃* StatedSp n K) :
    spGlobal e ≤ ⨆ k : Fin n, neighbourCore e k := by
  refine iSup_le fun j => ?_
  obtain ⟨k, hk, -⟩ := exists_ne_ne_of_three_le hn j ⟨(j.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  by_cases h : j.val + 1 < n
  · obtain ⟨k, hkj, hkj1⟩ := exists_ne_ne_of_three_le hn j ⟨j.val + 1, h⟩
    refine (pieceCore_le_neighbourCore e (k := k) ?_).trans (le_iSup _ k)
    rw [mem_spSupport]
    rintro (hkJ | ⟨j', hj', hj'k⟩)
    · exact hkj (Finset.mem_singleton.1 hkJ)
    · rw [Finset.mem_singleton.1 hj'] at hj'k
      exact hkj1 (Fin.ext hj'k.symm)
  · refine (pieceCore_le_neighbourCore e (k := k) ?_).trans (le_iSup _ k)
    rw [mem_spSupport]
    rintro (hkJ | ⟨j', hj', hj'k⟩)
    · exact hk (Finset.mem_singleton.1 hkJ)
    · rw [Finset.mem_singleton.1 hj'] at hj'k
      exact h (hj'k ▸ k.isLt)

end Swap

end CFSG.SeitzReduction.SymplecticPilot

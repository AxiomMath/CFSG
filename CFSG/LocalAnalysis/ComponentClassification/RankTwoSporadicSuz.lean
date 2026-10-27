module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuzTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Suz

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem suzInM_iff (a : Array ℕ)
    (g : Equiv.Perm (Fin 1782)) (h : Rep 1782 a g) : suzInM a = true ↔ g ∈ suzM :=
  mem_suzM_iff_siftA h

theorem suzAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Suz) ↥suzT (suzM.subgroupOf suzT) :=
  autModel_of_conj suzM_le_suzT suzEquivM.symm (MulEquiv.ofBijective suzConjT suzConjT_bijective)
    fun x p => suzConjT_apply x p

@[expose] noncomputable def suzE0Sub : Subgroup (Equiv.Perm (Fin 1782)) :=
  closure (permsA 1782 suzE0)

end CFSG.ComponentClassification.RankTwoSporadic.Suz

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuTests
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem ruInP_iff
    (a : Array ℕ) (g : Equiv.Perm (Fin 4060)) (h : Rep 4060 a g) :
    ruInP a = true ↔ g ∈ ruP := by
  rw [ruP_eq_sup, ← ruChainJoin_sub]
  exact ruChain_sift ruChainJoin_check.1 h

theorem ru_normal : (ruP.subgroupOf ruP).Normal := by
  rw [subgroupOf_self]
  infer_instance

theorem ruAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .Ru) ↥ruP (ruP.subgroupOf ruP) :=
  autModel_of_allInner ruEquivP.symm center_ruP mulAut_inner

@[expose] noncomputable def ruE0Sub : Subgroup (Equiv.Perm (Fin 4060)) :=
  closure (permsA 4060 ruE0)

end CFSG.ComponentClassification.RankTwoSporadic.Ru

module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21Rel

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit

variable {G : Type} [Group G] [Finite G]

theorem exists_gsWeakCorr {a b : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ coreActionKernel J) :
    ∃ K : Subgroup G, GSWeakCorr a J b K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJsub, -, hJq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).1 hJ
  have hTp := gsFixedLayer_isPComponent hJa hJsub
    (mem_centralizer_singleton_iff.mpr hab.symm) hb (mem_coreActionKernel.mp hbJ).1
    hJq (mem_coreActionKernel.mp hbJ).2
  have hTC : gsFixedLayer J b ≤ centralizer ({b} : Set G) ⊓ centralizer ({a} : Set G) :=
    le_inf ((gsFixedLayer_le_inf J b).trans inf_le_right)
      ((gsFixedLayer_le_inf J b).trans (inf_le_left.trans hJa))
  rw [inf_comm] at hTp
  obtain ⟨K, hKb, hK, hTK, -⟩ := FooteLit.foote_lemma_2_1_iv_subgroup
    (mem_centralizer_singleton_iff.mpr hab) ha hTC hTp
  exact ⟨K, ha, hb, hab, hJa, hJ, hKb, hK,
    (mem_coreActionKernel.mp hbJ).1, (mem_coreActionKernel.mp hbJ).2, hTK⟩

end CFSG.ComponentClassification.GrSLit

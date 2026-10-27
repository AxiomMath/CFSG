module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalOS2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Kappa
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82FinalOS9

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

structure Lemma82InputsK : Prop where
  b1 : ConjFixStatement
  b6 : SylowKernelStatement
  cf23 : CFProp23Fusion
  cf24 : CFProp24c
  cfc : CFProp23Center
  cfi : CFProp23IndexReduced
  schreier : SchreierFor Blueprint.Catalog
  l81 : Lemma81StatementK
  inner : CF82Inner
  prop29 : CF82Prop29Corr
  caseA10 : GS82CaseA10Input
  caseAL4U4 : GS82CaseAL4U4Input
  sy : CFL2Sylow
  c : CFL2C
  j : CFL2J
  rk : CFL2Rank
  jo : CFSec8JOrder
  comm : CF82L2Comm
  cyc : CF82L2Cyc
  az : CF82AZ
  a10p : CF82A10P
  nine : CF82L2NineAbelian
  l2a : CFL2A
  nfw : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW
  cover : CF82Cover

theorem lemma82_K (I : Lemma82InputsK) : Lemma82Statement := by
  intro X _ _ h hset
  by_contra hP
  obtain ⟨s0, -, -⟩ :=
    Eight2.exists_setting0_of_schreier I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cfi I.schreier hset hP
  obtain ⟨s1, -⟩ := s0.exists_setting1 I.l81
    (s0.kappaAt_of_cover I.l81 I.inner I.cover (I.nfw X s0.h s0.nf58))
  obtain ⟨s2, -⟩ := s1.exists_setting2 I.b1 I.b6 I.cf23 I.cf24 I.cfc I.inner I.prop29
  obtain ⟨s3, -⟩ := s2.exists_setting3
  exact Eight2.gs82CaseA' I.sy I.c I.j I.rk I.jo I.caseA10 I.caseAL4U4 s3
    (Eight2.normalizer_le_centralizer_a I.sy I.c I.j I.rk I.jo I.comm I.cyc I.az I.a10p I.nine
      I.l2a s3)

end CFSG.ComponentClassification.GSThmB

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerBase
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Symplectic
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Orthogonal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
  (OuterComm outerComm_of_outer_comm outerComm_statedProj_sp outerComm_statedProj_sp_two
    outTowerAt_orthogonal)

theorem outTowerAt_catA_one {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    {p : ℕ} : OutTowerAt (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group p := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (GaloisField q.p q.exponent) := inferInstance
  refine outTowerAt_of_outerComm (OuterComm.of_mulEquiv
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
    (outerComm_of_outer_comm
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm
        (GaloisField q.p q.exponent))))

theorem outTowerAt_catC {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    {p : ℕ} : OutTowerAt (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group p := by
  have hr : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
  exact outTowerAt_of_outerComm (OuterComm.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv) (outerComm_statedProj_sp hr _))

theorem outTowerAt_catB_two {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    {p : ℕ} : OutTowerAt (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group p := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  exact outTowerAt_of_outerComm (OuterComm.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) (outerComm_statedProj_sp_two _))

theorem outTowerAt_catB_even {r : ℕ} {q : TauCeti.PrimePower} (hr : 3 ≤ r) (hq : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) {p : ℕ} :
    OutTowerAt (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group p := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B r q, hv⟩
  exact outTowerAt_of_outerComm (OuterComm.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq hr)
    (outerComm_statedProj_sp hr _))

theorem outTowerAt_catOrth {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : RankLE2 p (Cat d)) :
    OutTowerAt (TauCeti.CFSGIndex.lie d).Group p := by
  by_cases hp3 : p = 3
  · subst hp3
    exact absurd hrk (not_rankLE2_orthogonal_three d hd)
  · refine outTowerAt_orthogonal hd hp ?_
    have h2 := hp.two_le
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

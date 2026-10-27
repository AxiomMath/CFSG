module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294DeltaBase
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Symplectic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
  (OuterComm outerComm_of_outer_comm outerComm_statedProj_sp outerComm_statedProj_sp_two)

theorem DeltaTowerAt.of_alternating {n : ℕ} (hn : 5 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    DeltaTowerAt p (alternatingGroup (Fin n)) :=
  DeltaTowerAt.of_not_dvd_card_outer hp
    (CFSG.RankThree.PartOne.not_dvd_outer_alternating hp (by omega) hn)

theorem DeltaTowerAt.of_catA_one {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (GaloisField q.p q.exponent) := inferInstance
  exact DeltaTowerAt.of_outerComm (OuterComm.of_mulEquiv
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
    (outerComm_of_outer_comm
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm
        (GaloisField q.p q.exponent))))

theorem DeltaTowerAt.of_catC {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group := by
  have hr : 3 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
  exact DeltaTowerAt.of_outerComm (OuterComm.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv) (outerComm_statedProj_sp hr _))

theorem DeltaTowerAt.of_catB_two {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  exact DeltaTowerAt.of_outerComm (OuterComm.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) (outerComm_statedProj_sp_two _))

theorem DeltaTowerAt.of_catB_even {r : ℕ} {q : TauCeti.PrimePower} (hr : 3 ≤ r) (hq : q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) {p : ℕ} :
    DeltaTowerAt p (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B r q, hv⟩
  exact DeltaTowerAt.of_outerComm (OuterComm.of_mulEquiv
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq hr)
    (outerComm_statedProj_sp hr _))

end CFSG.LocalAnalysis.RankFourTheoremC

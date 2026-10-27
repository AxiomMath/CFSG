module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BSplitLocal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SSporadic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SChev
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SRee
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SLinear
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SUnitary
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SSp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SOrthMinus
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem liftClause_classical (t : StatedLieTag) (n p f : ℕ) :
    FamilyLift fun S _ => StatedClassicalModel S t n p f := by
  cases t with
  | PSL => exact liftClause_classical_PSL
  | PSU => exact liftClause_classical_PSU
  | PSp => exact liftClause_classical_PSp
  | POmegaOdd => exact liftClause_classical_POmegaOdd
  | POmegaPlus => exact liftClause_classical_POmegaPlus
  | POmegaMinus => exact liftClause_classical_POmegaMinus
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    intro S _ _ _ _ h
    exact h.2.elim

theorem kFactSylowSplit_holds :
    KFactSylowSplit := by
  intro p hp hp2 K _ _ hs hnonab hcat hrank S
  have hclause : LiftClause K :=
    liftClause_of_catalog_of_families liftClause_classical
      (fun t p f ht => liftClause_chevalleyExceptional ht)
      (fun t p f ht => liftClause_reeTits ht)
      (fun p f => liftClause_suzuki_family)
      (fun S _ _ _ hnonab h => liftClause_sporadicRep hnonab h) hnonab
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnonab hcat)
  exact (hclause p hp hp2 hrank).split hp S

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

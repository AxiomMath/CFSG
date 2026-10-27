module

public import CFSG.LocalAnalysis.GL83PartI.I713.Dispatch
public import CFSG.LocalAnalysis.GL83PartI.I713.Linear
public import CFSG.LocalAnalysis.GL83PartI.I713.Unitary
public import CFSG.LocalAnalysis.GL83PartI.I713.Symplectic
public import CFSG.LocalAnalysis.GL83PartI.I713.Orthogonal
public import CFSG.LocalAnalysis.GL83PartI.I713.Exceptional
public import CFSG.LocalAnalysis.GL83PartI.I713.SuzukiRee
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace GL83.I713

open CFSG.Open CFSG.Blueprint

theorem familyClause_classical (t : StatedLieTag) (n p f : ℕ) : FamilyClause fun S _ => StatedClassicalModel S t n p f := by
  intro S _ _ _ hnonab hm
  cases t with
  | PSL => exact outClauseFor_classical_PSL hm
  | PSU => exact outClauseFor_classical_PSU hnonab hm
  | PSp => exact outClauseFor_classical_PSp hnonab hm
  | POmegaOdd => exact outClauseFor_classical_POmegaOdd hnonab hm
  | POmegaPlus => exact outClauseFor_classical_POmegaPlus hnonab hm
  | POmegaMinus => exact outClauseFor_classical_POmegaMinus hnonab hm
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hm.2.elim

theorem outClauseFor_of_catalog
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) : OutClauseFor S :=
  outClauseFor_of_catalog_of_families familyClause_classical
    (fun _ _ _ ht _ _ _ _ hn hm => outClauseFor_chevalleyExceptional hn ht hm)
    (fun _ _ _ ht _ _ _ _ _ hm => outClauseFor_reeTits ht hm)
    (fun _ _ _ _ _ _ _ hm => outClauseFor_suzuki hm) hnonab hcat

theorem i713OuterClause_holds :
    I713OuterClause := by
  intro p hp hp2 K _ _ hs hnonab hcat hK
  have := hs
  exact outClauseFor_of_catalog hnonab
    (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnonab hcat) p hp hp2 hK

theorem i_7_13_1_holds :
    GL83.I_7_13_1 :=
  i_7_13_1_of_outerClause i713OuterClause_holds

end GL83.I713

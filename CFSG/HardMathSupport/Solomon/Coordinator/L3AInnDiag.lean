module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem l3a_exists_conjAut_of_isConjByGL (F : Type) [Field F]
    {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F))}
    (h : Lemma54Ns.IsConjByGL (CFSG.Open.StatedSL 3 F) φ) :
    ∃ A : GL (Fin 3) F, MulAut.congr (psiO F) φ = conjAut 3 F A := by
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (AutL3.congr_psiO_mem_linearAutGroup h)
  exact ⟨A, hA.symm⟩

theorem l3a_exists_psuConj_of_isConjByGL {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (hq : 2 < p ^ f) {φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) F))}
    (h : Lemma54Ns.IsConjByGL (CFSG.Open.StatedSU 3 (p ^ f) F) φ) :
    ∃ u : ↥(unitaryIsom3 hF), MulAut.congr (psuO hF).symm φ = psuConj hF u := by
  obtain ⟨u, hu⟩ := AutL3.congr_psuO_mem_psuConj_range hF hq h
  exact ⟨u, hu.symm⟩

export LocalBalance.AutL3 (input7_fieldInnDiag_holds)

end CFSG.HardMathSupport.Solomon.Coordinator

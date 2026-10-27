module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt2B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL43G

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem lemma4_3_holds : Lemma4_3Stmt :=
  fun hI hG hc h2 => S4A.lemma4_3_of hI hG hc h2

end CFSG.OddStandard.SmallF3.HarrisU33

module

public import CFSG.ClassicalInvolution.Asc77.SU4Node
public import CFSG.ClassicalInvolution.SmallCases.TwinChainDefs

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

theorem su4PatternStmt_of_one_mod_four (hq4 : p ^ f % 4 = 1) : SU4PatternStmt p f := by
  intro G _ _ _ _ K z S _ Λ K₁ K₂ z₁ _ hK₂ hz₁ c02 p01 p12 hK₂i
  exact Λ.exists_shortNode_centralizer_of_one_mod_four S.odd S.five hq4 S.inClass S.p1 S.cls hz₁
    p01 p12 (mem_centralizingMembers_of_commutes hK₂ S.cls.mem c02.symm) hK₂i

end CFSG.ClassicalInvolution.Generic.CoreAssembly

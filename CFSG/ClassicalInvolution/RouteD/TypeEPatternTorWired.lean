module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclWired
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGlue

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime]

theorem e7TorusFixed : E7TorusFixed p f := by
  intro G _ _ _ _ K z _ hshape c j hj hjimg β hβ t htβ hKβ hβ0 ht
  exact c.torusFixedP_of_node_system (single_class K) hshape hj hjimg hβ htβ hKβ hβ0 ht

theorem e7PartnerExists_of_fundNoncentral (hMFZ : Gaps.FundNoncentral p) : E7PartnerExists p f :=
  e7PartnerExists_of_torusFixed hMFZ e7TorusFixed

end CFSG.ClassicalInvolution.MilestoneAssembly

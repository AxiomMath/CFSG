module

public import CFSG.ClassicalInvolution.Asc77.WP3CFCTag
public import CFSG.ClassicalInvolution.Asc77.WP3CFCPos

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CFC

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.SCV

section Third

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem hyp51At_zt_of_third (hs : ChainFrameCore p f Ω K J K' z t z')
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t)) :
    Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t) :=
  hyp51At_zt_of_tagZT hs (tagZT_at hs hThird)

end Third

end CFSG.ClassicalInvolution.Asc77.CFC

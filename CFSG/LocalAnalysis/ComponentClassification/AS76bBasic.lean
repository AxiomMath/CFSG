module

import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup

theorem pRank_type_eq_open {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p H = CFSG.Open.pRank p H := CFSG.SectionRank.pRank_coe_eq_openPRank p H

end CFSG.ComponentClassification.AS76b

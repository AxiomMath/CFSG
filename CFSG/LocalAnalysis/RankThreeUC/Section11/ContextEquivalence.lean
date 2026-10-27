module


public import CFSG.LocalAnalysis.RankThreeUC.Section11.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section11.Context

open CFSG.LocalAnalysis.RankThreeUC CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem section11_context_iff_section12 (M T : Subgroup G) :
    Section11.Context G M T ↔ Section12.Context G M T :=
  ⟨fun h => ⟨h.uc, h.mSigma, h.sylow⟩, fun h => ⟨h.uc, h.mSigma, h.sylow⟩⟩

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.Section11.Context.toSection12 {M T : Subgroup G} (h : Section11.Context G M T) :
    Section12.Context G M T := (section11_context_iff_section12 M T).1 h

end CFSG.LocalAnalysis.RankThreeUC.Section11.Context

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltJ
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.KFactProofs.Fi22Alt

theorem kFactFi22AltSection :
    KFactFi22AltSection := by
  intro L _ _ hL
  obtain ⟨⟨X, Y, q, xs, D⟩, -⟩ := altData_of_isFi22 hL
  obtain ⟨e⟩ := D.nonempty_alt9
  exact ⟨9, Subgroup.closure (xs '' Set.Icc 1 7), le_refl _, ⟨e⟩⟩

end CFSG.AGLEmbedding

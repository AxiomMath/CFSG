module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10S
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10R
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem gs81Exit10Input_of (h10 : GS81Step10Input) (hrec : CF81Exit10Recognition) :
    GS81Exit10Input := by
  intro hCI H _ _ h H₁ d v hst p f hp hp2 hf hJ hK hq h9
  obtain ⟨z₀, J₀, hz₀, hzJ, hsub, ⟨S, r, hr, ⟨eS⟩⟩, hwit⟩ :=
    h10 H h H₁ d v hst p f hp hp2 hf hJ hK hq h9
  have heq := h.genFittingFStar_eq
  obtain ⟨-, hsimple, -, -, -⟩ := h.generalizedFitting_simple
  have : IsSimpleGroup ↥(Open.genFittingFStar H) := by rw [heq]; exact hsimple
  have hFnonab : ∃ u w : ↥(Open.genFittingFStar H), u * w ≠ w * u := by
    rw [heq]
    exact h.exists_ne_commute_generalizedFitting
  have hout := (hCI H hFnonab z₀ hz₀ J₀ hzJ hsub S ⟨r, hr, ⟨eS⟩⟩).1 hwit
  rw [heq] at hout
  exact hrec H h H₁ d v hst p f hp hp2 hf hJ hK hq hout

end CFSG.ComponentClassification.GSThmB

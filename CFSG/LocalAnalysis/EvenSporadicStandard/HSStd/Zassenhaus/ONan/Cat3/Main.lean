module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Spor
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.OrdersExc
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Classical

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem catThreeA5_holds : CatThreeA5 := by
  intro L _ _ _ hnoncomm hcat h3 hcent
  have hC : CentHyp L := hcent
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hexc | hspor
  · exfalso
    obtain ⟨a, b, hab⟩ := hnoncomm
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (false_of_alternating e hn h3 hC).elim
  · exact Or.inr (Or.inr (classical_cases hcl h3 hC))
  · exact (false_of_exceptionalRep hexc h3).elim
  · rcases sporadic_cases hspor h3 hC with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

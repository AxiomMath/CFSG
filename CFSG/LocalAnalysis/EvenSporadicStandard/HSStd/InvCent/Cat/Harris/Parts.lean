module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Sporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Even
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Odd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic


theorem catHarrisAS_of_parts
    (kL281 : HarrisKleinFree .PSL 2 3 4) (kU39 : HarrisKleinFree .PSU 3 3 2)
    (kS43 : HarrisKleinFree .PSp 2 3 1) (kL42 : HarrisKleinFree .PSL 4 2 1)
    (kL52 : HarrisKleinFree .PSL 5 2 1) (kU42 : HarrisKleinFree .PSU 4 2 1)
    (kU52 : HarrisKleinFree .PSU 5 2 1) (kS44 : HarrisKleinFree .PSp 2 2 2)
    (kS48 : HarrisKleinFree .PSp 2 2 3)
    (aL281 : HarrisOddSharp .PSL 2 4) (aU39 : HarrisOddSharp .PSU 3 2)
    (aS43 : HarrisOddSharp .PSp 2 1)
    (wO7 : HarrisOmegaLarge .POmegaOdd 3 1) (wO8 : HarrisOmegaLarge .POmegaMinus 4 1) :
    CatHarrisAS := by
  intro G _ _ S hSn hS hna hcat hc t ht ⟨ζ⟩
  haveI := hSn
  have h : Cfg G S t := ⟨hS, hna, hc, ht⟩
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition ↥S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨es⟩⟩
  · exact (alt_arm_false h ζ hn θ).elim
  · rcases odd_arm CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      CFSG.SeitzReduction.gls3OddLieAutComponentsInput aL281 aU39 aS43 wO7 wO8 kL281 kU39 kS43
      h ζ hodd with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr h3))
  · by_cases htS : t ∈ S
    · exact (even_inner_false h ζ htS heven).elim
    · exact (even_outer_false CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        kL42 kL52 kU42 kU52 kS44 kS48 h ζ htS heven).elim
  · have hs := sporadic_arm es h ζ
    subst hs
    exact Or.inr (Or.inl ⟨es⟩)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

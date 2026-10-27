module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoElt
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwoSL3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

set_option linter.unusedSectionVars false


theorem excTLInnerTwo_of_ne_G2 {τ : Tag} (hτ : τ ≠ .G2) : ExcTLInnerTwo τ := by
  intro K _ _ hK M _ χ i hA2 _hperf q hq hL2
  obtain ⟨γ, hγ, δ, hδ, hsum, h1, h2, h3⟩ := hA2
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγr := hΨ.isRoot γ hγ
  have hδr := hΨ.isRoot δ hδ
  obtain ⟨h, nγ, nδ, hform⟩ := excTL_a2_lengths hτ hγr hδr hsum h1 h2 h3
  obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := hL2
  rcases excTL_chain_or_subset hτ hΨ hγ hδ nγ nδ hform with hsub |
      ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, n1, n2, n3, p12, p23, p13⟩
  · obtain ⟨hfin, hcard⟩ := excTL_two_card_le hτ hK hγr hδr nγ nδ hform
      (S := componentRoots χ i) hsub
    haveI : Finite ↥(componentRootSpan K χ i) := hfin
    exact excTL_false_of_card φ (by rw [hF]; exact hq) hcard
  · exact excTL_two_false_of_chain hτ hK φ ha₁ ha₂ ha₃ n1 n2 n3 p12 p23 p13

end CFSG.HardMathSupport.Dickson.Sec6.I1431

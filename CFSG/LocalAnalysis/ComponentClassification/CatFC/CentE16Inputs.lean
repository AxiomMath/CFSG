module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Even
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Odd
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedComponent

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem catE16_of_inputs (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hcard : ∀ s : TauCeti.SporadicName, Nat.card (NativeSporadic.Carrier s) = sporOrder s)
    (hm11 : Nat.card {x : NativeSporadic.Carrier .M11 // orderOf x = 2} = 165)
    (hj1 : ∀ φ : MulAut (NativeSporadic.Carrier .J1), ∃ g : NativeSporadic.Carrier .J1,
      φ = MulAut.conj g) : CatE16 := by
  intro K _ _ hcat _ hna τ hτ2 hout hCA κ hκ hκ2 hQ
  obtain ⟨e⟩ := hCA
  let D : CatE16Data K := ⟨τ, hτ2, hout, e, κ, hκ, hκ2, hQ⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition K hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | hsp
  · by_cases h6 : n = 6
    · subst h6
      exact (e16_false_odd hGLS hO D (oddLieType_of_alternating_six ⟨θ⟩)).elim
    · exact (e16_false_alt D hn h6 θ).elim
  · exact (e16_false_odd hGLS hO D hodd).elim
  · exact e16_even hO D heven
  · exact (e16_false_sporadic hcard hm11 hj1 D hsp).elim

end CFSG.ComponentClassification.CatFC

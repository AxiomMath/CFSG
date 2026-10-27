module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuterClassical
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuterExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG CFSG.Blueprint CFSG.Open


theorem evenOuterA6LeafMod_holds : EvenOuterA6LeafMod := by
  intro S _ _ hS σ hσ hout J hdata
  obtain ⟨t, n, f, hadm, hm⟩ := hS
  have hO : ComponentClassification.CatLeaf.LieOrderFormulasInput :=
    ComponentClassification.CatLeafProof.lieOrderFormulasInput
  cases t
  · exact KForm.Mod.z2s6_even_PSL hO hadm hm hdata hout
  · exact KForm.Mod.z2s6_even_PSU hO hadm hm hdata hout
  · exact KForm.Mod.z2s6_even_PSp hO hadm hm hdata hout
  · exact (hadm.2.2.2 rfl).elim
  · exact KForm.Mod.z2s6_even_Omega hO (Or.inl rfl) hadm hm hdata hout
  · exact KForm.Mod.z2s6_even_Omega hO (Or.inr rfl) hadm hm hdata hout
  · exact (KForm.Mod.z2s6_even_G2 hO hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_F4 hO hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_E6 hO hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_E7_E8 hO (Or.inl rfl) hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_E7_E8 hO (Or.inr rfl) hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_twistedE6 hO hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_trialityD4 hO hadm hm hdata hout).elim
  · exact (KForm.Mod.z2s6_even_twistedB2 hadm hm hσ hout).elim
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact (KForm.Mod.z2s6_even_twistedF4 hadm hm hσ hout).elim
  · exact (KForm.Mod.z2s6_even_Tits hadm hm hσ hout).elim

end CFSG.EvenSporadicStandard.M24Std

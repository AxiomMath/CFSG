module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Chevalley
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Linear
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Orthogonal
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Ree
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Suzuki
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Symplectic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Tits
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Unitary
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem involutionCentralizersCharTwo_of_evenLieType {S : Type} [Group S] (h : EvenLieType S) :
    InvolutionCentralizersCharTwo S := by
  obtain ⟨t, n, f, hadm, hm⟩ := h
  rcases hm with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
  · simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact involutionCentralizersCharTwo_of_psl_model hcl
    · exact involutionCentralizersCharTwo_of_psu_model hcl
    · exact involutionCentralizersCharTwo_of_psp_model hcl
    · exact absurd rfl hcl.1.2.2.2
    · exact involutionCentralizersCharTwo_of_pOmega_model (.inl rfl) hcl
    · exact involutionCentralizersCharTwo_of_pOmega_model (.inr rfl) hcl
  · exact involutionCentralizersCharTwo_exceptional ht hex
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact involutionCentralizersCharTwo_twistedF4 hrt
    · exact involutionCentralizersCharTwo_tits hrt
  · exact involutionCentralizersCharTwo_suzuki hsz

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod

namespace CFSG.EvenSporadicStandard.M24Std


theorem evenLieInvolutionTwoConstrained_holds : EvenLieInvolutionTwoConstrained := by
  intro S _ _ h t ht
  exact KForm.Mod.involutionCentralizersCharTwo_of_evenLieType h t ht

end CFSG.EvenSporadicStandard.M24Std

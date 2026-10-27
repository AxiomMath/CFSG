module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3FinKA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest10

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem not_d8InCentralizer16_of_u43Ext
    {K : Type} [Group K] (e : K ≃* ↥U43Ext) :
    ¬ D8InCentralizer16 K := by
  rintro ⟨s, -, hs, -, -⟩
  have h1 : orderOf (e s) = 16 := by rw [MulEquiv.orderOf_eq]; exact hs
  have h2 : orderOf ((e s : ↥U43Ext) : Equiv.Perm (Fin 820)) = 16 := by
    rw [Subgroup.orderOf_coe]
    exact h1
  exact U43Ext_orderOf_ne_sixteen (e s).2 h2

theorem finK16 :
    FinK16 := by
  intro K _ _ hK
  rcases hK with ⟨N, hN, ⟨e⟩, hC⟩ | ⟨⟨e⟩⟩
  · exact not_d8InCentralizer16_of_prod hN e hC
  · exact not_d8InCentralizer16_of_u43Ext e

theorem fin76bOuterRest₉_of_rest₁₀_cert
    (hR : Fin76bOuterRest₁₀) :
    Fin76bOuterRest₉ :=
  fin76bOuterRest₉_of_rest₁₀ finK16 hR

end CFSG.EvenSporadicStandard.Fin76b

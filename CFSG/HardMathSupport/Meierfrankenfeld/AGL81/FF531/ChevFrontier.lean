module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFrontier

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isChevIndexTwo_of_characteristic {i : TauCeti.LieTypeIndex} (h : i.characteristic = 2) :
    IsChevIndexTwo i := by
  cases i <;> simp_all [IsChevIndexTwo]

theorem ffChevModuleTheorem_of
    (hS : GF2NoFFSporadic) (hO : GF2NoFFLieOdd) : FFChevModuleTheorem := by
  intro V _ _ hV H L hhyp hFF
  obtain ⟨i, ⟨e⟩⟩ := hhyp.2.2.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hhyp.2.1.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod p)) _ _
  | alternating n hn => exact Or.inr ⟨n, hn, ⟨e⟩⟩
  | lie d =>
    by_cases hc : IsClassicalTwoOrG2 (TauCeti.CFSGIndex.lie d).Group
    · exact Or.inl (isChevTwo_of_classicalTwoOrG2
        (CFSG.HardMathSupport.Cooperstein.Proving.isClassicalTwoOrG2_of_mulEquiv e.symm hc))
    · by_cases hd : d.1.characteristic = 2
      · exact Or.inl (Or.inl ⟨d, isChevIndexTwo_of_characteristic hd, ⟨e⟩⟩)
      · by_cases hq : IsSQTKOddLieIndex d.1
        · exact absurd hFF (noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_odd d hq)
            V hV H L hhyp ⟨e⟩)
        · exact absurd hFF (hO d hd hc hq V hV H L hhyp ⟨e⟩)
  | sporadic n =>
    by_cases hq : IsSQTKSporadic n
    · exact absurd hFF (noFFModule_of_noIrrFFOffender
        (CFSG.HardMathSupport.Cooperstein.Proving.noIrrFFOffender_sporadic n hq)
        V hV H L hhyp ⟨e⟩)
    · exact absurd hFF (hS n hq V hV H L hhyp ⟨e⟩)

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531

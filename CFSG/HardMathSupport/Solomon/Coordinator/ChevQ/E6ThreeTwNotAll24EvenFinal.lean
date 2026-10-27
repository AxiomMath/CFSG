module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenD5Index
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open TauCeti CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

set_option linter.unusedSectionVars false

section Main


theorem twE6ConnShapeEvenD5 : TwE6ConnShapeEvenD5 := by
  intro K _ _ σ q E hcube hK2 f hfE hf1 hdim J hJ
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hcube.three_dvd
    omega
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  obtain ⟨h, hh, hd⟩ := hdim
  have hinj := twE6_conj_injective K σ q hcube.frob hcube.card_field hq2
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hf1 (hh.symm.trans (map_one _))
  have hh3 : h ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hh, map_one]
    exact hf3
  obtain ⟨r, e, hrK, hmodel⟩ := strongModel_of_d5_component K σ q hcube.char_ne_three hcube.frob
    hcube.card_field hq2 hcube.three_dvd h hh1 hh3 hd (hh ▸ hJ)
  intro _
  obtain ⟨d, ⟨ed⟩, hd3, hex⟩ := exists_lieIndex_of_pominus hmodel.1
    (by rw [← hrK]; exact hcube.char_ne_three)
  exact Or.inl ⟨d, ed, hd3, hex⟩

end Main

end KSConn

section Export

open KSConn


theorem twE6ConnShapeEven : TwE6ConnShapeEven := twE6ConnShapeEven_of_d5 twE6ConnShapeEvenD5

end Export

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

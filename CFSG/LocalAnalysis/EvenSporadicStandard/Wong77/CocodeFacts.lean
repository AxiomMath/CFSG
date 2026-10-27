module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Cocode

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint

theorem permLin_ind (g : Equiv.Perm (Fin 23)) (s : Finset (Fin 23)) :
    permLin g (ind s) = ind (s.image g) := by
  ext j
  simp only [permLin_apply, ind_apply]
  congr 1
  apply propext
  rw [Finset.mem_image]
  constructor
  · intro h
    exact ⟨g⁻¹ j, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

end CFSG.EvenSporadicStandard.Wong77.Module

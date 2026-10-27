module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Parts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltSeven
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem kd1426Alt_holds : KD1426Alt := by
  intro Y _ _ K B hK hq hcat hcore hlev hB hKB hcard hmax hC hH hM
  obtain ⟨i, hi, ⟨eK⟩⟩ := hcat
  cases i with
  | alternating n h =>
    change n = 7 ∨ n = 10 at hi
    rcases hi with rfl | rfl
    · exact KD1426AltSeven.alt7_core K B hK hq eK hcore hB hKB hcard hH
    · exact KD1426AltTenCore.alt10_core hK hq eK hcore hB hcard hmax hC hH
  | cyclic p hp => exact False.elim hi
  | lie d => exact False.elim hi
  | sporadic s => exact False.elim hi

end CFSG.LocalAnalysis.GLTheoremA

end

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpPow
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrSpTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.Sp

theorem parabIrrOn_idxB_of
    (hGA : CFSG.Open.GriessAllModelsStatement) : ParabIrrOn (IsLieOf IdxB) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  left
  obtain ⟨r, K, _, _, _, hr, ⟨φ⟩⟩ :=
    exists_mulEquiv_statedSp_of_isQuasisimple_idxB hGA hY h2 hF
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_isParabolicTwo hpar hne φ
  let C : SpCover Y P r K I := ⟨ρ, hρ⟩
  have hPY : P ≤ Y := hpar.1
  have hbig := C.exists_big_block hI htI hmax hPY hna
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · exact parabIrr_of_two C (by omega) hI htI hmax hbig hPY hp hp2 hB hcyc hBY hBP hW hNY hNB hirr
  · exact parabIrr_of_three_le C h3 hI htI hmax hbig hPY hp hp2 hB hcyc hBY hBP hW hNY hNP hNB
      hirr

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

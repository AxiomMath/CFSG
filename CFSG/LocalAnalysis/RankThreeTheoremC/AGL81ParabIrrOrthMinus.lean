module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusRep
public import CFSG.Open.GriessAllModelsStatement
public import Certificates.Certificate2326

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding

theorem parabIrrOn_idxTwistedD_of
    (hGA : CFSG.Open.GriessAllModelsStatement) : ParabIrrOn (IsLieOf IdxTwistedD) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hBp hcyc hBY hBP hW hNY hNP hNB hirrN
  left
  obtain ⟨r, K, _, _, _, b, c, hr, hirr, ⟨φ⟩⟩ :=
    ParabComm.OrthMinus.exists_mulEquiv_orthElementary_of_isQuasisimple_idxTwistedD hGA hY h2 hF
  obtain ⟨ρ, s, d, hd, hρ⟩ := LeviBlock.exists_comap_eq_orthParab hr hirr hpar φ.symm
  let C : ParabComm.OrthMinus.OmCover Y P r K b c d := ⟨ρ, hρ⟩
  have hPY : P ≤ Y := hpar.1
  have hbig := C.exists_big_block hd hr hirr hPY hna
  intro β hβ y hy
  exact C.centralizes_of_autHom_eq_one ⟨β, hBY hβ⟩
    (OrthMinus.autHom_eq_one_of_irred hp hp2 hr hirr hd C hPY hbig hBp hcyc hBY hBP hW hNY hNP hNB
      hirrN ⟨β, hβ⟩) y hy

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

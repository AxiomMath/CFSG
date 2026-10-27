module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeReeOpp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LieType.ChevTwo CFSG.LieType.ChevTwo.Semi
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


theorem seitzTwoGen_of_reeTitsModel_twistedF4 {S : Type} [Group S] [Finite S] {a : ℕ}
    (ha : 1 ≤ a) (h : ReeTitsModel S .twistedF4 2 (2 * a + 1)) : SeitzTwoGen S := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma ha h
  exact seitzTwoGen_of_mulEquiv e.symm (seitzTwoGen_reeGamma (K := K) (a := a) ha hK)

end CFSG.LocalAnalysis.GLTheoremA.Y10F

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmSix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

theorem famOmP_holds : FamOmP := by
  intro n q hv hq hn
  obtain ⟨V, _, _, _, Q, hQ, hdim, hplus, hθ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S172B.exists_omegaPlusTwo_model (n := n) (by omega)
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩).Group
      (CFSG.LocalAnalysis.GLTheoremA.isOmPA n 2) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩, Or.inl ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := hθ _ hcat
  refine noSmallModel_of_mulEquiv e ?_
  rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
  · exact noSmallModel_plus_five hQ hdim hplus
  · exact noSmallModel_plus_six hQ hdim hplus
  · exact noSmallModel_plus_ge_seven hQ hdim h7 hplus

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubFU5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubFSp6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4

theorem stdSubFAt_holds (G : Type) [Group G] [Finite G] :
    StdSubFAt G := by
  intro K hK hcat
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  rcases hi with h | h | h
  · obtain ⟨e⟩ := bridge_u4two (⟨i, h, ⟨e0⟩⟩ : catalogIs _ S9.isU4two)
    exact stdSub_of_tau hK e (StdU4.card_center_dvd_two_u4two hGA hK ⟨i, h, ⟨e0⟩⟩) StdU4.TphiQ
      StdU4.TphiQ_injective StdU4.isPGroup_T4 (by rw [StdU4.card_T4]; norm_num) StdU4.hFN_T4
      StdU4.hTc_T4
  · obtain ⟨e⟩ := U52Layer.bridge_u5two_stated (⟨i, h, ⟨e0⟩⟩ : catalogIs _ S9.isU5two)
    obtain ⟨τ, TM, h1, h2, h3, h4, h5⟩ := StdU5.stdSub_u5_data
    exact stdSub_of_tau hK e (StdU5.card_center_dvd_two_u5two hGA hK ⟨i, h, ⟨e0⟩⟩) τ h1 h2 h3 h4 h5
  · obtain ⟨e⟩ := bridge_sp6two (⟨i, h, ⟨e0⟩⟩ : catalogIs _ S9.isSp6two)
    exact stdSub_of_tau hK e (StdSp6.card_center_dvd_two_sp6two hGA hK ⟨i, h, ⟨e0⟩⟩) StdSp6.tau6
      StdSp6.tau6_injective StdSp6.isPGroup_T6 (by rw [StdSp6.card_T6]; norm_num) StdSp6.hFN_T6
      StdSp6.hTc_T6

end CFSG.LocalAnalysis.GLTheoremA.CatB

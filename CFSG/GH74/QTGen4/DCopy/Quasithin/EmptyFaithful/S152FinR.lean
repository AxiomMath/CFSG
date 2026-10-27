module

public import CFSG.Quasithin.EmptyFaithful.S152FinR
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L27
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Skeleton

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageRankNotTwo_of_finalR_F4 (h1518 : StageLemma1518) (h1519 : StageLemma1519)
    (h15111 : StageLemma15111) (h15112 : StageLemma15112) (h15208 : StageLemma15208_F4)
    (h15209 : StageNotation15209_F4) (h15213 : StageLemma15213_F4) (h15215 : StageTheorem15215_F4)
    (h25 : StageLemma15225_F4) (h26 : StageLemma15226_F4) (h27 : StageLemma15227Two_F4)
    (h28 : StageLemma15228_F4) (hfin : StageFinal152R) : StageRankNotTwo_F4 := by
  intro G _ _ T Mc M h hM hne4
  by_contra hOF
  have hCE : IsCE1513 T M := ⟨hne4, hOF⟩
  have hs : Setting152 T Mc M := ⟨h, hM, hCE⟩
  obtain ⟨H, hH⟩ := exists_isHStar h.inM_mc hM.1.1 hM.2.1.symm
  obtain ⟨H₁, H₂, hP⟩ := (h15209 G T Mc M hs H hH).pair
  obtain ⟨B₀, hB₀, -, -⟩ := (h15213 G T Mc M hs H hH).exists_B0
  have c1519 := h1519 G T Mc M h hM hCE
  have hAm := stageObserveF7N_of h1519 G T Mc M hs H hH
  exact hfin G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ hAm
    c1519.six_autOn (h1518 G T Mc M h hM hCE) (h15111 G T Mc M h hM hCE H hH)
    (h15112 G T Mc M h hM hCE H hH).1 (h15208 G T Mc M hs H hH) (h25 G T Mc M hs)
    (h26 G T Mc M hs).1 ((h26 G T Mc M hs).2 H hH)
    (lemma15227_three_of hs c1519 (h15215 G T Mc M hs B₀ hB₀) (h26 G T Mc M hs).1.w0_le
      hAm.elemAbelian (h27 G T Mc M hs))
    (h28 G T Mc M hs H hH B₀ hB₀)

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KLiftA7Ker
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.NatFinal
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Lift.FourCase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.A7Six CFSG.AGLEmbeddingD2.McLaughlin.A7Lift
  CFSG.HardMathSupport.Cooperstein.Coordinator Equiv Equiv.Perm

theorem false_of_alt7_yComponent_of_gnD
    {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hP : CFSG.Quasithin.IsC118Pair T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (eL : ↥Ls ≃* alternatingGroup (Fin 7))
    (hDL : CFSG.AGLEmbeddingD2.GN.gnD T ⊓
      Ls.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T) : False := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hLs
  have hGF : GF2EightFive :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds
  rcases exists_naturalOn_or_four_of_gf2EightFive hGF hX hLs.1 hJ eL with hn | hfour
  · exact false_of_alt7_natural_gen hX hP hLs eL hn
  · obtain ⟨W, U, hWV, hZW, hWK, hWU, hUV, hUK, hU16⟩ := hfour
    exact false_of_alt7_four hX hP hLs hJ eL hDL hWV hZW hWK hWU hUV hUK hU16

theorem kLiftA7_holds :
    KLiftA7 := by
  intro X _ _ T T₁ T₂ hX hg Ls L hLs hL ⟨eL⟩
  by_cases hDL : CFSG.AGLEmbeddingD2.GN.gnD T ⊓
      Ls.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T
  · exact (false_of_alt7_yComponent_of_gnD hX hg.c118 hLs eL hDL).elim
  · have hZ : Subgroup.center ↥Ls = ⊥ :=
      CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eL
        (alternatingGroup.center_eq_bot (by norm_num))
    obtain ⟨e⟩ := nonempty_barO2_mulEquiv_of_not_gnD_le hX hLs.1 hZ hL hDL
    exact ⟨e.trans eL⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

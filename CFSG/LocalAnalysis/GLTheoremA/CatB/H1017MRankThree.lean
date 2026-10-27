module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017MRankThreeCover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAMain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeAGlue

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Dickson.I271.TabMThreeA (zetaM_spec ker_yMc_le ker_coverHom_yMc
  centralizer_zetaM_eq_range coverHom_surjective yJ_surjective)


theorem i1017MonsterThreeRank_holds : I1017MonsterThreeRank := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨g⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M
  let φ : CFSG.Monster.Existence.MGriess ≃* K := (g.trans b).trans e.symm
  haveI : Finite CFSG.Monster.Existence.MGriess := Finite.of_equiv K φ.symm.toEquiv
  have hG := CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  have hB3 := CFSG.HardMathSupport.Dickson.I271.tabBThreeACard_thm
  have h := ker_yMc_le hG
  obtain ⟨hζ3, -, -, hker⟩ := ker_coverHom_yMc hG h
  obtain ⟨-, -, -, -, ⟨f⟩⟩ := zetaM_spec hB3 hG
  have hZ := card_center_centralizer_of_cover (centralizer_zetaM_eq_range hB3 hG)
    (coverHom_surjective h yJ_surjective) CFSG.Sporadic.Fi24.center_J hker
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_of_fi24Cover _ (hZ.trans hζ3) f
  exact ⟨E.map φ.toMonoidHom, isElemAbelian_map_equiv φ hE,
    by rw [Subgroup.card_map_of_injective φ.injective, hc]⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

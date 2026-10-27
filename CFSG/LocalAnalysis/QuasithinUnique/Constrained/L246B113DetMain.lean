module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetA7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetLie
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetList

public section

namespace CFSG.QuasithinUnique.Bridge.B113Det

open CFSG.Quasithin CFSG.Open

open scoped commutatorElement

theorem asB113DetList_of_dichotomy
    (hD : AsB42DichotomyNat) :
    AsB113DetList (IsSQTKQuotient CFSG.SectionRank.IsKGroupCat) := by
  intro V _ _ hV G A L hSQ hO2 hA hL hLA
  have hLG : L ≤ G := hL.1
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥L)) := odd_card_center_of_isComponentOf hO2 hL
  have hlist := sqtkSimpleList_of_quasisimple (Subgroup.inclusion hLG)
    (Subgroup.inclusion_injective hLG) hSQ hLq
  have hA7 : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center ↥L = ⊥ := by
    rintro ⟨e7⟩
    exact center_eq_bot_of_alt7 hD hV hA hLG hLq hLA hodd hlist e7
  obtain ⟨W, _, _, Lb, E, hW, hLbq, hirr, ⟨e1⟩, hEN, hE0, hel, hoff, -⟩ :=
    exists_section_module hV hA hLG hLq hLA
  have hlistLb := CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e1.symm hlist
  have hnatLb := (hD W hW Lb hLbq hirr hlistLb E hEN hE0 hel hoff).1
  have hnat := sqtkCharTwoOrAltNative_of_mulEquiv e1 hnatLb
  exact ⟨isLieAltType_of_native hLq hodd hA7 hnat, hnat⟩

end CFSG.QuasithinUnique.Bridge.B113Det

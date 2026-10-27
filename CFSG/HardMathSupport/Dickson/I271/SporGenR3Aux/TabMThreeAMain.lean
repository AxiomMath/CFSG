module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAClaim
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAKer
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAPerfect
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeATwentyThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeATwoB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAQuasi
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAGlue

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443

section Zeta


theorem centralizer_zetaM_eq_range (hB3 : TabBThreeACard) (hG : Gmat = AutO) :
    Subgroup.centralizer ({zetaM hG} : Set MGriess) = (yMc hG).range := by
  have h := ker_yMc_le hG
  obtain ⟨hζ3, hinv, hζD, hker⟩ := ker_coverHom_yMc hG h
  have hDζ := range_yMc_le_centralizer hG h hζD hζ3 hker
  obtain ⟨t, htD, htc, htB⟩ := exists_twoB_mem_range_yMc hG h
  exact centralizer_eq_of_cover_MGriess hB3 hG hDζ hζD hζ3 hinv
    (dvd_card_centralizer_inf_yMc hG h hζ3 hDζ hker) (coverHom (yMc hG) yJ h)
    (coverHom_surjective h yJ_surjective) hker (tGriess_mul_refT_three_mem_range hG) htD htc htB

theorem zetaM_spec (hB3 : TabBThreeACard) (hG : Gmat = AutO) :
    orderOf (zetaM hG) = 3 ∧ tGriess * zetaM hG * tGriess⁻¹ = (zetaM hG)⁻¹ ∧
      23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
        Subgroup.centralizer ({zetaM hG} : Set MGriess)) ∧
      (CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({zetaM hG} : Set MGriess)) ∧
        Nonempty (↥(Subgroup.centralizer ({zetaM hG} : Set MGriess)) ⧸
          Subgroup.center ↥(Subgroup.centralizer ({zetaM hG} : Set MGriess)) ≃*
            CFSG.Blueprint.NativeSporadic.Fi24prime)) := by
  have h := ker_yMc_le hG
  obtain ⟨hζ3, hinv, hζD, hker⟩ := ker_coverHom_yMc hG h
  have hDζ := range_yMc_le_centralizer hG h hζD hζ3 hker
  exact ⟨hζ3, hinv, dvd_card_centralizer_inf_yMc hG h hζ3 hDζ hker,
    quasisimple_centralizer_yMc hG h (commutator_range_yMc hG) hker
      (centralizer_zetaM_eq_range hB3 hG)⟩

end Zeta

section ThreeA


theorem centThreeA_MGriess (hB3 : TabBThreeACard) : CentThreeA MGriess := by
  obtain ⟨hζ3, hinv, h23, hq⟩ := zetaM_spec hB3 Gmat_eq_AutO_of_stroth
  exact centThreeA_MGriess_of_zeta hζ3 hinv h23 hq

end ThreeA

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint

section M


theorem centThreeA_M (hB3 : TabBThreeACard) : CentThreeA (NativeSporadic.Carrier .M) :=
  TabMThreeA.centThreeA_M_of_MGriess (TabMThreeA.centThreeA_MGriess hB3)

end M

end CFSG.HardMathSupport.Dickson.I271

module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open

theorem quasisimple_centralizer_yMc
    (hG : Gmat = AutO) (h : (yMc hG).ker ≤ yJ.ker) {ζ : MGriess}
    (hD : ⁅(yMc hG).range, (yMc hG).range⁆ = (yMc hG).range)
    (hker : ∀ d : ↥(yMc hG).range, coverHom (yMc hG) yJ h d = 1 ↔
      (d : MGriess) ∈ Subgroup.zpowers ζ)
    (hC : Subgroup.centralizer ({ζ} : Set MGriess) = (yMc hG).range) :
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({ζ} : Set MGriess)) ∧
      Nonempty (↥(Subgroup.centralizer ({ζ} : Set MGriess)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({ζ} : Set MGriess)) ≃*
          CFSG.Blueprint.NativeSporadic.Fi24prime) := by
  haveI := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hcen : (coverHom (yMc hG) yJ h).ker ≤ Subgroup.center ↥(yMc hG).range := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((hker d).1 hd)
    have hg : (g : MGriess) ∈ Subgroup.centralizer ({ζ} : Set MGriess) := hC.ge g.2
    have hgc : Commute (g : MGriess) ζ := Subgroup.mem_centralizer_singleton_iff.1 hg
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk]
    exact (hgc.zpow_right k).eq
  obtain ⟨hqs, ⟨e⟩⟩ := isQuasisimple_of_cover (commutator_eq_top_of_commutator_eq hD)
    (coverHom (yMc hG) yJ h) (coverHom_surjective h yJ_surjective)
    ⟨_, _, CFSG.Sporadic.Fi24.a_mul_b_ne⟩ hcen
  exact quasisimple_centralizer_of_isConj (G := MGriess)
    (Q := CFSG.Blueprint.NativeSporadic.Fi24prime) (D := (yMc hG).range) hC (IsConj.refl ζ)
    ⟨hqs, ⟨e.trans CFSG.Sporadic.Fi24.fi24EquivJ.symm⟩⟩

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA

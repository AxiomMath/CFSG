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
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

theorem commutator_range_yMc
    (hG : Gmat = AutO) : ⁅(yMc hG).range, (yMc hG).range⁆ = (yMc hG).range := by
  have h1 := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥(commutator (YGroup 4 4 2))))
    (H₂ := ⊤) (yMc hG)
  rw [← commutator_def, commutator_eq_top_of_commutator_eq y442_commutator_commutator,
    Subgroup.map_top] at h1
  exact h1.symm

theorem range_yMc_le_centralizer
    (hG : Gmat = AutO) (h : (yMc hG).ker ≤ yJ.ker) {ζ : MGriess}
    (hζD : ζ ∈ (yMc hG).range) (hζ3 : orderOf ζ = 3)
    (hker : ∀ d : ↥(yMc hG).range, coverHom (yMc hG) yJ h d = 1 ↔
      (d : MGriess) ∈ Subgroup.zpowers ζ) :
    (yMc hG).range ≤ Subgroup.centralizer ({ζ} : Set MGriess) := by
  refine le_centralizer_of_commutator_eq (commutator_range_yMc hG) hζ3 fun d hd => ?_
  have h1 : coverHom (yMc hG) yJ h ⟨ζ, hζD⟩ = 1 := (hker ⟨ζ, hζD⟩).2 (Subgroup.mem_zpowers ζ)
  have h2 : coverHom (yMc hG) yJ h (⟨d, hd⟩ * ⟨ζ, hζD⟩ * ⟨d, hd⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (hker _).1 h2

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA

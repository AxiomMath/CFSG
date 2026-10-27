module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

@[expose] noncomputable def yWordC (w : List ℕ) (hl : w.length % 2 = 0) (hw : ∀ c ∈ w, c < 11) :
    ↥(commutator (YGroup 4 4 2)) :=
  ⟨evalWord (yGen 4 4 2) w, evalWord_mem_commutator (w.length / 2) w (by omega) hw⟩

theorem coe_yWordC (w : List ℕ) (hl : w.length % 2 = 0) (hw : ∀ c ∈ w, c < 11) :
    (yWordC w hl hw : YGroup 4 4 2) = evalWord (yGen 4 4 2) w :=
  rfl

@[expose] noncomputable def yMc
    (hG : Gmat = AutO) : ↥(commutator (YGroup 4 4 2)) →* MGriess :=
  (yM hG).comp (commutator (YGroup 4 4 2)).subtype

theorem yMc_yWordC
    (hG : Gmat = AutO) (w : List ℕ) (hl : w.length % 2 = 0) (hw : ∀ c ∈ w, c < 11) :
    yMc hG (yWordC w hl hw) = yM hG (evalWord (yGen 4 4 2) w) :=
  rfl

@[expose] noncomputable def zetaM
    (hG : Gmat = AutO) : MGriess :=
  yM hG (evalWord (yGen 4 4 2) yVWord) ^ 17

theorem zetaM_eq
    (hG : Gmat = AutO) :
    zetaM hG = yMc hG (yWordC yVWord (by decide) (by decide) ^ 17) := by
  rw [map_pow, yMc_yWordC]
  rfl

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA

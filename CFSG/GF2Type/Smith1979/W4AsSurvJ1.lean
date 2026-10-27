module

public import CFSG.GF2Type.Smith1979.W4AsE11Layer
public import CFSG.GF2Type.Smith1979.W4AsSurvGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.Open

theorem j1NoFaithfulEight_holds : J1NoFaithfulEight := by
  intro K _ _ ⟨e⟩ V _ _ _ hV ρ hρ
  have h11 : 11 ∣ Nat.card (K ⧸ center K) := by
    rw [Nat.card_congr e.toEquiv, show goldschmidtJ1 = walterJ1 from rfl,
      CFSG.Walter.J1Props.card_walterJ1]
    norm_num
  have h := h11.trans (Surv.card_quotient_center_dvd_gl_eight hV ρ hρ)
  norm_num at h

end CFSG.GF2Type.Smith1979.W4As

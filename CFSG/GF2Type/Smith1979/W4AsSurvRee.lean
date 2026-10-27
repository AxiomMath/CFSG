module

public import CFSG.GF2Type.Smith1979.W4AsE11Layer
public import CFSG.GF2Type.Smith1979.W4AsSurvGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.Open

theorem reeNoFaithfulEight_holds : ReeNoFaithfulEight := by
  intro K _ _ m hm hcard V _ _ _ hV ρ hρ
  have h3 : 3 ^ 9 ∣ Nat.card (K ⧸ center K) := by
    rw [hcard]
    unfold ordRee
    have h : 3 ^ 9 ∣ (3 ^ (2 * m + 1)) ^ 3 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega)
    exact (h.mul_right _).mul_right _
  have h := h3.trans (Surv.card_quotient_center_dvd_gl_eight hV ρ hρ)
  norm_num at h

end CFSG.GF2Type.Smith1979.W4As

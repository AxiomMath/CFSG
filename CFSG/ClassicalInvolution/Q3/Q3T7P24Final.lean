module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A09
public import CFSG.ClassicalInvolution.Q3.Q3T7P25Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T7

section Final


abbrev H3Three : Prop := Q3T8.Asc77.S24B.H3

theorem c24_1Three_of_h3 (h3 : H3Three) : C24_1Three := by
  intro G _ _ _ Ω K K' z hs W hW hzW hS4 hZ
  have hs' : Q3T8.Asc77.Hyp23 Ω K K' z := Q3T7P25.hyp23_of_three hs
  have hZ' : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥ := by
    have e : CFSG.centerIn (Subgroup.normalizer (W : Set G)) =
        Asc77.centerIn (Subgroup.normalizer (W : Set G)) := CFSG.centerIn_eq_map_center _
    rwa [e] at hZ
  obtain ⟨S, R, R', b, b', -, -, -, -, hyp⟩ :=
    Q3T8.Asc77.c24_setupU G Ω K K' z hs' W hW hzW hS4 hZ'
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hyp.hR.1
  have h8 : Nat.card R = 8 := Q3T7P25.natCard_isSylow2In_member hs.1.stand.hyp hJ hRJ
  rcases Q3T8.Asc77.T7C2.c24_5_proved G Ω K K' W S R R' z (b * b') hyp h8 with hnot | hconc
  · exact (Q3T8.Asc77.S24B.c24_9_core_of h3 (Q3T8.Asc77.S24.noGraph_of h3) G Ω K K' W S R R' z
      (b * b') hyp h8 hnot).elim
  · exact hconc

end Final

end CFSG.ClassicalInvolution.Q3.Q3T7P24

module

public import CFSG.ClassicalInvolution.Q3.Q3T7Stmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Disc3

section Main


theorem thm7A3_of_steps (hWz : WzThree) (h21 : C21_2Three) (h22 : C22_1Three)
    (h231 : C23_1Three) (h233 : C23_3Three) (h24 : C24_1Three) (h25 : C25_E4Three) : Thm7A3 := by
  intro G _ _ _ Ω K hs h3 hn ⟨K', hK'tw, hK'ne⟩ hdisc
  by_cases hc : ConcOrTF4 G
  · exact hc.conclusionD hn
  exfalso
  obtain ⟨z, hz⟩ := hs.hyp.classical K hs.mem
  have hU : IsUniqueInvolution K z := hz.isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hstd : Std7Three Ω K K' z := ⟨hs, hdisc, hU, hK'tw, hK'ne, hc, h3⟩
  have hperp : KPerp Ω K = twinSet Ω K := h21 G Ω K K' z hstd
  rcases h22 G Ω K K' z hstd hperp with hP | hexit
  · have hyp23 : Hyp23Three Ω K K' z := ⟨hstd, hP⟩
    obtain ⟨W, hW, hzW⟩ := hWz G Ω K hs z hU
    rcases h231 G Ω K K' z hyp23 W hW with hE4 | hS4
    · exact hc (h25 G Ω K K' z hyp23 W hW hzW hE4)
    · rcases h233 G Ω K K' z hyp23 W hW hzW hS4 with hZ | hexit
      · exact hc (h24 G Ω K K' z hyp23 W hW hzW hS4 hZ)
      · exact hc hexit
  · exact hc hexit

theorem thm7A3_of_stepsStruct (h : Thm7Steps3) : Thm7A3 :=
  thm7A3_of_steps h.wz h.s21 h.s22 h.s231 h.s233 h.s24 h.s25

end Main

end CFSG.ClassicalInvolution.Q3.Q3T7

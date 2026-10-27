module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3LinAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3UniAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3TD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265

section Certs


set_option linter.unusedSectionVars false

theorem qUFamF3_holds : S265.QUFamF3 := by
  intro p Ω _ _ S B T x b hN hp hty
  subst hp
  have cfg := hN.cfg
  have hb3 : b ^ 3 = 1 := cfg.elem.2 b cfg.hb
  rcases cfg.prop with hF | ⟨-, hTD4, hNI⟩
  · obtain ⟨labK, hkind, m, ⟨hm, hm2, hcan⟩ | ⟨hm, hm3, hcan⟩⟩ :=
      exists_label_of_fieldOn cfg.comp hF hb3 cfg.ipart hty
    · exact qUConcl_of_linear cfg hF hkind hm hm2 hcan
    · exact qUConcl_of_unitary cfg hF hkind hm hm3 hcan
  · exact (false_of_isTD4 cfg.comp cfg.chev hb3 hTD4 hNI (cfg.g2 rfl hTD4) cfg.ipart hty).elim

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end

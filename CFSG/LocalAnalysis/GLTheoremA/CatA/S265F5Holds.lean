module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5LinAsm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5UniAsm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265

section Certs


set_option linter.unusedSectionVars false

theorem qUFamFhi_holds : S265.QUFamFhi := by
  intro p Ω _ _ S B T x b hN hp3 hty
  have cfg := hN.cfg
  have hbp : b ^ p = 1 := cfg.elem.2 b cfg.hb
  rcases cfg.prop with hF | ⟨h3, -, -⟩
  · obtain ⟨labK, hkind, m, hm2, ⟨hpm, hcan⟩ | ⟨hpm, hcan⟩⟩ :=
      exists_label_of_fieldOn_prime cfg.prime cfg.odd hp3 cfg.comp hF hbp cfg.ipart hty
    · exact qUConcl_of_linear_prime cfg hF hkind hm2 hpm hcan
    · exact qUConcl_of_unitary_prime cfg hF hkind hm2 hpm hcan
  · exact absurd h3 hp3

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end

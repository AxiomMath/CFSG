module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremB

section Main


theorem QUCfg.false_of_d4two_outer (hcore : D4Y.D4BigCoreAt) {Ω : Type} [Group Ω] [Finite Ω]
    {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg 3 S B T x b)
    (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isD4two)
    (hout : ¬ ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (Ipart 3 S b : Set Ω),
      chevAut 3 (Ipart 3 S b) ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 (Ipart 3 S b))) : False := by
  obtain ⟨hF, hS8⟩ := cfg.ident_d4two hJ
  exact cfg.false_of_d4eight_outer hcore hF hS8 hout

theorem QUNL.false_of_sp6two_r2 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (h : QUNL 3 S B T x b) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) S9.isSp6two)
    (hr : Nat.card B < 27 * Nat.card (Dgrp b x)) : False :=
  h.false_of_sp68 (h.cfg.ident_sp6two hJ).2 hr

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end

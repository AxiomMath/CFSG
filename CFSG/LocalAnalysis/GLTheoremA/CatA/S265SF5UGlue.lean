module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UResDef
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UE8Case
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA


theorem qsFamF5URes_of_cls (hCls : QSF5UCls) : QSFamF5URes := by
  intro Ω _ _ S B T x D K h hF hZ h25
  obtain ⟨lab, hlab, hlab2, h3, hsmall⟩ := SG.exists_innLabel_of_qsnl_big h
  refine (?_ : False).elim
  have hc := hCls Ω S B T x D K h hF hZ h25 lab hlab hlab2 h3
  have he := false_of_exc_five h hF hZ hlab.labelOf hlab2 h3
  simp only [or_imp] at hc he
  simp only [not_or] at hsmall
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hc
  obtain ⟨e1, e2, e3, e4, e5⟩ := he
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsmall
  cases ht : lab.tag
  · exact c1 ht
  · exact c2 ht
  · exact c3 ht
  · exact c4 ht
  · exact c5 ht
  · exact c6 ht
  · exact e2 ht fun h8 => by rw [ht] at h8; cases h8
  · exact e4 ht fun h8 => by rw [ht] at h8; cases h8
  · by_cases h4 : rk2Ord 5 lab.n = 4
    · exact false_of_e8_rk2Ord_four h hF hlab hlab2 ht h4
    · exact e5 ht fun _ => h4
  · exact e1 ht fun h8 => by rw [ht] at h8; cases h8
  · exact e3 ht fun h8 => by rw [ht] at h8; cases h8
  all_goals contradiction

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end

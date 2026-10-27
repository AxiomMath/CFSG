module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGResCls
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmTwoM
import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_conj_omega)

theorem qsF3ResOmM_holds : QSF3ResOmM := by
  intro Ω _ _ S B T x D K lab h hcat hB hlab hlab2 _ hc
  have hraw := SG.exists_rawDatum_chevAut h hlab
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h4⟩ := hc
  dsimp only at ht h4 hlab2 hraw
  subst ht h4
  have hn1 : 1 ≤ n := hlab2.1
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
  rw [if_neg (by decide), if_neg (by decide)] at hraw
  obtain ⟨F, _, _, hF, b, c, hbc, hs, hnc, Φ, hΦ⟩ := hraw
  haveI := hs
  refine SG.false_of_conj_centralizer h hcat hB hnc Φ hΦ (fun r hr =>
    perfectInLayer_conj_omega (.inr (.inr rfl))
      (statedClassicalModel_omegaMinus 4 n hF b c hbc ⟨Nat.prime_two, hn1, le_rfl⟩)
      Nat.prime_three (by norm_num) (by norm_num) r hr) ?_
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl : n = 1 := by omega
    rintro X hX hXc r hr hr1 ⟨J, hJ, hJc⟩
    exact SG.conclB_rMinus_two F b c (by rw [hF, pow_one]) hbc X hX hXc r hr hr1 J hJ hJc
  · exact fun X hX hXc r hr _ _ =>
      SG.exists_simple_centralizer_omMinus hF hn hbc hX hXc hr

end CFSG.LocalAnalysis.GLTheoremA.S265

end

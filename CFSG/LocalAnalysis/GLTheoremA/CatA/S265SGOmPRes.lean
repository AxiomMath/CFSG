module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGResCls
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGEnd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPConj
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmPFive
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmTwoP
import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265


open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_conj_omega)

theorem qsF3ResOmP_holds : QSF3ResOmP := by
  intro Ω _ _ S B T x D K lab h hcat hB hlab hlab2 h3 hc
  rcases SG.resOmP_rank h3 hc with h4 | h5
  · have hraw := SG.exists_rawDatum_chevAut h hlab
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, -, -⟩ := hc
    dsimp only at ht h4 hlab2 hraw
    subst ht h4
    have hn1 : 1 ≤ n := hlab2.1
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
    rw [if_neg (by decide)] at hraw
    obtain ⟨F, _, _, hF, hs, hnc, Φ, hΦ⟩ := hraw
    haveI := hs
    refine SG.false_of_conj_centralizer h hcat hB hnc Φ hΦ (fun r hr =>
      perfectInLayer_conj_omega (.inr (.inl rfl))
        (statedClassicalModel_omegaPlus 4 n hF ⟨Nat.prime_two, hn1, le_rfl⟩) Nat.prime_three
        (by norm_num) (by norm_num) r hr) ?_
    rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 1 := by omega
      rintro X hX hXc r hr hr1 ⟨J, hJ, hJc⟩
      exact SG.conclB_rPlus_two F (by rw [hF, pow_one]) X hX hXc r hr hr1 J hJ hJc
    · exact fun X hX hXc r hr _ _ =>
        SG.exists_simple_centralizer_omPlus hF hn (by norm_num) hX hXc hr
  · exact SG.false_of_omP_five h hB hlab.labelOf hc.1 hc.2.1 h5

end CFSG.LocalAnalysis.GLTheoremA.S265

end

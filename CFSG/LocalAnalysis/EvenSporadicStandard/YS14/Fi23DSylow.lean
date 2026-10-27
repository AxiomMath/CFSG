module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi23DSylowIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.SylowChar
public import Certificates.Certificate27751
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.EvenSporadicStandard.YS14

theorem involutionFixesElem_fi23D :
    CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem
      CFSG.EvenSporadicStandard.Induction.Fi.Fi23D 16 := by
  obtain ⟨T, hcomm, V, hV, hVX⟩ := Certificates.certificate27751
  exact @involutionFixesElem_of_sylow_large_invs CFSG.EvenSporadicStandard.Induction.Fi.Fi23D
    inferInstance inferInstance ↥(T : Subgroup CFSG.Sporadic.Fi23.J) (Subgroup.toGroup _)
    (fi23D_sylow_iso T) hcomm V hV hVX

end CFSG.EvenSporadicStandard.YS14

module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Co1Seven
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.Sporadic.Schreier.Co1OddInner
public import CFSG.Sporadic.Co2Schreier.FullAut
public import Certificates.Certificate2049
public import Certificates.Certificate2051
public import Certificates.Certificate2053
public import Certificates.Certificate2055
public import Certificates.Certificate2056
public import Certificates.Certificate2057
public import Certificates.Certificate2058
public import Certificates.Certificate2059
public import Certificates.Certificate2060
public import Certificates.Certificate2130
public import Certificates.Certificate2133
public import Certificates.Certificate2135
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2146
public import Certificates.Certificate2147
public import Certificates.Certificate2148
public import Certificates.Certificate2150
public import Certificates.Certificate3024
public import Certificates.Certificate3086
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3120
public import Certificates.Certificate16013
public import Certificates.Certificate16017
public import Certificates.Certificate2054

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallOddCore
  CFSG.EvenSporadicStandard.Solomon78 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

noncomputable def co1GTEquiv :
    CFSG.Blueprint.NativeSporadic.Co1 ≃* ↥GT :=
  @MulEquiv.trans CFSG.Blueprint.NativeSporadic.Co1 ↥GA ↥GT _ _ _ co1MatEquiv eGT

theorem sporPlaneKill_Co1_seven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .Co1 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .Co1 ≃* Spor .Co1 := b
  have hAut := full_automorphisms_inner_of_inputs
      Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner
  have bX : ↥GT ≃* Spor .Co1 := co1GTEquiv.symm.trans b₀
  have h0 : ¬ SporadicOnePair .Co1 7 := by decide
  have hoff := offPair_Co1
  refine @sporPlaneKill_of_noSig_model hOut .Co1 7 (by norm_num) (by norm_num) h0 ↥GT
    (Subgroup.toGroup GT) bX ?_ (NativeSporadic.Carrier .Co1) _ b₀ hoff
  intro R Y hR hR9 hY3 hRY
  exact co1Seven_noSig hAut R hR hR9 Y ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hY3) hRY

theorem sporPair_Co1_seven
    (hOut : SporadicOuterLeTwo) : SporPair .Co1 7 :=
  sporPair_of_planeKill (sporPlaneKill_Co1_seven hOut)

end CFSG.HardMathSupport.Dickson.I271

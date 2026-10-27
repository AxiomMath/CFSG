module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenReplace
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenI112
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenBalance
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenCyclicE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenGood
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenQuasi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenLpEps
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenThreeLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA


theorem s267FactGenOn_of_plane
    {Q : TauCeti.LieTypeIndex → Prop} (h4 : GenPlaneCompOn Q) :
    S267FactGenOn Q :=
  s267FactGenOn_of_steps (genStep1On_of_leaves genGood_holds)
    (genStepCentOn_of_leaves (genCompQuasiOn_holds' Q))
    (genStepI112On_of_leaves (genCompQuasiOn_holds' Q) (genCompChevOn_holds' Q)
      genChevThreeLocal_holds CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds
      CFSG.HardMathSupport.Solomon.Coordinator.tables112More_holds)
    (genStep3On_holds (genCompQuasiOn_holds' Q))
    (genStep4On_of_leaves (fun G _ _ p hp => lBalanceAt_holds G p hp) (genCompQuasiOn_holds' Q))
    (genStep5On_of_leaves h4)
    (genStep6On_of_leaves genGood_holds (genCompQuasiOn_holds' Q) (genCompChevOn_holds' Q)
      genLpEpsLocal_holds S2019.s2019FactAmbAut_holds)

theorem s267FactGen_of_on
    (hc : S267FactGenOn S267ClassicalIdx)
    (he : S267FactGenOn S2019.S2019ExcCoreIdx) : S267FactGen := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hSp hChev hBel hSB hrank hB4 hBC hp3B
  obtain ⟨A, hA, hcard⟩ := exists_elemAbelian_aut_cube hp hSn hperf hBel hB4 hBC
  rcases hChev with hLie | hAmb
  · obtain ⟨i, hi, e⟩ := hLie
    cases i with
    | cyclic r hr => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      obtain ⟨d, hv⟩ := d
      have hchar : d.characteristic = q := hi
      have mk : ∀ Q : TauCeti.LieTypeIndex → Prop, Q d → GenHyp Q p q S B := fun Q hQ =>
        ⟨hp, hp2, hq, hq2, hqp, hK, hSn, hperf, hSp, ⟨⟨d, hv⟩, hchar, hQ, e⟩, hBel, hSB, hrank,
          hB4, hBC, hp3B⟩
      cases d with
      | A n Q => exact hc p q Ω S B (mk _ trivial)
      | twistedA n Q => exact hc p q Ω S B (mk _ trivial)
      | B n Q => exact hc p q Ω S B (mk _ trivial)
      | C n Q => exact hc p q Ω S B (mk _ trivial)
      | D n Q => exact hc p q Ω S B (mk _ trivial)
      | twistedD n Q => exact hc p q Ω S B (mk _ trivial)
      | E6 Q => exact he p q Ω S B (mk _ trivial)
      | E7 Q => exact he p q Ω S B (mk _ trivial)
      | E8 Q => exact he p q Ω S B (mk _ trivial)
      | F4 Q => exact he p q Ω S B (mk _ trivial)
      | G2 Q => exact he p q Ω S B (mk _ trivial)
      | twistedE6 Q => exact he p q Ω S B (mk _ trivial)
      | trialityD4 Q => exact he p q Ω S B (mk _ trivial)
      | suzuki m => exact absurd hchar.symm (by simpa using hq2)
      | reeF4 m => exact absurd hchar.symm (by simpa using hq2)
      | tits => exact absurd hchar.symm (by simpa using hq2)
      | reeG2 m =>
        exfalso
        have hq3 : q = 3 := by simpa using hchar.symm
        have hp3 : p ≠ 3 := fun hp3 => hqp (hq3.trans hp3.symm)
        have hm : 1 ≤ m := by
          have hr := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
          simpa using (TauCeti.LieTypeIndex.inStandardRange_iff _).mp hr
        obtain ⟨e₀⟩ := e
        exact S2019.false_of_reeG2_aut GL83.I713.i_7_13_1_holds hp hp2 hp3 hm e₀
          ⟨TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩, ⟨e₀⟩⟩ hA hcard
  · exfalso
    have hlt := S2019.s2019FactAmbAut_holds p q hp hp2 hq hq2 hqp _ hAmb A hA
    have : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
    omega

theorem s267FactGen_of_planes
    (hc : GenPlaneCompOn S267ClassicalIdx)
    (he : GenPlaneCompOn S2019.S2019ExcCoreIdx) : S267FactGen :=
  s267FactGen_of_on (s267FactGenOn_of_plane hc) (s267FactGenOn_of_plane he)

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

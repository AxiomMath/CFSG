module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07K21
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat27
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAssembly7
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporB7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Comp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FAt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFJBorelTits
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Of
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnHolds
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat24
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat25

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys07Cat29

theorem ys07_of_cat29_inputs
    (hLie : ∀ p : ℕ, p.Prime → p ≠ 2 → KD264KLie p) (hI5 : I107Res5)
    (hR : I264bResidual2) (hI3 : I1431Res3) (h137 : I137Res2) (hPar : I141F.ParityModel) (h2610 : I2610Res) : YS07 :=
  have h137' : I137Res := ⟨h137.chev, I137BorelTits_holds, h137.o5, h137.l3⟩
  ys07_of_cat20_inputs ⟨KD264Gen.kd264SporS_of_B7
      (KD264Gen.B7.kd264SporAt_B_seven
          CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds), hLie⟩ CatB.u4InnRest_holds hI5.toI107Res4.toI107Res3 hR
    fun G _ _ m _ p _ =>
      S9Cat21Inputs.toS9Cat19InputsK hI3
        ⟨i137_of_comp h137'.chev h137'.bt h137'.o5 h137'.l3, i137_3_of_comp h137'.chev h137'.bt h137'.o5 h137'.l3,
          I141F.i141At_of_facts hPar G p,
          CatB.I2610.i2610_of_facts (G := G) h2610.u6 h2610.f4 h2610.te6
            (fun Y _ _ => lBalanceAt_holds Y 3 Nat.prime_three)⟩

end Ys07Cat29

end CFSG.LocalAnalysis.GLTheoremA

end

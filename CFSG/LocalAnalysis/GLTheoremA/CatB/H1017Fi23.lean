module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi22
public import Certificates.Certificate431003
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint


set_option maxRecDepth 100000 in
theorem i1017FiTwoThreeAttained_holds : I1017FiTwoThreeAttained := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi23
  let ψ : NativeSporadic.Carrier .Fi23 ≃*
      (NativeSporadic.seedMonoid 3 253 1 fi23Lift.base.seedA fi23Lift.base.seedB)ˣ :=
    MulEquiv.refl _
  have hlen : fi23Lift.base.outs.length = 5 := by decide
  have key := attained_of_liftCheck (spec3 253) fi23Lift Certificates.certificate431003
    ((e.trans b.symm).trans ψ)
  rw [hlen] at key
  exact key

end CFSG.LocalAnalysis.GLTheoremA.H1017

end

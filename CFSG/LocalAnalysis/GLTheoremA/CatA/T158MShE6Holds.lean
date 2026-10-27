module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6ModelTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6ModelUntw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Head
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Short
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Orbit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Outer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4T2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

section Lang

theorem t158E6ModelOf_holds : T158E6ModelOf := by
  intro G _ _ L J A d b hP hcat
  obtain ⟨i, hi, he⟩ := hcat
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])
  | lie idx =>
    obtain ⟨q, hs, hq | hq⟩ := hi
    · exact t158E6ModelData_untw hP ⟨.lie idx, ⟨q, hs, hq⟩, he⟩
    · exact t158E6ModelData_tw hP ⟨.lie idx, ⟨q, hs, hq⟩, he⟩

theorem t158E6LangData_holds : T158E6LangData :=
  t158E6LangData_of_model t158E6ModelOf_holds

end Lang

section Main

theorem t158CompE6_of_residuals (hK : T171Sh.ExcKernelCompAction) (hO : E6A2OrbitThreeOuter)
    (hR2 : E6D4T2CosetAction) : T158CompE6 :=
  t158CompE6_of t158E6LangData_holds hK d4InnAutDerivedNotFG_holds e6ShortOrbit_holds e6OrbitThreeUnique_holds
    hO hR2

theorem t158CompE6_of_kernel (hK : T171Sh.ExcKernelCompAction) (hR2 : E6D4T2CosetAction) : T158CompE6 :=
  t158CompE6_of_residuals hK e6A2OrbitThreeOuter_holds hR2

theorem t158CompE6_of_kernel_inner (hK : T171Sh.ExcKernelCompAction) (hI : E6D4T2InnerCosetAction) :
    T158CompE6 :=
  t158CompE6_of_kernel hK (e6D4T2CosetAction_of_inner hI)

theorem t158SetupE6_of_kernel_inner (hK : T171Sh.ExcKernelCompAction) (hI : E6D4T2InnerCosetAction) :
    T158SetupE6 :=
  t158SetupE6_of (t158CompE6_of_kernel_inner hK hI)

end Main

end CFSG.LocalAnalysis.GLTheoremA.T158

end

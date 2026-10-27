module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows

public section

set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

open CFSG.LocalAnalysis.GLTheoremA.I1416Rows (sporOrd_eq_sporOrder)

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder sporFactors_prime
  sporFactors_nodup exists_of_prime_pow_dvd_prod)

theorem crow_of_factors
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M)
    (h : ∀ x ∈ sporFactors s, x.1 ≠ 2 → 2 ≤ x.2 → CRow s x.1) (p : ℕ) :
    CRow s p := by
  intro S _ _ he hp hp2
  by_cases hd : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · rw [sporOrd_eq_sporOrder] at hd
    obtain ⟨x, hx, rfl, h2⟩ := exists_of_prime_pow_dvd_prod hp (by norm_num)
      (sporFactors_prime s) (sporFactors_nodup s) hd
    exact h x hx hp2 h2 S he hp hp2
  · exact crow_of_not_sq_dvd hOut hbr hOrd hsB hsM hp hd S he hp hp2

end CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

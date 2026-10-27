module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1415Rows

open CFSG.LocalAnalysis.GLTheoremA.I1416Rows (sporOrd_eq_sporOrder)

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporFactors sporOrder sporFactors_prime
  sporFactors_nodup exists_of_prime_pow_dvd_prod)

theorem arow_of_factors
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hsB : s ≠ .B) (hsM : s ≠ .M)
    (h : ∀ x ∈ sporFactors s, x.1 ≠ 2 → 2 ≤ x.2 →
      x.1 * 1814400 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s → I1415Row s x.1)
    (p : ℕ) : I1415Row s p := by
  intro S _ _ he hp hp2
  by_cases hd2 : p ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · by_cases hd : p * 1814400 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
    · rw [sporOrd_eq_sporOrder] at hd2
      obtain ⟨x, hx, rfl, h2⟩ := exists_of_prime_pow_dvd_prod hp (by norm_num)
        (sporFactors_prime s) (sporFactors_nodup s) hd2
      exact h x hx hp2 h2 hd S he hp hp2
    · exact arow_of_card hOut hbr hOrd hsB hsM hp hd S he hp hp2
  · exact arow_of_not_sq_dvd hOut hbr hOrd hsB hsM hp hd2 S he hp hp2

end CFSG.LocalAnalysis.GLTheoremA.I1415Rows

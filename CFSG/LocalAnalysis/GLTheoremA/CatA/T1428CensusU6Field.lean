module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatDistinct

theorem orderTwistedA_five_two_pow_injective {s r : ℕ} (hs : 1 ≤ s) (hr : 1 ≤ r)
    (h : orderTwistedA 5 (2 ^ s) = orderTwistedA 5 (2 ^ r)) : s = r := by
  let A := orderTwistedA 5 (2 ^ s)
  let Ps := twP 5 (2 ^ s)
  let Pr := twP 5 (2 ^ r)
  let gs := Nat.gcd (5 + 1) (2 ^ s + 1)
  let gr := Nat.gcd (5 + 1) (2 ^ r + 1)
  have h1 : A * gs = 2 ^ (s * 15) * Ps := by
    simpa [A, Ps, gs, show 5 * (5 + 1) / 2 = 15 by norm_num] using
      orderTwistedA_mul_gcd (r := 5) (m := s) (by norm_num) hs
  have h2 : orderTwistedA 5 (2 ^ r) * gr = 2 ^ (r * 15) * Pr := by
    simpa [Pr, gr, show 5 * (5 + 1) / 2 = 15 by norm_num] using
      orderTwistedA_mul_gcd (r := 5) (m := r) (by norm_num) hr
  have h2' : A * gr = 2 ^ (r * 15) * Pr := by
    rw [show A = orderTwistedA 5 (2 ^ r) from h]
    exact h2
  have hPs : Odd Ps := by simpa [Ps] using odd_twP (r := 5) hs
  have hPr : Odd Pr := by simpa [Pr] using odd_twP (r := 5) hr
  have hgs : Odd gs := by simpa [gs] using odd_gcd_twisted (r := 5) hs
  have hgr : Odd gr := by simpa [gr] using odd_gcd_twisted (r := 5) hr
  have hmul : 2 ^ (s * 15) * (Ps * gr) = 2 ^ (r * 15) * (Pr * gs) := by
    calc 2 ^ (s * 15) * (Ps * gr) = (2 ^ (s * 15) * Ps) * gr := (mul_assoc _ _ _).symm
      _ = (A * gs) * gr := by rw [← h1]
      _ = A * (gs * gr) := mul_assoc _ _ _
      _ = A * (gr * gs) := by rw [mul_comm gs gr]
      _ = (A * gr) * gs := (mul_assoc _ _ _).symm
      _ = (2 ^ (r * 15) * Pr) * gs := by rw [h2']
      _ = 2 ^ (r * 15) * (Pr * gs) := mul_assoc _ _ _
  have hEq := (two_pow_mul_odd_inj (hPs.mul hgr) (hPr.mul hgs) hmul).1
  omega

end CFSG.LocalAnalysis.GLTheoremA

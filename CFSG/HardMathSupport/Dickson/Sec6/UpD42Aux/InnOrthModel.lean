module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddCentralizer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

theorem five_le_of_finrank_fixedSpace_eq_eight {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {x : V ≃ₗ[K] V} {n : ℕ}
    (hdim : Module.finrank K V = 2 * n)
    (hfix : Module.finrank K (CFSG.RankThree.PartOne.KCOrthogonal.fixedSpace x) = 8)
    (hx : x ≠ 1) : 5 ≤ n := by
  have hlt := CFSG.HardMathSupport.Malle.E27Lie.finrank_fixedSpace_lt (K := K) (V := V) hx
  rw [hfix, hdim] at hlt
  omega

end CFSG.HardMathSupport.Dickson.Sec6

end

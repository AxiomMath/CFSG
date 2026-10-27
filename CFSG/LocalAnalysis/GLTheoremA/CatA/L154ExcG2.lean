module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldG2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

section Rigidity


theorem frobRootNotConjG2_holds : FrobRootNotConjG2 := by
  intro L _ _ _ p₀ S p R e a i z hp hp2 he hq0 hT _ _ _ _ _ hz
  haveI : ExpChar L 2 := ExpChar.prime Nat.prime_two
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h8 : 8 ≤ 2 ^ (e * p) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e * p) := Nat.pow_le_pow_right (by norm_num)
        (calc 3 = 1 * 3 := by norm_num
          _ ≤ e * p := Nat.mul_le_mul he hp3)
  refine FrobRoot.not_conj_cubic S R (r := 2) (j := e) Nat.prime_two hq0 he (by omega)
    (by omega) ?_ (fun _ => by omega) hT i z hz
  intro h3
  have h2 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  rw [h3] at h2
  omega

end Rigidity

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

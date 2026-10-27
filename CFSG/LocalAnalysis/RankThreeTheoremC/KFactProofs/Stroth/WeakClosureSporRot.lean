module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem wcOn_eleven_of_rotation {K : Type} [Group K] [Finite K] {a b g : K} (ha1 : a ≠ 1)
    (ha : a ^ 11 = 1) (hab : Commute a b) (hga : g * a * g⁻¹ = b) (hgb : g * b * g⁻¹ = a⁻¹)
    (h3 : ¬ 11 ^ 3 ∣ Nat.card K) : WCOn 11 K := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hinv : a⁻¹ = a ^ 10 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha)
  have hgb' : g * b * g⁻¹ = a ^ 10 * b ^ 0 := by rw [hgb, hinv, pow_zero, mul_one]
  exact WCOn.of_conj_pair ha1 ha hab.eq hga (c := 10) (d := 0) hgb' h3 (by decide +revert)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
import CFSG.CGT.PushingUpLit.CGT6M.FiveDataJ2
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.RankThree.Native.ONThreeFusion
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_five_of_data {K : Type} [Group K] [Finite K] {a b g : K} (ha1 : a ≠ 1)
    (ha5 : a ^ 5 = 1) (hab : Commute a b) (hga : g * a * g⁻¹ = b)
    (hgb : g * b * g⁻¹ = (a * b)⁻¹) (h3 : ¬ 5 ^ 3 ∣ Nat.card K) : WCOn 5 K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb5 : b ^ 5 = 1 := by
    rw [← hga, conj_pow, ha5]
    simp
  have hinv : (a * b)⁻¹ = a ^ 4 * b ^ 4 := by
    have ha4 : a⁻¹ = a ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ha5)
    have hb4 : b⁻¹ = b ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hb5)
    rw [mul_inv_rev, ha4, hb4]
    exact (hab.pow_pow 4 4).symm.eq
  rw [hinv] at hgb
  exact WCOn.of_conj_pair ha1 ha5 hab.eq hga (c := 4) (d := 4) hgb h3 (by decide +revert)

theorem wcOn_J2_five_of_equiv {Q : Type} [Group Q] [Finite Q]
    (hQ : IsSporadic Q .J2) : WCOn 5 Q := by
  obtain ⟨a, b, g, ha1, ha5, hab, hga, hgb, h3⟩ := CFSG.CGT.PushingUpLit.CGT6M.linesData_J2 hQ
  exact wcOn_five_of_data ha1 ha5 hab hga hgb h3

theorem wcOn_J2_five [Finite (Carrier .J2)] :
    WCOn 5 (Carrier .J2) :=
  wcOn_J2_five_of_equiv ⟨MulEquiv.refl _⟩

theorem wcSporadicAt_J2
    [Finite (Carrier .J2)] : WCSporadicAt .J2 := by
  refine wcSporadicAt_of_card .J2 (N := 604800) CFSG.Sporadic.J2.card_J2 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
    obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    exact WCOn.of_cubic hx hy hz hc
  · exact wcOn_J2_five
  · exfalso; norm_num at hdvd

theorem wcOn_ON_three
    [Finite (Carrier .ONan)] : WCOn 3 (Carrier .ONan) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact WCOn.of_conj_elements fun x y hx hy => CFSG.RankThree.Native.onThree_fusion hx hy

theorem wcOn_ON_seven [Finite (Carrier .ONan)] :
    WCOn 7 (Carrier .ONan) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_ON

theorem wcSporadicAt_ON
    [Finite (Carrier .ONan)] : WCSporadicAt .ONan := by
  refine wcSporadicAt_of_card .ONan (N := 460815505920) CFSG.Sporadic.ON.card_ON ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_ON_three
  · exfalso; norm_num at hdvd
  · exact wcOn_ON_seven
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

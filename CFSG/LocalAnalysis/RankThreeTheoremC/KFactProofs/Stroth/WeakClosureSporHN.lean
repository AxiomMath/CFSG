module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.Faithful

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

set_option maxRecDepth 4000

private theorem wcOn_JH_three
    [Finite ↥CFSG.Sporadic.HNSchreier.JH] : WCOn 3 ↥CFSG.Sporadic.HNSchreier.JH := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨S, hS⟩, hcard, -, -, hcnt, -⟩ :=
    CFSG.Sporadic.HNSchreier.ctuc_hn_Sylow_three_complete_element_coverage
  have hnot : ¬ IsMulCommutative (S : Subgroup ↥CFSG.Sporadic.HNSchreier.JH) := by
    rw [hS]
    exact not_isMulCommutative_of_order_count (k := 6) (m := 512) (by rw [hcard]; norm_num) hcnt
      (by norm_num)
  exact WCOn.of_sylow S fun hc => absurd hc hnot

theorem wcOn_HN_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.HN] : WCOn 3 CFSG.Blueprint.NativeSporadic.HN := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥CFSG.Sporadic.HNSchreier.JH :=
    Finite.of_equiv _ CFSG.Sporadic.HNSchreier.hnEquivJ.toEquiv
  exact WCOn.of_mulEquiv (K := CFSG.Blueprint.NativeSporadic.HN)
    (L := ↥CFSG.Sporadic.HNSchreier.JH) CFSG.Sporadic.HNSchreier.hnEquivJ wcOn_JH_three

theorem wcOn_HN_three
    [Finite (Carrier .HN)] : WCOn 3 (Carrier .HN) :=
  wcOn_HN_three_aux

theorem wcSporadicAt_HN
    [Finite (Carrier .HN)] : WCSporadicAt .HN := by
  refine wcSporadicAt_of_card .HN (N := 273030912000000) CFSG.Sporadic.HNSchreier.card_HN ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_HN_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_HN
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporQuot
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
import CFSG.Sporadic.Th.Max3.AllConjFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

set_option maxRecDepth 4000

private theorem wcOn_J_three
    [Finite ↥CFSG.Sporadic.Th.J] :
    WCOn 3 ↥CFSG.Sporadic.Th.J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨κ, -, -⟩, -⟩ := CFSG.Sporadic.Th.Max3.max3_alternating_quotient
  exact wcOn_of_surj_sylow (A := ↥(alternatingGroup (Fin 9))) CFSG.Sporadic.Th.Max3.M
    (κ.toMonoidHom.comp (QuotientGroup.mk' _))
    (κ.surjective.comp (QuotientGroup.mk'_surjective _)) alt9_sylow_three_not_comm

theorem wcOn_Th_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.Th] :
    WCOn 3 CFSG.Blueprint.NativeSporadic.Th := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥CFSG.Sporadic.Th.J := Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.toEquiv
  exact WCOn.of_mulEquiv (K := CFSG.Blueprint.NativeSporadic.Th)
    (L := ↥CFSG.Sporadic.Th.J) CFSG.Sporadic.Th.thEquivJ wcOn_J_three

theorem wcOn_Th_three
    [Finite (Carrier .Th)] : WCOn 3 (Carrier .Th) :=
  wcOn_Th_three_aux

theorem wcOn_Th_five [Finite (Carrier .Th)] :
    WCOn 5 (Carrier .Th) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Th

theorem wcSporadicAt_Th_of_seven
    [Finite (Carrier .Th)] (h7 : WCOn 7 (Carrier .Th)) :
    WCSporadicAt .Th := by
  refine wcSporadicAt_of_card .Th (N := 90745943887872000) ?_ ?_
  · exact (Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv).trans
      CFSG.Sporadic.Th.Max3.natCard_J
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Th_three
  · exact wcOn_Th_five
  · exact h7
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

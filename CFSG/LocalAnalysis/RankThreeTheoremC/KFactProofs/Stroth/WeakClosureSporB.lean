module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporHeis

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_B_three_aux
    [Finite CFSG.Blueprint.NativeSporadic.B] : WCOn 3 CFSG.Blueprint.NativeSporadic.B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact WCOn.of_hasNoncommPair (hasNoncommPair_of_commData (G := CFSG.Blueprint.NativeSporadic.B)
    Nat.prime_three CFSG.Monster.B.Pinned.commData_three (i := 0) (j := 1) rfl)

theorem wcOn_B_three
    [Finite (Carrier .B)] : WCOn 3 (Carrier .B) :=
  wcOn_B_three_aux

theorem wcOn_B_five_aux
    [Finite CFSG.Blueprint.NativeSporadic.B] : WCOn 5 CFSG.Blueprint.NativeSporadic.B := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact WCOn.of_hasNoncommPair (hasNoncommPair_of_commData (G := CFSG.Blueprint.NativeSporadic.B)
    Nat.prime_five CFSG.Monster.B.Pinned.commData_five (i := 0) (j := 1) rfl)

theorem wcOn_B_five
    [Finite (Carrier .B)] : WCOn 5 (Carrier .B) :=
  wcOn_B_five_aux

theorem wcSporadicAt_B_of_seven
    [Finite (Carrier .B)] (h7 : WCOn 7 (Carrier .B)) : WCSporadicAt .B := by
  have hN : Nat.card CFSG.Blueprint.NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [CFSG.Monster.Existence.card_nativeB]
    decide
  refine wcSporadicAt_of_card .B (N := 4154781481226426191177580544000000) hN ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 4154781481226426191177580544000000 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_B_three
  · exact wcOn_B_five
  · exact h7
  all_goals (exfalso; norm_num at hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

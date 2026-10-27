module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11TransProved
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.RankThree.Asc83Table.M22
import CFSG.RankThree.Asc83Table.M23
import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_M11_three
    [Finite (Carrier .M11)] : WCOn 3 (Carrier .M11) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact WCOn.of_normalizer_transitive fun P a b ha hb ha1 hb1 =>
    CFSG.LocalAnalysis.RankThreeTheoremC.m11SylowTransitive_proved (Carrier .M11) ⟨e⟩ P a b ha hb
      ha1 hb1

theorem wcSporadicAt_M11
    [Finite (Carrier .M11)] : WCSporadicAt .M11 := by
  refine wcSporadicAt_of_card .M11 (N := 7920) CFSG.Sporadic.Mathieu.card_M11 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_M11_three
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd

theorem wcOn_M12_three [Finite (Carrier .M12)] :
    WCOn 3 (Carrier .M12) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact WCOn.of_hasNoncommPair
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc)

theorem wcSporadicAt_M12
    [Finite (Carrier .M12)] : WCSporadicAt .M12 := by
  refine wcSporadicAt_of_card .M12 (N := 95040) CFSG.Sporadic.Mathieu.card_M12 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_M12_three
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd

theorem wcOn_M22_three [Finite (Carrier .M22)] :
    WCOn 3 (Carrier .M22) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  open CFSG.RankThree.Asc83Table.M22 in
  exact WCOn.of_square_witness (x := X) (y := Y) (h := GI) X_cube Y_cube XY_comm.eq
    (by
      have := E.card
      rw [E_a, E_b] at this
      exact this.trans (by norm_num))
    (by
      show ¬ 3 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22
      rw [CFSG.Sporadic.Mathieu.card_M22]
      norm_num)
    (a := 0) (b := 1) (c := 2) (d := 0) GI_X GI_Y (by decide +revert)

theorem wcSporadicAt_M22 [Finite (Carrier .M22)] :
    WCSporadicAt .M22 := by
  refine wcSporadicAt_of_card .M22 (N := 443520) CFSG.Sporadic.Mathieu.card_M22 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_M22_three
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd

theorem wcOn_M23_three [Finite (Carrier .M23)] :
    WCOn 3 (Carrier .M23) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  open CFSG.RankThree.Asc83Table.M23 in
  exact WCOn.of_square_witness (x := X) (y := Y) (h := GR) X_cube Y_cube XY_comm.eq
    (by
      have := E.card
      exact this.trans (by norm_num))
    (by
      show ¬ 3 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M23
      rw [CFSG.Sporadic.Schreier.m23_card]
      norm_num)
    (a := 0) (b := 1) (c := 1) (d := 2) GR_X GR_Y (by decide +revert)

theorem wcSporadicAt_M23 [Finite (Carrier .M23)] :
    WCSporadicAt .M23 := by
  refine wcSporadicAt_of_card .M23 (N := 10200960) CFSG.Sporadic.Schreier.m23_card ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_M23_three
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd

theorem wcOn_M24_three [Finite (Carrier .M24)] :
    WCOn 3 (Carrier .M24) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact WCOn.of_hasNoncommPair
    (CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc)

theorem wcSporadicAt_M24
    [Finite (Carrier .M24)] : WCSporadicAt .M24 := by
  refine wcSporadicAt_of_card .M24 (N := 244823040) CFSG.Sporadic.Mathieu.card_M24 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_M24_three
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd
  · exfalso; norm_num at hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

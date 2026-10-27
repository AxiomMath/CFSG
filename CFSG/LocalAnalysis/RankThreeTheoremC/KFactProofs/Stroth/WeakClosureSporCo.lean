module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.Sporadic.Co2Cert.Cert
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofMcL
import CFSG.Sporadic.HNSchreier.SplitExt

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem wcOn_McL_three_of_equiv
    {X : Type} [Group X] [Finite X]
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.McL) : WCOn 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine WCOn.of_not_isMulCommutative fun P hcomm => ?_
  obtain ⟨s, hs, -, t, ht, hst⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof.exists_noncentral_McL e P
  exact hst (congrArg Subtype.val (hcomm.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩))

theorem wcOn_McL_three
    [Finite (Carrier .McL)] : WCOn 3 (Carrier .McL) := by
  haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hcen : Subgroup.center CFSG.Blueprint.NativeSporadic.McL = ⊥ :=
    CFSG.Sporadic.HNSchreier.center_eq_bot_of_simple
      (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  exact wcOn_McL_three_of_equiv (X := CFSG.Blueprint.NativeSporadic.McL)
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)

theorem wcSporadicAt_McL
    [Finite (Carrier .McL)] : WCSporadicAt .McL := by
  refine wcSporadicAt_of_card .McL (N := 898128000) CFSG.Sporadic.McL.card_McL ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_McL_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_McL
  all_goals (exfalso; norm_num at hdvd)

section Co2

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Sporadic.Co2Cert

theorem wcOn_co2P_three :
    WCOn 3 ↥CFSG.Sporadic.Co2Cert.co2P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine WCOn.of_self_centralizing (D := Tg) (IsPGroup.of_card (n := 4)
    (by rw [card_Tg]; norm_num)) ?_ factorization_card_co2P_three (by rw [card_Tg]; norm_num)
  intro x hx
  have hxD : (x : Equiv.Perm (Fin 2300)) ∈ Dg := by
    rw [← centralizer_Dg_inf_eq]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun z hz => ?_, x.2⟩
    have := hx ⟨z, Dg_le hz⟩ (Subgroup.mem_subgroupOf.2 hz)
    exact (congrArg Subtype.val this).symm
  exact Subgroup.mem_subgroupOf.2 hxD

theorem wcOn_Co2_three
    [Finite (Carrier .Co2)] :
    WCOn 3 (Carrier .Co2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact WCOn.of_mulEquiv co2PermEquiv wcOn_co2P_three

theorem wcSporadicAt_Co2
    [Finite (Carrier .Co2)] : WCSporadicAt .Co2 := by
  refine wcSporadicAt_of_card .Co2 (N := 42305421312000) CFSG.Sporadic.Co2.card_Co2 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Co2_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co2
  all_goals (exfalso; norm_num at hdvd)

end Co2

section Co3

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Sporadic.Schreier.Co3

theorem wcOn_co3P_three :
    WCOn 3 ↥co3P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine WCOn.of_small_centralizer (y := ⟨yPerm, yPerm_mem⟩) (Subtype.ext yPerm_pow) (f := 7)
    factorization_card_co3P_three (m := 4536) ?_ (by norm_num)
  rw [card_centralizer_subgroup co3P ⟨yPerm, yPerm_mem⟩]
  exact Cy_eq.1 ▸ Cy_eq.2

theorem wcOn_Co3_three
    [Finite (Carrier .Co3)] :
    WCOn 3 (Carrier .Co3) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact WCOn.of_mulEquiv co3PermEquiv wcOn_co3P_three

theorem wcSporadicAt_Co3
    [Finite (Carrier .Co3)] : WCSporadicAt .Co3 := by
  refine wcSporadicAt_of_card .Co3 (N := 495766656000) CFSG.Sporadic.Co3.card_Co3 ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hq2
  · exact wcOn_Co3_three
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co3
  all_goals (exfalso; norm_num at hdvd)

end Co3

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

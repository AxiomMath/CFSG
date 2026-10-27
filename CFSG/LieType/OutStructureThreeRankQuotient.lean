module

public import CFSG.LieType.OutStructureThreeRankLarge
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Reduce
public import CFSG.RankThree.PartOne.SLB4A.TypeA
public import CFSG.RankThree.PartOne.SLB4A.TypeSU

public section

namespace CFSG.LieType.OutStructure

theorem exists_elemAbelian_sixteen_of_classical {S : Type} [Group S] [Finite S]
    {t : CFSG.Open.StatedLieTag} {N r f : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel S t N r f) (ht : t = .PSL ∨ t = .PSU) (hN : 8 ≤ N) :
    ∃ V : Subgroup S, CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 4 := by
  have hr : r.Prime := hcl.1.1
  have hcl' := hcl
  have : Fact r.Prime := ⟨hr⟩
  have key : ∃ U : Subgroup S, CFSG.IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
    rcases ht with rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl'
      refine CFSG.RankThree.PartOne.SLB4A.exists_of_mulEquiv e ?_
      rcases hr.eq_two_or_odd' with rfl | hodd
      · have : Fintype K := Fintype.ofFinite K
        have : CharP K 2 := charP_of_card_eq_prime_pow (f := f)
          (by rw [← Nat.card_eq_fintype_card, hK])
        exact CFSG.RankThree.PartOne.SLB4A.exists_two_pow_five_psl_even N (by omega)
      · refine CFSG.RankThree.PartOne.SLB4A.exists_two_pow_five_psl_odd N (by omega)
          (CFSG.RankThree.PartOne.SLB4A.neg_one_ne_one_of_card_odd K ?_)
        rw [hK]
        exact Nat.odd_iff.1 hodd.pow
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl'
      refine CFSG.RankThree.PartOne.SLB4A.exists_of_mulEquiv e ?_
      rcases hr.eq_two_or_odd' with rfl | hodd
      · have : Fintype K := Fintype.ofFinite K
        have : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
          (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
        exact CFSG.RankThree.PartOne.SLB4A.exists_two_pow_five_psu_even
          (Nat.pos_of_ne_zero (pow_ne_zero _ hr.ne_zero)) N (by omega)
      · refine CFSG.RankThree.PartOne.SLB4A.exists_two_pow_five_psu_odd hodd.pow N (by omega)
          (CFSG.RankThree.PartOne.SLB4A.neg_one_ne_one_of_card_odd K ?_)
        rw [hK]
        exact Nat.odd_iff.1 hodd.pow.pow
  obtain ⟨U, hU, hUc⟩ := key
  have h5 : 5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 U).mp hU) hUc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, -, hV, hVc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2)
    (H := (⊤ : Subgroup S)) (k := 4) (by omega)
  exact ⟨V, hV, hVc⟩

theorem four_le_pRank_three_of_surjective_classical
    (hGA : CFSG.Open.GriessAllModelsStatement) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) {t : CFSG.Open.StatedLieTag} {N r f : ℕ}
    (hcl : CFSG.Open.StatedClassicalModel S t N r f) (ht : t = .PSL ∨ t = .PSU) (hN : 8 ≤ N)
    {X : Type} [Group X] [Finite X] (π : X →* S) (hπ : Function.Surjective π) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨V, hV, hVc⟩ := exists_elemAbelian_sixteen_of_classical hcl ht hN
  refine CFSG.HardMathSupport.Solomon.Coordinator.i1021_main hnab Nat.prime_three (by norm_num)
    (by norm_num) hV hVc ?_ (Nat.card X) X le_rfl π hπ
  intro X1 _ _ ψ hψ hcomm hker _
  have hZ : ψ.ker = Subgroup.center X1 := by
    refine le_antisymm hker fun z hz => ?_
    have hψz : ψ z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i1021_center_eq_bot hnab, Subgroup.mem_bot]
      at hψz
    exact hψz
  let e : X1 ⧸ Subgroup.center X1 ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact four_le_pRank_three_of_classical_large hGA ⟨hcomm, e.isSimpleGroup⟩
    (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hcl) ht hN

end CFSG.LieType.OutStructure

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourExistenceCyclic

public section

open CFSG.Open CFSG.LargeEvenClassification.Helpers

namespace CFSG.ProperTwoGeneratedCore

universe u

theorem cyclic_index_two_rank_bound {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [IsCyclic H] (hindex : H.index ≤ 2) : twoRank G ≤ 2 := by
  have hpositive : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hnormal : H.Normal := by
    have hcases : H.index = 1 ∨ H.index = 2 := by omega
    rcases hcases with hone | htwo
    · exact Subgroup.normal_of_index_eq_one hone
    · exact Subgroup.normal_of_index_eq_two htwo
  let : H.Normal := hnormal
  obtain ⟨E, _, hE, hcard⟩ := pRank_witness (by decide : 1 < 2) (⊤ : Subgroup G)
  have hpE : IsPGroup 2 E := IsPGroup.of_card hcard
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := @mul_comm' E _ hE.1 }
  have hgeneratorRank : pGeneratorRank 2 E ≤ 2 := by
    obtain ⟨generators, hgenerates, hcardGenerators⟩ :=
      cyclic_index_two_subgroup_generators H hindex E
    exact (pGeneratorRank_le_generators Nat.prime_two hpE generators hgenerates).trans
      hcardGenerators
  rw [elementary_pGeneratorRank_eq_log_card Nat.prime_two
    (fun e : E => Subtype.ext (hE.2 e e.property)), hcard, Nat.log_pow (by decide : 1 < 2)]
      at hgeneratorRank
  exact hgeneratorRank

theorem no_normal_four_abelian_normal_cyclic {P : Type u} [Group P] [Finite P]
    (htwo : IsPGroup 2 P)
    (hnoFour : ∀ V : Subgroup P, V.Normal → IsElemAbelian 2 V → Nat.card V ≠ 4)
    (A : Subgroup P) [A.Normal] (hcommutative : IsMulCommutative A) : IsCyclic A := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' A _ hcommutative }
  let E := normalElementarySquareKernel A hcommutative
  let : E.Normal := normalElementarySquareKernel_normal A hcommutative
  have hE := normalElementarySquareKernel_elementary A hcommutative
  have hcardSmall : Nat.card E < 4 := by
    by_contra hlarge
    obtain ⟨V, hVnormal, _, hVelementary, hVcard⟩ :=
      normal_elementary_subgroup_order 2 Nat.prime_two htwo E hE (by norm_num; omega)
    exact hnoFour V hVnormal hVelementary (by norm_num at hVcard; exact hVcard)
  obtain ⟨rank, hcard⟩ := (htwo.to_subgroup E).exists_card_eq
  have hrank : rank ≤ 1 := by
    by_contra hlarge
    have hpower : 2 ^ 2 ≤ 2 ^ rank := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hcard] at hpower
    norm_num at hpower
    omega
  have hkernelCard : Nat.card (powMonoidHom 2 : A →* A).ker = 2 ^ rank := by
    exact (Subgroup.card_map_of_injective Subtype.val_injective).symm.trans hcard
  have hgeneratorRank : pGeneratorRank 2 A = rank := by
    unfold pGeneratorRank
    rw [commutative_frattini_card_eq_power_kernel Nat.prime_two (htwo.to_subgroup A),
      hkernelCard]
    exact Nat.log_pow (by decide : 1 < 2) rank
  exact pGroup_generator_rank_one_cyclic Nat.prime_two (htwo.to_subgroup A)
    (hgeneratorRank ▸ hrank)

theorem high_two_rank_normal_four (P : Type u) [Group P] [Finite P]
    (htwo : IsPGroup 2 P) (hrank : 3 ≤ CFSG.Open.twoRank P) :
    ∃ V : Subgroup P, V.Normal ∧ CFSG.Open.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  by_contra hnone
  have hnoFour : ∀ V : Subgroup P, V.Normal → IsElemAbelian 2 V → Nat.card V ≠ 4 := by
    intro V hnormal helementary hcard
    exact hnone ⟨V, hnormal, helementary, hcard⟩
  have hcyclic : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → IsCyclic A := by
    intro A hnormal hcommutative
    let : A.Normal := hnormal
    exact no_normal_four_abelian_normal_cyclic htwo hnoFour A hcommutative
  obtain ⟨H, _, hHcyclic, hindex⟩ := cyclic_abelian_normal_index_two P htwo hcyclic
  let : IsCyclic H := hHcyclic
  have hbound := cyclic_index_two_rank_bound H hindex
  omega

end CFSG.ProperTwoGeneratedCore

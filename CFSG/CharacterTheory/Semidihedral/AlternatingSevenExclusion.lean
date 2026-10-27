module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingModel
public import CFSG.CharacterTheory.Semidihedral.CentralizerAlternatives

public section

namespace CFSG.Semidihedral.AlternatingSevenExclusion

theorem symmetric_seven_no_order_eight (g : Equiv.Perm (Fin 7)) : orderOf g ≠ 8 := by
  intro horder
  have hcycles : ∀ n ∈ g.cycleType, n ∣ 4 := by
    intro n hn
    have hbound : n ≤ 7 := (Multiset.le_sum_of_mem hn).trans (by
      simpa using g.sum_cycleType_le)
    have hdivides : n ∣ 8 := by
      simpa only [g.lcm_cycleType, horder] using Multiset.dvd_lcm hn
    interval_cases n <;> norm_num at *
  have hdivides : orderOf g ∣ 4 := by
    rw [← g.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr hcycles
  norm_num [horder] at hdivides

theorem factorization_5040_two : (5040 : ℕ).factorization 2 = 4 := by
  rw [show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num,
    Nat.factorization_mul_apply_of_coprime ((by decide : Nat.Coprime 2 315).pow_left 4),
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315), Nat.add_zero]

theorem symmetric_seven_sylow_card (S : Sylow 2 (Equiv.Perm (Fin 7))) :
    Nat.card S = 16 := by
  rw [S.card_eq_multiplicity, Nat.card_perm]
  norm_num only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  rw [factorization_5040_two]
  norm_num

theorem symmetric_seven_card : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]

theorem alternating_seven_card : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have hcard := (alternatingGroup (Fin 7)).card_mul_index
  rw [alternatingGroup.index_eq_two, symmetric_seven_card] at hcard
  omega

theorem dihedral_sylow_not_symmetric_seven {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (m : ℕ) (hm : 2 ≤ m)
    (eS : (S : Subgroup G) ≃* DihedralGroup (2 ^ (m - 1)))
    (e : G ≃* Equiv.Perm (Fin 7)) : False := by
  have hGcard : Nat.card G = 5040 :=
    (Nat.card_congr e.toEquiv).trans symmetric_seven_card
  have hScard : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity, hGcard, factorization_5040_two]
    norm_num
  have hparameter : m = 4 := by
    have hpow : 2 ^ m = 2 ^ 4 := by
      rw [← CentralizerAlternatives.card_of_dihedral_equiv m (by omega) eS, hScard]
      norm_num
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
  let r : S := eS.symm (DihedralGroup.r 1)
  have hr : orderOf r = 8 := by
    rw [← eS.orderOf_eq r]
    simp only [r, eS.apply_symm_apply, DihedralGroup.orderOf_r_one]
    norm_num [hparameter]
  have himage : orderOf (e r.val) = 8 := by
    rw [e.orderOf_eq]
    exact (orderOf_injective (S : Subgroup G).subtype Subtype.val_injective r).trans hr
  exact symmetric_seven_no_order_eight (e r.val) himage

theorem native_dihedral_index_two_excludes_alternating_seven_layer
    {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup (CFSG.ComponentClassification.GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : CFSG.ComponentClassification.GeneralizedFitting.subgroup G,
      a * b ≠ b * a)
    (S : Sylow 2 G) (m : ℕ) (hm : 2 ≤ m)
    (eS : (S : Subgroup G) ≃* DihedralGroup (2 ^ (m - 1)))
    (J : Subgroup G) (hJ : J.index = 2)
    (hFJ : CFSG.ComponentClassification.GeneralizedFitting.subgroup G ≤ J) :
    ¬ Nonempty (CFSG.ComponentClassification.GeneralizedFitting.subgroup G ≃*
      alternatingGroup (Fin 7)) := by
  rintro ⟨θ⟩
  obtain ⟨ρ, hρ, _, _, _, hindex⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternating.generalizedFitting_permutation_model
      hnonab (Or.inr (by decide : 7 ≤ 7)) θ
  have hFindex : (CFSG.ComponentClassification.GeneralizedFitting.subgroup G).index = 2 := by
    have hdivides : 2 ∣ (CFSG.ComponentClassification.GeneralizedFitting.subgroup G).index := by
      rw [← hJ]
      exact Subgroup.index_dvd_of_le hFJ
    have hpos : 0 < (CFSG.ComponentClassification.GeneralizedFitting.subgroup G).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.le_antisymm hindex (Nat.le_of_dvd hpos hdivides)
  have hFcard : Nat.card (CFSG.ComponentClassification.GeneralizedFitting.subgroup G) = 2520 :=
    (Nat.card_congr θ.toEquiv).trans alternating_seven_card
  have hGcard : Nat.card G = 5040 := by
    rw [← (CFSG.ComponentClassification.GeneralizedFitting.subgroup G).card_mul_index,
      hFcard, hFindex]
  have hbijective : Function.Bijective ρ :=
    (Nat.bijective_iff_injective_and_card ρ).mpr
      ⟨hρ, hGcard.trans symmetric_seven_card.symm⟩
  exact dihedral_sylow_not_symmetric_seven S m hm eS (MulEquiv.ofBijective ρ hbijective)

theorem dihedral_index_two_excludes_alternating_seven_layer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup (CFSG.generalizedFitting G)]
    (hnonab : ∃ a b : CFSG.generalizedFitting G, a * b ≠ b * a)
    (S : Sylow 2 G) (m : ℕ) (hm : 2 ≤ m)
    (eS : (S : Subgroup G) ≃* DihedralGroup (2 ^ (m - 1)))
    (J : Subgroup G) (hJ : J.index = 2) (hFJ : CFSG.generalizedFitting G ≤ J) :
    ¬ Nonempty (CFSG.generalizedFitting G ≃* alternatingGroup (Fin 7)) := by
  have hF := CFSG.generalizedFitting_eq_componentClassification G
  let : IsSimpleGroup (CFSG.ComponentClassification.GeneralizedFitting.subgroup G) := by
    rw [← hF]
    infer_instance
  rw [hF] at hnonab hFJ ⊢
  exact native_dihedral_index_two_excludes_alternating_seven_layer hnonab S m hm eS J hJ hFJ

end CFSG.Semidihedral.AlternatingSevenExclusion

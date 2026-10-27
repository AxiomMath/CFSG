module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeAltOrder
public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open TauCeti CFSG.Open

theorem center_eq_bot_of_isSimpleGroup {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hb
  · exfalso
    have hcomm : IsMulCommutative G := ⟨⟨fun a b => (Subgroup.mem_center_iff.1
      (ht ▸ Subgroup.mem_top a) b).symm⟩⟩
    let _ : CommGroup G := { ‹Group G› with mul_comm := hcomm.is_comm.comm }
    exact h (Group.is_simple_iff_prime_card.mp inferInstance)

theorem odd_two_pow_sub_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  obtain ⟨k, hk⟩ : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have : 0 < 2 ^ m := by positivity
  exact ⟨k - 1, by omega⟩

theorem odd_two_pow_add_one {m : ℕ} (hm : 1 ≤ m) : Odd (2 ^ m + 1) := by
  obtain ⟨k, hk⟩ : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  exact ⟨k, by omega⟩

theorem odd_prod_four_pow_sub_one (m : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  obtain ⟨k, hk⟩ : 4 ∣ 4 ^ i := dvd_pow_self 4 (by omega)
  have : 0 < 4 ^ i := by positivity
  exact ⟨2 * k - 1, by omega⟩

theorem factorization_two_pow_mul_of_odd {e c : ℕ} (hc : Odd c) :
    (2 ^ e * c).factorization 2 = e := by
  rw [Nat.factorization_mul (by positivity) hc.pos.ne', Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hc.not_two_dvd_nat]
  simp

theorem isSimpleGroup_lie_typeD_two (m : ℕ) (d : ValidLieTypeIndex) (q : PrimePower)
    (hq : q.card = 2) (hd : d.1 = .D m q) : IsSimpleGroup (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hm : 4 ≤ m := four_le_of_valid_D hv
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp
    (MulEquiv.refl _)
  rw [hp, he] at hmod
  obtain ⟨-, K, _, _, _, ⟨e⟩⟩ := hmod
  have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
    (K := K) (n := m) (by omega)
  change IsSimpleGroup (ValidLieTypeIndex.Group ⟨.D m q, hv⟩)
  exact e.isSimpleGroup

theorem isSimpleGroup_lie_twistedD_two (m : ℕ) (d : ValidLieTypeIndex) (q : PrimePower)
    (hq : q.card = 2) (hd : d.1 = .twistedD m q) : IsSimpleGroup (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hm : 4 ≤ m := four_le_of_valid_twistedD hv
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp
    (MulEquiv.refl _)
  rw [hp, he] at hmod
  obtain ⟨-, K, _, _, _, b, c, hbc, ⟨e⟩⟩ := hmod
  have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
    (K := K) (n := m) (b := b) (c := c) (by omega) hbc
  change IsSimpleGroup (ValidLieTypeIndex.Group ⟨.twistedD m q, hv⟩)
  exact e.isSimpleGroup

theorem isSimpleGroup_lie_twistedA_three_two (d : ValidLieTypeIndex) (q : PrimePower)
    (hq : q.card = 2) (hd : d.1 = .twistedA 3 q) : IsSimpleGroup (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  rw [hp, he] at hmod
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK (3 + 1)
    (by norm_num) (by simp)
  change IsSimpleGroup (ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩)
  exact e.isSimpleGroup

theorem not_prime_of_two_le_factorization {n : ℕ} (h : 2 ≤ n.factorization 2) : ¬ n.Prime := by
  intro hp
  have h4 : 4 ∣ n := by
    refine dvd_trans ?_ (Nat.ordProj_dvd n 2)
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_dvd_pow 2 h
  rcases (Nat.dvd_prime hp).1 h4 with h1 | h1
  · omega
  · exact absurd (h1 ▸ hp) (by norm_num)

theorem two_le_mul_pred {m : ℕ} (hm : 4 ≤ m) : 2 ≤ m * (m - 1) := by
  have := Nat.mul_le_mul hm (show 3 ≤ m - 1 by omega)
  omega

theorem tauCetiOrthFacts_holds : TauCetiOrthFacts := by
  refine ⟨?_, ?_⟩
  · rintro m d ⟨q, hq, hd | hd⟩
    · have hm : 4 ≤ m := four_le_of_valid_D (hd ▸ d.2)
      have hs := isSimpleGroup_lie_typeD_two m d q hq hd
      have hc := card_lie_typeD_two m d q hq hd
      have hodd : Odd ((2 ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) :=
        (odd_two_pow_sub_one (by omega)).mul (odd_prod_four_pow_sub_one m)
      have hf : (Nat.card (CFSGIndex.lie d).Group).factorization 2 = m * (m - 1) := by
        rw [hc, mul_assoc]
        exact factorization_two_pow_mul_of_odd hodd
      exact ⟨center_eq_bot_of_isSimpleGroup
        (not_prime_of_two_le_factorization (hf ▸ two_le_mul_pred hm)), hf⟩
    · have hm : 4 ≤ m := four_le_of_valid_twistedD (hd ▸ d.2)
      have hs := isSimpleGroup_lie_twistedD_two m d q hq hd
      have hc := card_lie_twistedD_two m d q hq hd
      have hodd : Odd ((2 ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1)) :=
        (odd_two_pow_add_one (by omega)).mul (odd_prod_four_pow_sub_one m)
      have hf : (Nat.card (CFSGIndex.lie d).Group).factorization 2 = m * (m - 1) := by
        rw [hc, mul_assoc]
        exact factorization_two_pow_mul_of_odd hodd
      exact ⟨center_eq_bot_of_isSimpleGroup
        (not_prime_of_two_le_factorization (hf ▸ two_le_mul_pred hm)), hf⟩
  · rintro d ⟨q, hq, hd⟩
    have hs := isSimpleGroup_lie_twistedA_three_two d q hq hd
    have hc := card_lie_twistedA_three_two d q hq hd
    refine ⟨center_eq_bot_of_isSimpleGroup ?_, hc⟩
    rw [hc]
    norm_num

end CFSG.HardMathSupport.Curtis.Coordinator.PLType

module

public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal

section Frobenius

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isComplement'_sylow_of_isNormalPComplement {N : Subgroup G}
    (hN : CFSG.GroupTheory.IsNormalPComplement p N) (P : Sylow p G) :
    (P : Subgroup G).IsComplement' N := by
  obtain ⟨-, hcop, k, hk⟩ := hN
  have hcard : Nat.card N * p ^ k = Nat.card G := by
    rw [← hk]
    exact Subgroup.card_mul_index N
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hndvd : ¬ p ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm
  have hP : Nat.card P = p ^ k := by
    rw [Sylow.card_eq_multiplicity, ← hcard, Nat.factorization_mul hN0 hpk0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, Nat.Prime.factorization_pow Fact.out]
    simp
  refine Subgroup.isComplement'_of_coprime ?_ ?_
  · rw [hP, mul_comm, hcard]
  · rw [hP]
    exact Nat.Coprime.pow_left k hcop.symm

omit [Finite G] [Fact p.Prime] in
theorem isPGroup_automizer_bot :
    IsPGroup p (↥(Subgroup.normalizer ((⊥ : Subgroup G) : Set G)) ⧸
      (Subgroup.centralizer ((⊥ : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((⊥ : Subgroup G) : Set G))) := by
  intro x
  refine ⟨0, ?_⟩
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]

theorem exists_normal_pComplement_of_forall
    (h : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup p Q →
      IsPGroup p (↥(Subgroup.normalizer (Q : Set G)) ⧸
        (Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G)))) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.Coprime p (Nat.card N) ∧
      ∀ P : Sylow p G, (P : Subgroup G).IsComplement' N := by
  obtain ⟨N, hN⟩ := ((CFSG.GroupTheory.frobenius_normal_p_complement (G := G) p).1).2
    (fun Q hQ => by
      by_cases hQ1 : Q = ⊥
      · subst hQ1
        exact isPGroup_automizer_bot
      · exact h Q hQ1 hQ)
  exact ⟨N, hN.1, hN.2.1.symm, isComplement'_sylow_of_isNormalPComplement hN⟩

end Frobenius

section TwoLocal

variable {K : Type*} [Group K] [Finite K]

theorem one_le_gLATwoLocalRank_of_dvd_card_twoLocal {H : Subgroup K} (hH : IsTwoLocal H)
    {r : ℕ} (hr : r.Prime) (hrd : r ∣ Nat.card H) : 1 ≤ GLATwoLocalRank r K := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) r hrd
  have hxo : orderOf (x : K) = r := by rw [Subgroup.orderOf_coe, hx]
  have hEH : Subgroup.zpowers (x : K) ≤ H := (Subgroup.zpowers_le).2 x.2
  have hE : IsElemAbelian r (Subgroup.zpowers (x : K)) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  have hcard : Nat.card (Subgroup.zpowers (x : K)) = r ^ 1 := by
    rw [Nat.card_zpowers, hxo, pow_one]
  have h1 : 1 ≤ pRank r H := CFSG.SectionRank.le_pRank hr.one_lt hEH hE hcard
  refine h1.trans (le_csSup ?_ ⟨H, hH, rfl⟩)
  refine ⟨pRank r (⊤ : Subgroup K), ?_⟩
  rintro k ⟨H', -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hr.one_lt le_top

theorem exists_twoLocal_not_isPGroup (hsimple : IsSimpleGroup K) (hnc : ∃ a b : K, a * b ≠ b * a) :
    ∃ H : Subgroup K, IsTwoLocal H ∧ ¬ IsPGroup 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hcomm : ∀ a b : K, a * b = b * a := by
    obtain ⟨N, hNn, hcop, hcompl⟩ := exists_normal_pComplement_of_forall (G := K) (p := 2)
      (fun Q hQ hQp => by
        refine IsPGroup.to_quotient (hno _ ⟨Q, hQ, hQp, rfl⟩) _)
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 K))
    have hsolv : Group.IsSolvable K := by
      rcases hNn.eq_bot_or_eq_top with hN | hN
      · subst hN
        have hc := (hcompl P).card_mul_card
        rw [Subgroup.card_bot, mul_one] at hc
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 P.isPGroup'
        have hK : IsPGroup 2 K := IsPGroup.of_card (n := n) (hc.symm.trans hn)
        have := hK.isNilpotent
        infer_instance
      · subst hN
        rw [Subgroup.card_top, Nat.coprime_two_left] at hcop
        exact CFSG.Milestones.odd_order_solvable hcop
    exact IsSimpleGroup.comm_iff_isSolvable.2 hsolv
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (hcomm a b)

theorem inputOddTwoLocal_proved : InputOddTwoLocal := by
  intro K _ _ hsimple hnc _
  obtain ⟨H, hH, hHp⟩ := exists_twoLocal_not_isPGroup hsimple hnc
  have : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card H := by
    by_contra hno
    push Not at hno
    refine hHp (IsPGroup.of_card (n := (Nat.card H).primeFactorsList.length) ?_)
    exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => by
      by_contra hd2
      exact hno d hd hd2 hdd
  obtain ⟨r, hr, hr2, hrd⟩ := this
  exact ⟨r, hr, hr2, one_le_gLATwoLocalRank_of_dvd_card_twoLocal hH hr hrd⟩

end TwoLocal

end CFSG.HardMathSupport.Solomon.Coordinator

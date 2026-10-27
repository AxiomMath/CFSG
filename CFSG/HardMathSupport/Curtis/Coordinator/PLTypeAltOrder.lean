module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open TauCeti CFSG.Open CFSG.Assembly.LowTwoRank

theorem primePower_card_two {q : PrimePower} (h : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  rw [PrimePower.card_def] at h
  have hp := q.prime_p
  have hpe : q.p ∣ 2 := by
    rw [← h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hpe
  rw [hp2] at h
  exact ⟨hp2, Nat.pow_right_injective le_rfl (by simpa using h)⟩

theorem gcd_four_two_pow_sub {m : ℕ} (hm : 1 ≤ m) : Nat.gcd 4 (2 ^ m - 1) = 1 := by
  have hodd : Odd (2 ^ m - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨2 ^ k - 1, ?_⟩
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have h4 : Nat.Coprime 2 (2 ^ m - 1) := (Nat.coprime_two_left).2 hodd
  exact (Nat.Coprime.pow_left 2 h4)

theorem gcd_four_two_pow_add {m : ℕ} (hm : 1 ≤ m) : Nat.gcd 4 (2 ^ m + 1) = 1 := by
  have hodd : Odd (2 ^ m + 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact ⟨2 ^ k, by rw [pow_succ]; omega⟩
  have h4 : Nat.Coprime 2 (2 ^ m + 1) := (Nat.coprime_two_left).2 hodd
  exact (Nat.Coprime.pow_left 2 h4)

theorem prod_four_pow_eq (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 (m - 1), (2 ^ (2 * i) - 1) = ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [pow_mul]
  norm_num

theorem four_le_of_valid_D {m : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D m q).Valid) :
    4 ≤ m :=
  (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

theorem four_le_of_valid_twistedD {m : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedD m q).Valid) : 4 ≤ m :=
  (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1

theorem card_lie_typeD_two (m : ℕ) (d : ValidLieTypeIndex) (q : PrimePower) (hq : q.card = 2)
    (hd : d.1 = .D m q) :
    Nat.card (CFSGIndex.lie d).Group =
      2 ^ (m * (m - 1)) * (2 ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hm : 4 ≤ m := four_le_of_valid_D hv
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp
    (MulEquiv.refl _)
  rw [hp, he] at hmod
  have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.2.1 rfl
  change Nat.card (ValidLieTypeIndex.Group ⟨.D m q, hv⟩) = _
  rw [h, ordD, pow_one, gcd_four_two_pow_sub (by omega), Nat.div_one, prod_four_pow_eq]

theorem card_lie_twistedD_two (m : ℕ) (d : ValidLieTypeIndex) (q : PrimePower) (hq : q.card = 2)
    (hd : d.1 = .twistedD m q) :
    Nat.card (CFSGIndex.lie d).Group =
      2 ^ (m * (m - 1)) * (2 ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), (4 ^ i - 1) := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hm : 4 ≤ m := four_le_of_valid_twistedD hv
  have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp
    (MulEquiv.refl _)
  rw [hp, he] at hmod
  have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.2.2.2 rfl
  change Nat.card (ValidLieTypeIndex.Group ⟨.twistedD m q, hv⟩) = _
  rw [h, ordTwistedD, pow_one, gcd_four_two_pow_add (by omega), Nat.div_one, prod_four_pow_eq]

theorem card_lie_twistedA_three_two (d : ValidLieTypeIndex) (q : PrimePower) (hq : q.card = 2)
    (hd : d.1 = .twistedA 3 q) : Nat.card (CFSGIndex.lie d).Group = 25920 := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hp, he⟩ := primePower_card_two hq
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv (MulEquiv.refl _)
  rw [hp, he] at hmod
  have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hmod).2.1 rfl
  change Nat.card (ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) = _
  rw [h]
  decide +kernel

end CFSG.HardMathSupport.Curtis.Coordinator.PLType

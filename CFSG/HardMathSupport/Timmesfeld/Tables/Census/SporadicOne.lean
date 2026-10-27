module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.Sporadic.ON
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
public import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.Blueprint CFSG.Open
  CFSG.RankThree.PartOne.StrongP

@[expose] def SporadicOnePair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 3 ∧ name ∈ ({.J3, .McL, .Suz, .ONan, .Co3, .Co2, .Co1, .Fi22, .Fi23, .Fi24Prime, .HN, .Ly,
    .Th, .B, .M} : Finset TauCeti.SporadicName)) ∨
  (p = 5 ∧ name ∈ ({.Co1, .HN, .Ly, .B, .M} : Finset TauCeti.SporadicName)) ∨
  (p = 7 ∧ name = .M)

instance (name : TauCeti.SporadicName) (p : ℕ) : Decidable (SporadicOnePair name p) := by
  unfold SporadicOnePair
  infer_instance

@[expose] def SporadicLocalOnePairs : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ p : ℕ, p.Prime → SporadicOnePair name p → IsLocallyOneBalancedAbs p S

@[expose] def SporadicBMData : Prop :=
  Nat.card (NativeSporadic.Carrier .B) = 4154781481226426191177580544000000 ∧
    Nat.card (NativeSporadic.Carrier .M) = monsterOrder ∧
    HasNoncommPair 13 (NativeSporadic.Carrier .M)

@[expose] def OffPair (name : TauCeti.SporadicName) (X : Type) [Group X] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ SporadicOnePair name p →
    ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X)

theorem offPair_of_card {name : TauCeti.SporadicName} {X : Type} [Group X] {n : ℕ}
    (hX : Nat.card X = n) (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, p ≠ 2 → ¬ SporadicOnePair name p →
      ¬ p ^ 3 ∣ n ∨ (¬ p ^ 4 ∣ n ∧ HasNoncommPair p X)) : OffPair name X := by
  intro p hp hp2 hq
  rw [hX]
  by_cases hd : p ∣ n
  · exact h p (Nat.mem_primeFactors.2 ⟨hp, hd, hn⟩) hp2 hq
  · exact Or.inl fun h3 => hd ((dvd_pow_self p three_ne_zero).trans h3)

section Pairs

theorem pair_M12_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .M12) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem pair_M24_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .M24) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem pair_J2_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .J2) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem pair_J4_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .J4) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem pair_He_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .He) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

theorem pair_Ru_three :
    HasNoncommPair 3 (NativeSporadic.Carrier .Ru) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
  exact CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc

end Pairs

section OffPairs

theorem offPair_M11 :
    OffPair .M11 (NativeSporadic.Carrier .M11) := by
  refine offPair_of_card CFSG.Sporadic.Mathieu.card_M11 (by norm_num) ?_
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_M12 :
    OffPair .M12 (NativeSporadic.Carrier .M12) := by
  refine offPair_of_card CFSG.Sporadic.Mathieu.card_M12 (by norm_num) ?_
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_M12_three⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_M22 :
    OffPair .M22 (NativeSporadic.Carrier .M22) := by
  refine offPair_of_card CFSG.Sporadic.Mathieu.card_M22 (by norm_num) ?_
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_M23 :
    OffPair .M23 (NativeSporadic.Carrier .M23) := by
  refine offPair_of_card CFSG.Sporadic.Schreier.m23_card (by norm_num) ?_
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_M24 :
    OffPair .M24 (NativeSporadic.Carrier .M24) := by
  refine offPair_of_card CFSG.Sporadic.Mathieu.card_M24 (by norm_num) ?_
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_M24_three⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_J1 :
    OffPair .J1 (NativeSporadic.Carrier .J1) := by
  refine offPair_of_card CFSG.Sporadic.J1.card_J1 (by norm_num) ?_
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_J2 :
    OffPair .J2 (NativeSporadic.Carrier .J2) := by
  refine offPair_of_card CFSG.Sporadic.J2.card_J2 (by norm_num) ?_
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_J2_three⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_J3 :
    OffPair .J3 (NativeSporadic.Carrier .J3) := by
  refine offPair_of_card CFSG.Sporadic.J3.card_J3 (by norm_num) ?_
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_J4 :
    OffPair .J4 (NativeSporadic.Carrier .J4) := by
  refine offPair_of_card CFSG.Sporadic.J4.card_J4 (by norm_num) ?_
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_J4_three⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_J4⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_HS :
    OffPair .HS (NativeSporadic.Carrier .HS) := by
  refine offPair_of_card CFSG.Sporadic.HS.card_HS (by norm_num) ?_
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_HS⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_McL :
    OffPair .McL (NativeSporadic.Carrier .McL) := by
  refine offPair_of_card CFSG.Sporadic.McL.card_McL (by norm_num) ?_
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_McL⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_He :
    OffPair .He (NativeSporadic.Carrier .He) := by
  refine offPair_of_card CFSG.Sporadic.He.card_He (by norm_num) ?_
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_He_three⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_He⟩,
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Ru :
    OffPair .Ru (NativeSporadic.Carrier .Ru) := by
  refine offPair_of_card CFSG.Sporadic.Ru.card_Ru (by norm_num) ?_
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ _ => Or.inr ⟨by norm_num, pair_Ru_three⟩,
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Ru⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Suz :
    OffPair .Suz (NativeSporadic.Carrier .Suz) := by
  refine offPair_of_card CFSG.Sporadic.Suz.card_Suz (by norm_num) ?_
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_ONan :
    OffPair .ONan (NativeSporadic.Carrier .ONan) := by
  refine offPair_of_card CFSG.Sporadic.ON.card_ON (by norm_num) ?_
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_ON⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Co1 :
    OffPair .Co1 (NativeSporadic.Carrier .Co1) := by
  refine offPair_of_card CFSG.Sporadic.Co1.card_Co1 (by norm_num) ?_
  have hpf : Nat.primeFactors 4157776806543360000 = {2, 3, 5, 7, 11, 13, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Co2 :
    OffPair .Co2 (NativeSporadic.Carrier .Co2) := by
  refine offPair_of_card CFSG.Sporadic.Co2.card_Co2 (by norm_num) ?_
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co2⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Co3 :
    OffPair .Co3 (NativeSporadic.Carrier .Co3) := by
  refine offPair_of_card CFSG.Sporadic.Co3.card_Co3 (by norm_num) ?_
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co3⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Fi22 :
    OffPair .Fi22 (NativeSporadic.Carrier .Fi22) := by
  refine offPair_of_card CFSG.Sporadic.Fi22.card_Fi22 (by norm_num) ?_
  have hpf : Nat.primeFactors 64561751654400 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Fi23 :
    OffPair .Fi23 (NativeSporadic.Carrier .Fi23) := by
  refine offPair_of_card CFSG.Sporadic.Fi23.card_Fi23 (by norm_num) ?_
  have hpf : Nat.primeFactors 4089470473293004800 = {2, 3, 5, 7, 11, 13, 17, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Fi24Prime :
    OffPair .Fi24Prime (NativeSporadic.Carrier .Fi24Prime) := by
  refine offPair_of_card CFSG.Sporadic.Fi24.card_Fi24prime (by norm_num) ?_
  have hpf : Nat.primeFactors 1255205709190661721292800 = {2, 3, 5, 7, 11, 13, 17, 23, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Fi24_seven⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_HN :
    OffPair .HN (NativeSporadic.Carrier .HN) := by
  refine offPair_of_card CFSG.Sporadic.HN.card_HN (by norm_num) ?_
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Ly :
    OffPair .Ly (NativeSporadic.Carrier .Ly) := by
  refine offPair_of_card CFSG.Sporadic.Ly.card_Ly' (by norm_num) ?_
  have hpf : Nat.primeFactors 51765179004000000 = {2, 3, 5, 7, 11, 31, 37, 67} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_Th :
    OffPair .Th (NativeSporadic.Carrier .Th) := by
  refine offPair_of_card CFSG.RankThree.PartOne.CTP.card_Th (by norm_num) ?_
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inr ⟨by norm_num, CFSG.RankThree.PartOne.CTP.hasNoncommPair_Th⟩,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_B (hB : Nat.card (NativeSporadic.Carrier .B) = 4154781481226426191177580544000000) :
    OffPair .B (NativeSporadic.Carrier .B) := by
  refine offPair_of_card hB (by norm_num) ?_
  have hpf : Nat.primeFactors 4154781481226426191177580544000000 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num),
    fun _ _ => Or.inl (by norm_num)⟩

theorem offPair_M (hM : Nat.card (NativeSporadic.Carrier .M) = monsterOrder)
    (h13 : HasNoncommPair 13 (NativeSporadic.Carrier .M)) :
    OffPair .M (NativeSporadic.Carrier .M) := by
  refine offPair_of_card hM (by norm_num [monsterOrder]) ?_
  have hpf : Nat.primeFactors monsterOrder =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71} := by
    norm_num [monsterOrder, Nat.primeFactors, Nat.primeFactorsList]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ hQ => absurd (by decide) hQ,
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inr ⟨by norm_num [monsterOrder], h13⟩,
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder]),
    fun _ _ => Or.inl (by norm_num [monsterOrder])⟩

theorem offPair_carrier
    (hBM : SporadicBMData) (s : TauCeti.SporadicName) : OffPair s (NativeSporadic.Carrier s) := by
  cases s with
  | M11 => exact offPair_M11
  | M12 => exact offPair_M12
  | M22 => exact offPair_M22
  | M23 => exact offPair_M23
  | M24 => exact offPair_M24
  | J1 => exact offPair_J1
  | J2 => exact offPair_J2
  | J3 => exact offPair_J3
  | J4 => exact offPair_J4
  | HS => exact offPair_HS
  | McL => exact offPair_McL
  | He => exact offPair_He
  | Ru => exact offPair_Ru
  | Suz => exact offPair_Suz
  | ONan => exact offPair_ONan
  | Co1 => exact offPair_Co1
  | Co2 => exact offPair_Co2
  | Co3 => exact offPair_Co3
  | Fi22 => exact offPair_Fi22
  | Fi23 => exact offPair_Fi23
  | Fi24Prime => exact offPair_Fi24Prime
  | HN => exact offPair_HN
  | Ly => exact offPair_Ly
  | Th => exact offPair_Th
  | B => exact offPair_B hBM.1
  | M => exact offPair_M hBM.2.1 hBM.2.2

end OffPairs

theorem sporadicLocalOneData_of_pairs
    (hB : SporadicBridges) (hBM : SporadicBMData) (h : SporadicLocalOnePairs) :
    SporadicLocalOneData := by
  intro S _ _ hS hnab name he p hp hp2 h3 hcase
  by_cases hq : SporadicOnePair name p
  · exact h S hS hnab name he p hp hq
  · exfalso
    obtain ⟨e⟩ := he
    obtain ⟨c⟩ := hB name
    let f : S ≃* NativeSporadic.Carrier name := e.trans c.symm
    have hcard : Nat.card S = Nat.card (NativeSporadic.Carrier name) := Nat.card_congr f.toEquiv
    rcases offPair_carrier hBM name p hp hp2 hq with h1 | ⟨h4, hpair⟩
    · rw [hcard] at h3
      exact h1 h3
    · have hS' : HasNoncommPair p S :=
        HasNoncommPair.map f.symm.toMonoidHom f.symm.injective hpair
      rcases hcase with h4' | hno
      · rw [hcard] at h4'
        exact h4 h4'
      · exact hno hS'

theorem sporadicLocalOneData_of_pairs_holds
    (hBM : SporadicBMData) (h : SporadicLocalOnePairs) : SporadicLocalOneData :=
  sporadicLocalOneData_of_pairs (hB := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group) hBM h

end CFSG.HardMathSupport.Timmesfeld.Tables.Census

module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUBridge
public import CFSG.LieType.SeitzGeneration.OuterSUPair
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUMain

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration.SUPair CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

theorem subfieldPairSUOdd_of_ne_two (ℓ f f₀ : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData ℓ f K) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f = p * f₀) (hq : ℓ ^ f₀ ≠ 2) (n : ℕ) (hn : 3 ≤ n)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hne : (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n) :
    Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
      ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤ := by
  classical
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have := h₀.finite
  have : CharP k ℓ := h₀.charP
  have hK := h.card_eq_sq
  have hKk0 := h₀.card_eq_sq
  have hq2 : 2 ≤ ℓ ^ f₀ := h₀.one_lt_pow
  have hq3 : 3 ≤ ℓ ^ f₀ := by omega
  have hqf : ℓ ^ f = (ℓ ^ f₀) ^ p := by rw [hf, pow_mul']
  have hqne : ℓ ^ f ≠ 2 := by
    rw [hqf]
    have : 3 ^ 1 ≤ (ℓ ^ f₀) ^ p := le_trans (Nat.pow_le_pow_left hq3 1)
      (Nat.pow_le_pow_right (by omega) hp.one_lt.le)
    omega
  have hKk : Nat.card K = Nat.card k ^ p := by
    rw [hK, hKk0, hqf]
    ring
  set K₀ : Subfield K := h.fixedField with hK₀def
  have hK₀ : ∀ x, x ∈ K₀ ↔ unitaryInvolution K ℓ f x = x := fun x => by
    rw [hK₀def, h.mem_fixedField, bar_eq_unitaryInvolution h]
  have hcardK₀ : Nat.card K₀ = ℓ ^ f := h.card_fixedField
  have hcardk₀ : Nat.card (k.comap K₀.subtype) = ℓ ^ f₀ := by
    rw [← h₀.card_fixedField]
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨(x.1 : K), x.2⟩, ?_⟩
        invFun := fun y => ⟨⟨(y.1 : K), ?_⟩, y.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · rw [h₀.mem_fixedField]
      apply Subtype.ext
      rw [hbar]
      exact (h.mem_fixedField).1 x.1.2
    · rw [hK₀def, h.mem_fixedField, ← hbar]
      have := (h₀.mem_fixedField).1 y.2
      exact congrArg (fun z : k => (z : K)) this
  have hKc : Nat.card K₀ = Nat.card (k.comap K₀.subtype) ^ p := by
    rw [hcardK₀, hcardk₀, hqf]
  have hk3 : 3 ≤ Nat.card (k.comap K₀.subtype) := by rw [hcardk₀]; exact hq3
  have hUk := isUnitaryInvolution_unitaryInvolution (p := ℓ) (f := f₀) hKk0
  have h3 := exists_norm_ne_one (p := ℓ) (f := f₀) hKk0 hq
  have h3' := exists_three_norm_neg_one (ℓ := ℓ) (f := f₀) hKk0
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsup := ratSU_sup_conj_eq_top hK hqne (stable_of_bar h h₀ hbar)
    (unitaryInvolution k ℓ f₀) (bar_coe h h₀ hbar) hUk K₀ hK₀ hp hp2 hKk hKc hk3
    (m := m) (by omega) (fun _ => h3) h3' (A : GL (Fin (m + 1)) K)
    (conjTr_mul_self_of_mem h (m + 1) A) (by
      intro heq
      apply hne
      refine Subgroup.map_injective (f := (eSU h (m + 1)).toMonoidHom) (eSU h (m + 1)).injective ?_
      rw [map_conj_suSub_eq h h₀ hbar (m + 1) A, map_suSub_eq h h₀ hbar (m + 1)]
      exact heq)
  rw [← Subgroup.sup_eq_closure]
  refine Subgroup.map_injective (f := (eSU h (m + 1)).toMonoidHom) (eSU h (m + 1)).injective ?_
  rw [Subgroup.map_sup, map_suSub_eq h h₀ hbar (m + 1), map_conj_suSub_eq h h₀ hbar (m + 1) A,
    hsup, Subgroup.map_top_of_surjective _ (eSU h (m + 1)).surjective]

@[expose] def SubfieldPairSUOddTwo : Prop :=
  ∀ (ℓ f f₀ : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K) (k : Subfield K)
    (h₀ : UnitaryFieldData ℓ f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ),
    p.Prime → p ≠ 2 → f = p * f₀ → ℓ ^ f₀ = 2 → ∀ n : ℕ, 4 ≤ n → ¬ (p ∣ n ∧ p ∣ ℓ ^ f₀ + 1) →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
      Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
        ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤

theorem subfieldPairSUOdd (h2 : SubfieldPairSUOddTwo) :
    SubfieldPairSUOdd := by
  intro ℓ f f₀ K _ h k h₀ hbar p hp hp2 hf n hn hpn h32 A hne
  by_cases hq : ℓ ^ f₀ = 2
  · exact h2 ℓ f f₀ K h k h₀ hbar p hp hp2 hf hq n (by
      rcases Nat.lt_or_ge n 4 with h4 | h4
      · exact absurd ⟨by omega, hq⟩ h32
      · exact h4) hpn A hne
  · exact subfieldPairSUOdd_of_ne_two ℓ f f₀ K h k h₀ hbar p hp hp2 hf hq n hn A hne

end CFSG.LieType.SeitzGeneration

module

public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

theorem isPSolvable_of_isSolvable {X : Type*} [Group X] {p : ℕ} (hp : p.Prime)
    (hX : Group.IsSolvable X) : CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = p ∨ Nat.Coprime p (Nat.card (↥H ⧸ T))
  by_cases hpq : Nat.card (↥H ⧸ T) = p
  · exact Or.inl hpq
  · exact Or.inr ((Nat.coprime_primes hp hq).mpr (Ne.symm hpq))

theorem isSolvable_of_card_eq_pow_mul_pow {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rwa [← Nat.card_eq_fintype_card])

theorem isSolvable_of_index {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 60)
    (W : Subgroup K) (hn : 5 ≤ W.index) : Group.IsSolvable W := by
  have hmul : W.index * Nat.card W = 60 := by rw [← hK]; exact W.index_mul_card
  have hdiv : Nat.card W ∣ 60 := ⟨W.index, by rw [← hmul]; ring⟩
  have hle : Nat.card W ≤ 12 := by nlinarith
  have hmem : Nat.card W ∈ (Nat.divisors 60).filter (· ≤ 12) := by simp [hdiv, hle]
  have heq : (Nat.divisors 60).filter (· ≤ 12) = {1, 2, 3, 4, 5, 6, 10, 12} := by decide +kernel
  rw [heq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 0) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 0)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 5) (a := 0) (b := 1)
      Nat.prime_two (by norm_num) (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 1) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 5) (a := 1) (b := 1)
      Nat.prime_two (by norm_num) (by norm_num) (by simpa using h)
  · exact isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 2) (b := 1)
      Nat.prime_two Nat.prime_three (by norm_num) (by simpa using h)

theorem eq_top_of_not_isPSolvable_three {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : Nat.card K = 60) (W : Subgroup K) (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W) :
    W = ⊤ := by
  by_contra hne
  apply hW
  refine isPSolvable_of_isSolvable Nat.prime_three (isSolvable_of_index hK W ?_)
  have hmul : W.index * Nat.card W = 60 := by rw [← hK]; exact W.index_mul_card
  have hdvd : W.index ∣ 60 := ⟨_, hmul.symm⟩
  have hne1 : W.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have hpos : 0 < W.index := Nat.pos_of_ne_zero (by rintro h; rw [h] at hmul; omega)
  have hinj : Function.Injective (MulAction.toPermHom K (K ⧸ W)) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases (MulAction.toPermHom K (K ⧸ W)).normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      apply hne
      rw [eq_top_iff]
      intro k _
      have : k ∈ (MulAction.toPermHom K (K ⧸ W)).ker := by rw [h]; trivial
      have h2 := Equiv.Perm.ext_iff.mp this (QuotientGroup.mk 1)
      simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h2
      have h3 : (QuotientGroup.mk k : K ⧸ W) = QuotientGroup.mk 1 := by
        simpa [MulAction.Quotient.smul_mk] using h2
      simpa using QuotientGroup.eq.mp h3
  have hcard : Nat.card K ∣ Nat.card (Equiv.Perm (K ⧸ W)) := Subgroup.card_dvd_of_injective _ hinj
  have hfin : Nat.card (K ⧸ W) = W.index := rfl
  rw [Nat.card_perm, hfin, hK] at hcard
  by_contra hlt
  rw [not_le] at hlt
  have hmem : W.index ∈ ({2, 3, 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rw [h] at hcard <;> revert hcard <;> decide

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

module

public import CFSG.ClassicalInvolution.QuaternionStructure

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped MatrixGroups

@[expose] def IsQuaternionPair {G : Type*} [Monoid G] (x y : G) : Prop :=
  x ^ 2 = y ^ 2 ∧ (x * y) ^ 2 = x ^ 2 ∧ x ^ 2 ≠ 1

theorem IsQuaternionPair.map {G H : Type*} [Monoid G] [Monoid H] (f : G →* H)
    (hf : Function.Injective f) {x y : G} (h : IsQuaternionPair x y) :
    IsQuaternionPair (f x) (f y) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← map_pow, ← map_pow, h1], by rw [← map_mul, ← map_pow, ← map_pow, h2], ?_⟩
  rw [← map_pow]
  intro h
  exact h3 (hf (by rw [h, map_one]))

theorem exists_isQuaternionPair_quaternionGroup (k : ℕ) (hk : 1 ≤ k) :
    ∃ x y : QuaternionGroup (2 ^ k), IsQuaternionPair x y := by
  have hN : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hne : ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by positivity) h
    have : 0 < 2 ^ k := by positivity
    omega
  refine ⟨QuaternionGroup.a ((2 ^ (k - 1) : ℕ) : ZMod (2 * 2 ^ k)), QuaternionGroup.xa 0, ?_, ?_,
    ?_⟩
  · rw [QuaternionGroup.xa_sq, pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add]
    congr 2
    omega
  · rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_sq, pow_two, QuaternionGroup.a_mul_a,
      ← Nat.cast_add]
    congr 2
    omega
  · rw [pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, QuaternionGroup.one_def]
    intro h
    apply hne
    rw [← QuaternionGroup.a.inj h]
    congr 1
    omega

theorem exists_sylow_quaternion_or_dvd_of_witness {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hw : classicalInvolutionWitness K) :
    (∃ S : Sylow 2 K, ∃ k : ℕ, 1 ≤ k ∧
        Nonempty ((S : Subgroup K) ≃* QuaternionGroup (2 ^ k))) ∨ 5040 ∣ Nat.card K := by
  rcases hw with ⟨p, n, hp, hp2, -, ⟨e⟩⟩ | ⟨-, hcard, ⟨e⟩⟩
  · left
    let f : K →* SL(2, GaloisField p n) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore K))
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : Odd (Nat.card f.ker) := by
      have : f.ker = classicalInvolutionOddCore K := by
        ext x
        change e (QuotientGroup.mk x) = 1 ↔ x ∈ classicalInvolutionOddCore K
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
      rw [this]
      exact QuaternionStructure.odd_natCard_oddCore K
    obtain ⟨T⟩ : Nonempty (Sylow 2 K) := inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow 2 SL(2, GaloisField p n)) := inferInstance
    obtain ⟨φ⟩ := QuaternionStructure.nonempty_sylow_equiv_of_surjective f hf hker T U
    have hchar : ringChar (GaloisField p n) ≠ 2 := by
      rw [ringChar.eq (GaloisField p n) p]
      exact hp2
    obtain ⟨k, hk, ⟨q⟩⟩ := specialLinearGroup_sylow_quaternion (GaloisField p n) hchar U
    exact ⟨T, k, hk, ⟨φ.trans q⟩⟩
  · right
    set Q := K ⧸ classicalInvolutionOddCore K
    have h1 : Nat.card Q = Nat.card (Q ⧸ Subgroup.center Q) * Nat.card (Subgroup.center Q) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card K = Nat.card Q * Nat.card (classicalInvolutionOddCore K) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h3 : Nat.card (Q ⧸ Subgroup.center Q) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    rw [h2, h1, h3, hcard]
    exact Dvd.intro (Nat.card (classicalInvolutionOddCore K)) (by ring)

end CFSG.ClassicalInvolution

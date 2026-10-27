module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504Embedding
public import CFSG.Walter.SimpleCaseStronglyEmbedded
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse

public section

namespace CFSG.ComponentClassification.LiteratureLocal

open Subgroup Order504
open scoped MatrixGroups

theorem nonempty_mulEquiv_psl2_eight_of_simple {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 504) : Nonempty (G ≃* PSL(2, GaloisField 2 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hS8 := card_sylow_two_subgroup hG S
  have hab : CFSG.Walter.HasAbelianSylowTwo G := by
    intro P
    exact isMulCommutative_iff.mpr fun a b => Subtype.ext (sylow_two_comm hG P a.2 b.2)
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hn : (S : Subgroup G).Normal :=
      ⟨fun n hn g => by rw [h g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
    exact not_normal_of_card (by rw [hS8]; norm_num) (by rw [hS8, hG]; norm_num) hn
  obtain ⟨hM1, hM2, hM3⟩ := normalizer_sylow_two_stronglyEmbedded hG S
  have hM : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (normalizer ((S : Subgroup G) : Set G)) :=
    ⟨hM1, hM2, hM3⟩
  rcases CFSG.Walter.isTypeL2_of_stronglyEmbedded G hnonab hab _ hM with
    ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩
  · have hcard : Nat.card G = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Walter.psl2_even_card (by omega)]
    rw [hG] at hcard
    have hf3 : f = 3 := by
      rcases Nat.lt_or_ge f 4 with h | h
      · interval_cases f <;> first | rfl | (norm_num at hcard)
      · exfalso
        have h1 : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
        have h2 : (2 ^ 4) ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h1 2
        have h3 : 2 ^ 4 * ((2 ^ 4) ^ 2 - 1) ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
          Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
        rw [← hcard] at h3
        norm_num at h3
    subst hf3
    exact ⟨e⟩
  · exfalso
    obtain ⟨Q⟩ : Nonempty (Sylow 2 PSL(2, GaloisField p f)) := inferInstance
    have hQ := CFSG.Walter.psl2_sylow_two_card_eq_four (GaloisField p f)
      (GaloisField.card p f (by omega)) hpodd hf h8 Q
    have h1 := S.card_eq_multiplicity
    have h2 := Q.card_eq_multiplicity
    rw [← Nat.card_congr e.toEquiv] at h2
    rw [hS8] at h1
    rw [hQ] at h2
    omega

theorem simple_order_504_is_psl2_eight (G : Type) [Group G] [Finite G]
    (hG : Nat.card G = 504) (hnormal : ∀ N : Subgroup G, N.Normal → N = ⊥ ∨ N = ⊤) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 2 3 ∧
      CFSG.Assembly.ComponentType.ClassicalModel G .PSL 2 2 3 ∧
      Nonempty (G ≃* PSL(2, GaloisField 2 3)) := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hG]; norm_num)
  have : IsSimpleGroup G := { eq_bot_or_eq_top_of_normal := fun N hN => hnormal N hN }
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2_eight_of_simple hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstated := CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv G 2 3
    (by norm_num) e
  exact ⟨hstated,
    CFSG.ComponentClassification.ClassicalModelStatedBridge.classicalModel_psl_of_stated hstated,
    ⟨e⟩⟩

end CFSG.ComponentClassification.LiteratureLocal

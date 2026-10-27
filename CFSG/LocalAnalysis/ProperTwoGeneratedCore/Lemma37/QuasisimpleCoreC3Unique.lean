module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {H : Type*} [Group H]

theorem caseC3_exists_mem_normalizer_not_mem [Finite H] {R S : Subgroup H} (hS : IsPGroup 2 S)
    (hRS : R ≤ S) (hne : R ≠ S) : ∃ s ∈ S, s ∈ Subgroup.normalizer (R : Set H) ∧ s ∉ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : R.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hne (le_antisymm hRS h)
  have hlt' := Group.normalizerCondition_of_isNilpotent (G := S) (R.subgroupOf S) hlt
  obtain ⟨s, hs, hsn⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨s, s.2, ?_, fun h => hsn h⟩
  have : s ∈ (Subgroup.normalizer (R : Set H)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hRS]
    exact hs
  exact this

theorem caseC3_le_of_abelian [Finite H] {W T S₀ A : Subgroup H} (hWT : W ≤ T) (hTS : T ≤ S₀)
    (hWT2 : W.relIndex T = 2) (hTS2 : T.relIndex S₀ = 2)
    (h1 : ∀ a ∈ S₀, a ∉ W → Nat.card (W ⊓ Subgroup.centralizer {a} : Subgroup H) ≤ 4)
    (h2 : ∀ a₁ ∈ T, a₁ ∉ W → ∀ a₂ ∈ S₀, a₂ ∉ T →
      Nat.card (W ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {a₂} : Subgroup H) ≤ 2)
    (hAS : A ≤ S₀) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA16 : Nat.card A = 16) :
    A ≤ W := by
  have hWS4 : W.relIndex S₀ = 4 := by
    rw [← Subgroup.relIndex_mul_relIndex W T S₀ hWT hTS, hWT2, hTS2]
  have hcardWA : W.relIndex A * Nat.card (W ⊓ A : Subgroup H) = 16 := by
    rw [Subgroup.relIndex_mul_card, hA16]
  have hrelWA : W.relIndex A ≤ 4 :=
    hWS4 ▸ Subgroup.relIndex_le_of_le_right hAS (by rw [hWS4]; norm_num)
  have hWA4 : 4 ≤ Nat.card (W ⊓ A : Subgroup H) := by
    by_contra hlt
    push Not at hlt
    have : W.relIndex A * Nat.card (W ⊓ A : Subgroup H) < 4 * 4 :=
      Nat.mul_lt_mul_of_le_of_lt hrelWA hlt (by norm_num)
    omega
  have hcent : ∀ a ∈ A, W ⊓ A ≤ W ⊓ Subgroup.centralizer {a} := fun a ha b hb =>
    ⟨hb.1, Subgroup.mem_centralizer_singleton_iff.mpr (hA b hb.2 a ha)⟩
  by_contra hAW
  obtain ⟨a, haA, haW⟩ := Set.not_subset.mp hAW
  by_cases hAT : A ≤ T
  ·
    have hrel2 : W.relIndex A ≤ 2 :=
      hWT2 ▸ Subgroup.relIndex_le_of_le_right hAT (by rw [hWT2]; norm_num)
    have hWA8 : 8 ≤ Nat.card (W ⊓ A : Subgroup H) := by
      by_contra hlt
      push Not at hlt
      have : W.relIndex A * Nat.card (W ⊓ A : Subgroup H) < 2 * 8 :=
        Nat.mul_lt_mul_of_le_of_lt hrel2 hlt (by norm_num)
      omega
    have := (Subgroup.card_le_of_le (hcent a haA)).trans (h1 a (hTS (hAT haA)) haW)
    omega
  · obtain ⟨a₂, ha₂A, ha₂T⟩ := Set.not_subset.mp hAT
    have hWA_le : Nat.card (W ⊓ A : Subgroup H) ≤ 4 :=
      (Subgroup.card_le_of_le (hcent a₂ ha₂A)).trans
        (h1 a₂ (hAS ha₂A) (fun h => ha₂T (hWT h)))
    have hcardTA : T.relIndex A * Nat.card (T ⊓ A : Subgroup H) = 16 := by
      rw [Subgroup.relIndex_mul_card, hA16]
    have hrelTA : T.relIndex A ≤ 2 :=
      hTS2 ▸ Subgroup.relIndex_le_of_le_right hAS (by rw [hTS2]; norm_num)
    have hTA8 : 8 ≤ Nat.card (T ⊓ A : Subgroup H) := by
      by_contra hlt
      push Not at hlt
      have : T.relIndex A * Nat.card (T ⊓ A : Subgroup H) < 2 * 8 :=
        Nat.mul_lt_mul_of_le_of_lt hrelTA hlt (by norm_num)
      omega
    have hTAW : ¬ (T ⊓ A ≤ W) := fun hle => by
      have : Nat.card (T ⊓ A : Subgroup H) ≤ Nat.card (W ⊓ A : Subgroup H) :=
        Subgroup.card_le_of_le fun b hb => ⟨hle hb, hb.2⟩
      omega
    obtain ⟨a₁, ha₁TA, ha₁W⟩ := Set.not_subset.mp hTAW
    have hle : W ⊓ A ≤ W ⊓ Subgroup.centralizer {a₁} ⊓ Subgroup.centralizer {a₂} :=
      fun b hb => ⟨hcent a₁ ha₁TA.2 hb, (hcent a₂ ha₂A hb).2⟩
    have := (Subgroup.card_le_of_le hle).trans (h2 a₁ ha₁TA.1 ha₁W a₂ (hAS ha₂A) ha₂T)
    omega

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

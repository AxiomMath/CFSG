module

public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

@[expose] def BenderCoverRigid : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K A : Subgroup X) [K.Normal] [(A.subgroupOf K).Normal],
    A ≤ K → (∀ a ∈ A, ∀ k ∈ K, a * k = k * a) → Nat.card A = 2 → ⁅K, K⁆ = K →
      CFSG.BenderSuzuki.IsBenderGroup (↥K ⧸ A.subgroupOf K) →
      ∀ (S : Sylow 2 ↥K) (z : X), (∀ s ∈ (S : Subgroup ↥K), z * (s : X) * z⁻¹ = (s : X)) →
        ∀ k ∈ K, z * k * z⁻¹ = k

@[expose] def BenderOuterInvolution : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.BenderSuzuki.IsBenderGroup K →
    ∀ α : MulAut K, α * α = 1 → (¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) →
      (∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y) ∧
        ∀ S : Sylow 2 K, ∃ x : K, α x = x ∧ x ∉ normalizer ((S : Subgroup K) : Set K)

structure BenderFacts : Prop where
  coverRigid : BenderCoverRigid
  outerInvolution : BenderOuterInvolution

section BenderWrappers

open CFSG.BenderSuzuki

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem exists_benderType_of_isBenderGroup (h : IsBenderGroup K) :
    ∃ n i e, CFSG.GH74.Uniqueness.Bender.BenderType K n i e :=
  CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp h

theorem isSimpleGroup_of_isBenderGroup (h : IsBenderGroup K) : IsSimpleGroup K := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup h
  exact hT.isSimple

theorem two_le_twoRank_of_isBenderGroup
    (h : IsBenderGroup K) : 2 ≤ Open.twoRank K := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup h
  rw [hT.twoRank_eq]
  exact hT.two_le.2

theorem exists_not_commute_of_isBenderGroup
    (h : IsBenderGroup K) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hsimple := isSimpleGroup_of_isBenderGroup h
  have hrank := two_le_twoRank_of_isBenderGroup h
  let _ : CommGroup K := { ‹Group K› with mul_comm := hcomm }
  have hprime := IsSimpleGroup.prime_card (α := K)
  obtain ⟨E, -, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) (⊤ : Subgroup K)
  have hdvd : 2 ^ 2 ∣ Nat.card K := by
    have h1 : 2 ^ 2 ∣ Nat.card E := by
      rw [hEcard]
      exact Nat.pow_dvd_pow 2 hrank
    exact h1.trans (Subgroup.card_subgroup_dvd_card E)
  rcases hprime.eq_one_or_self_of_dvd 4 (by simpa using hdvd) with h4 | h4
  · norm_num at h4
  · rw [← h4] at hprime
    norm_num at hprime

theorem isConj_of_involutions_of_isBenderGroup
    (h : IsBenderGroup K) {x y : K} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup h
  have hx' := orderOf_eq_prime_iff.mp hx
  have hy' := orderOf_eq_prime_iff.mp hy
  exact hT.lemma_3_4_a (by simpa [sq] using hx'.1) hx'.2 (by simpa [sq] using hy'.1) hy'.2

theorem isStronglyEmbedded_normalizer_of_isBenderGroup
    (h : IsBenderGroup K) (S : Sylow 2 K) :
    IsStronglyEmbedded (normalizer ((S : Subgroup K) : Set K)) := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup h
  obtain ⟨t, hc⟩ := hT.exists_benderCore S
  exact hc.strong

end BenderWrappers

end CFSG.GH74.Uniqueness

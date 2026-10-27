module

public import Mathlib.GroupTheory.Transfer
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact64iiOuterNPCArith

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

theorem not_normalizer_le_centralizer_of_simple {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p K) (hPne : (P : Subgroup K) ≠ ⊥) :
    ¬ Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := by
  intro hNC
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hc := hcomp.card_mul_card
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hNC).ker with h | h
  · rw [h, Subgroup.card_bot, one_mul] at hc
    have hKp : IsPGroup p K := by
      have h1 := P.card_eq_multiplicity
      rw [hc] at h1
      exact IsPGroup.of_card h1
    have hcen : Subgroup.center K = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K)).resolve_left
        (by
          haveI : Nontrivial K := by
            obtain ⟨a, b, hab⟩ := hnab
            exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
          exact (hKp.bot_lt_center).ne')
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center K := by
      rw [hcen]
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)
  · rw [h, Subgroup.card_top] at hc
    have hP1 : Nat.card (P : Subgroup K) = 1 := by
      have hpos : 0 < Nat.card K := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [hc, mul_one])
    exact hPne (Subgroup.eq_bot_of_card_eq _ hP1)

theorem exists_normalizer_not_centralize_torsion {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p K) (hPne : (P : Subgroup K) ≠ ⊥) {γ : K} {a : ℕ} (hγ : orderOf γ = p ^ a)
    (hγP : γ ∈ (P : Subgroup K)) (hgen : ∀ x ∈ (P : Subgroup K), x ∈ Subgroup.zpowers γ) :
    ∃ y ∈ Subgroup.normalizer ((P : Subgroup K) : Set K), ∃ x ∈ (P : Subgroup K),
      x ^ p = 1 ∧ y * x * y⁻¹ ≠ x := by
  obtain ⟨y, hyN, hyC⟩ := SetLike.not_le_iff_exists.1
    (not_normalizer_le_centralizer_of_simple hnab P hPne)
  have hyγ : y * γ ≠ γ * y := by
    intro h
    apply hyC
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen t ht)
    exact (Commute.zpow_left (Commute.symm h) i).eq
  have hy1 : y * γ * y⁻¹ ∈ Subgroup.zpowers γ :=
    hgen _ ((Subgroup.mem_normalizer_iff.1 hyN γ).1 hγP)
  refine ⟨y, hyN, γ ^ (p ^ (a - 1)), (P : Subgroup K).pow_mem hγP _, ?_, ?_⟩
  · have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        have : γ = 1 := by rwa [pow_zero, orderOf_eq_one_iff] at hγ
        exact absurd (by rw [this]; simp) hyγ
      · exact h
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel ha0]
    rw [← hγ]
    exact pow_orderOf_eq_one γ
  · intro htor
    set N : Subgroup K := Subgroup.normalizer ((P : Subgroup K) : Set K) with hN
    haveI : ((P : Subgroup K).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
    have hpow : y ^ ((P : Subgroup K).relIndex N) ∈ (P : Subgroup K) := by
      have := Subgroup.pow_index_mem ((P : Subgroup K).subgroupOf N) (⟨y, hyN⟩ : N)
      rwa [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at this
    have hdvd : (P : Subgroup K).relIndex N ∣ (P : Subgroup K).index :=
      Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer
    have he : ¬ p ∣ (P : Subgroup K).relIndex N := fun h => P.not_dvd_index (h.trans hdvd)
    have hye : y ^ ((P : Subgroup K).relIndex N) * γ = γ * y ^ ((P : Subgroup K).relIndex N) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hgen _ hpow)
      rw [← hi]
      exact (Commute.zpow_self γ i).eq
    exact hyγ (commute_of_torsion_commute hγ hy1 htor he hye)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

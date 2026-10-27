module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem three_pow_three_le_relIndex_centralizer {K : Type*} [Group K] [Finite K]
    {Q B : Subgroup K} {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) (hQ : IsPGroup 3 Q)
    (hB : IsPGroup d B) (hBQ : B ≤ normalizer (Q : Set K))
    (hne : ¬ Q ≤ centralizer (B : Set K)) :
    3 ^ 3 ≤ (centralizer (B : Set K)).relIndex Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime d) := ⟨hd⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup K, F = Q ⊓ centralizer (B : Set K) := ⟨_, rfl⟩
  have hFQ : F ≤ Q := by rw [hF]; exact inf_le_left
  have hFC : F ≤ centralizer (B : Set K) := by rw [hF]; exact inf_le_right
  have hrelF : F.relIndex Q = (centralizer (B : Set K)).relIndex Q := by
    rw [hF, inf_comm]
    exact Subgroup.inf_relIndex_right (centralizer (B : Set K)) Q
  rw [← hrelF]
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hdvd : F.relIndex Q ∣ 3 ^ m := by
    rw [← hm]
    exact F.relIndex_dvd_card Q
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hn1 : F.relIndex Q ≠ 1 := by
    intro h
    exact hne ((Subgroup.relIndex_eq_one.mp h).trans hFC)
  have hsne : s ≠ 0 := by
    rintro rfl
    exact hn1 (by rw [hs, pow_zero])
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hsne
  obtain ⟨X, hX⟩ : ∃ X : Set K, X = (Q : Set K) \ (F : Set K) := ⟨_, rfl⟩
  have hXstable : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    rw [hX, Set.mem_sdiff] at hx ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hBQ hb) x).mp hx.1
    · intro hcon
      apply hx.2
      rw [hF] at hcon ⊢
      refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcomm : b * (b * x * b⁻¹) = (b * x * b⁻¹) * b :=
        (Subgroup.mem_centralizer_iff.mp hcon.2) b hb
      have hxeq : x = b * x * b⁻¹ := by
        calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
          _ = b⁻¹ * ((b * x * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
          _ = b * x * b⁻¹ := by group
      rw [hxeq]
      exact (Subgroup.mem_centralizer_iff.mp hcon.2) c hc
  let _ : MulAction B X :=
    { smul := fun b x => ⟨(b : K) * (x : K) * (b : K)⁻¹, hXstable (b : K) b.2 (x : K) x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : B) : K) * (x : K) * ((1 : B) : K)⁻¹ = (x : K)
        simp)
      mul_smul := fun b b' x => Subtype.ext (by
        show ((b * b' : B) : K) * (x : K) * ((b * b' : B) : K)⁻¹ =
          (b : K) * ((b' : K) * (x : K) * (b' : K)⁻¹) * (b : K)⁻¹
        simp [mul_assoc]) }
  have hfix_empty : MulAction.fixedPoints B X = (∅ : Set X) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨x, hx⟩ hfix
    rw [MulAction.mem_fixedPoints] at hfix
    rw [hX, Set.mem_sdiff] at hx
    exact hx.2 (by
      rw [hF]
      refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hval : c * x * c⁻¹ = x := congrArg Subtype.val (hfix ⟨c, hc⟩)
      exact mul_inv_eq_iff_eq_mul.mp hval)
  have hdvdX : d ∣ Nat.card X := by
    have hcong := hB.card_modEq_card_fixedPoints X
    rw [hfix_empty] at hcong
    simp only [Nat.card_of_isEmpty] at hcong
    exact Nat.modEq_zero_iff_dvd.mp hcong
  have hcardQ : F.relIndex Q * Nat.card F = Nat.card Q := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := Q)
    rwa [inf_eq_left.mpr hFQ] at h
  have hcardX : Nat.card X = Nat.card F * (F.relIndex Q - 1) := by
    have hFsub : (F : Set K) ⊆ (Q : Set K) := fun x hx => hFQ hx
    have h1 : Nat.card X = Nat.card Q - Nat.card F := by
      rw [hX]
      exact Set.ncard_sdiff hFsub
    rw [h1, ← hcardQ, Nat.mul_comm (F.relIndex Q) (Nat.card F),
      Nat.mul_sub_left_distrib, Nat.mul_one]
  have hcop : Nat.Coprime d (Nat.card F) := by
    rw [hd.coprime_iff_not_dvd]
    intro hdivF
    have hFdvd : Nat.card F ∣ 3 ^ m := by
      rw [← hm, ← hcardQ]
      exact dvd_mul_left (Nat.card F) (F.relIndex Q)
    have hdvd3 : d ∣ 3 := hd.dvd_of_dvd_pow (hdivF.trans hFdvd)
    have h3 : d = 3 := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp hdvd3
    omega
  have hdiv : d ∣ F.relIndex Q - 1 := by
    have h := hdvdX
    rw [hcardX] at h
    exact hcop.dvd_of_dvd_mul_left h
  have hdiv3s : d ∣ 3 ^ s - 1 := by
    rwa [hs] at hdiv
  have hs3 : 3 ≤ s := by
    by_contra h
    have hs2 : s ≤ 2 := by omega
    interval_cases s
    · have hdvd2 : d ∣ 2 := by
        have h := hdiv3s
        norm_num at h
        exact h
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    · have hdvd8 : d ∣ 8 := by
        have h := hdiv3s
        norm_num at h
        exact h
      have hdvd2 : d ∣ 2 := by
        have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
        rw [h8] at hdvd8
        exact hd.dvd_of_dvd_pow hdvd8
      have := Nat.le_of_dvd (by norm_num) hdvd2
      omega
  calc 3 ^ 3 ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
    _ = F.relIndex Q := hs.symm

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

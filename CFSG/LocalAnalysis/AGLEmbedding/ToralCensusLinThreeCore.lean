module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeCuts
public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitCycle

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_fixed_of_card_eq_three {m : ℕ} (hm : m = 3) {s : Matrix (Fin m) (Fin m) K}
    (h3 : s ^ 3 = 1) (hdet : s.det = 1) (hK : ¬ 3 ∣ Nat.card K - 1) :
    ∃ w : Fin m → K, w ≠ 0 ∧ s *ᵥ w = (1 : K) • w := by
  subst hm
  by_cases hns : ∀ c : K, s ≠ c • 1
  · obtain ⟨w, hw0, hw⟩ :=
      LinearThreeKit.exists_mulVec_eq_smul_of_pow_three h3 hdet hns (one_pow 3)
    exact ⟨w, hw0, hw⟩
  · push Not at hns
    obtain ⟨c, rfl⟩ := hns
    have hc3 : c ^ 3 = 1 := by
      have := congrFun (congrFun h3 0) 0
      rw [smul_pow, one_pow] at this
      simpa using this
    have hc1 := eq_one_of_pow_prime_eq_one_of_not_dvd Nat.prime_three hc3 hK
    refine ⟨Pi.single 0 1, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_⟩
    rw [hc1, one_smul, one_smul, Matrix.one_mulVec]

variable {n : ℕ} {I : Set ℕ}

theorem eq_three_of_threeCensus (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty)
    {t : SpecialLinearGroup (Fin n) K} (htP : t ∈ perfectJoin (flagStabilizer n K I))
    (ht3 : t ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hC : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q) :
    n = 3 ∧ 4 ≤ Nat.card K := by
  have htI : t ∈ flagStabilizer n K I := perfectJoin_le _ htP
  obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ht3
  have ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hζ]
  have hgr := gradedPerfectSL_holds K n I t htP
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hid : ∀ {a b : ℕ} (h : IsConsecutiveCut n I a b),
      ¬ (3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) →
      cutBlock (t : Matrix (Fin n) (Fin n) K) a b h.2.1 = 1 := by
    intro a b h hnb
    refine (hgr a b h).2 ?_
    have := h.1
    by_cases h2 : b - a = 2
    · exact Or.inr ⟨h2, card_eq_two_of_lt_four (by omega)⟩
    · exact Or.inl (by omega)
  obtain ⟨b₀, a₁, h₀, h₁, hb₀a₁⟩ := exists_first_last_cuts hI hne
  have hζ1 : ζ = 1 := by
    have key : ∀ {a b : ℕ} (h : IsConsecutiveCut n I a b),
        ¬ (3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) → ζ = 1 := by
      intro a b h hnb
      have h3 := cutBlock_pow_three_eq_scalar h htI ht
      rw [hid h hnb, one_pow] at h3
      have := congrFun (congrFun h3 ⟨0, by have := h.1; omega⟩) ⟨0, by have := h.1; omega⟩
      simpa [scalar_apply] using this.symm
    by_cases hbig₀ : 3 ≤ b₀ - 0 ∨ (b₀ - 0 = 2 ∧ 4 ≤ Nat.card K)
    · by_cases hbig₁ : 3 ≤ n - a₁ ∨ (n - a₁ = 2 ∧ 4 ≤ Nat.card K)
      · exact (false_of_two_perfect_cuts hcyc h₀ h₁ hb₀a₁ hbig₀ hbig₁).elim
      · exact key h₁ hbig₁
    · exact key h₀ hbig₀
  subst hζ1
  have hFV : ∀ {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b) (h' : IsConsecutiveCut n I a' b'),
      b ≤ a' →
      (∃ w : Fin (b - a) → K, w ≠ 0 ∧
        cutBlock (t : Matrix (Fin n) (Fin n) K) a b h.2.1 *ᵥ w = (1 : K) • w) →
      (∃ w : Fin (b' - a') → K, w ≠ 0 ∧
        cutBlock (t : Matrix (Fin n) (Fin n) K) a' b' h'.2.1 *ᵥ w = (1 : K) • w) → False :=
    fun h h' hba ⟨w, hw0, hw⟩ ⟨w', hw'0, hw'⟩ =>
      false_of_eigen_cutBlocks ht (one_pow 3) hC h h' hba hw hw0 hw' hw'0
  have hFVnb : ∀ {a b : ℕ} (h : IsConsecutiveCut n I a b),
      ¬ (3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) →
      ∃ w : Fin (b - a) → K, w ≠ 0 ∧
        cutBlock (t : Matrix (Fin n) (Fin n) K) a b h.2.1 *ᵥ w = (1 : K) • w := by
    intro a b h hnb
    refine ⟨Pi.single ⟨0, by have := h.1; omega⟩ 1, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_⟩
    rw [hid h hnb, Matrix.one_mulVec, one_smul]
  have hsize : ∀ {a b : ℕ} (h : IsConsecutiveCut n I a b),
      (3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K)) →
      ¬ (∃ w : Fin (b - a) → K, w ≠ 0 ∧
        cutBlock (t : Matrix (Fin n) (Fin n) K) a b h.2.1 *ᵥ w = (1 : K) • w) →
      b - a = 2 ∧ 4 ≤ Nat.card K := by
    intro a b h hbig hnfv
    have hlt := isConsecutiveCut_sub_lt hI hne h
    rcases hbig with h3 | h2
    · by_cases hq : 3 ∣ Nat.card K - 1
      · exact (false_of_three_le_cut hcyc h h3 hlt hq).elim
      · have h4 : b - a = 3 := by
          by_contra hne3
          exact false_of_four_le_cut hcyc h (by omega) hq
        have hs3 := cutBlock_pow_three_eq_scalar h htI ht
        rw [map_one] at hs3
        exact (hnfv (exists_fixed_of_card_eq_three h4 hs3 (hgr a b h).1 hq)).elim
    · exact h2
  have hb₀n : b₀ < n := lt_of_le_of_lt hb₀a₁ h₁.1
  by_cases hfv₀ : ∃ w : Fin (b₀ - 0) → K, w ≠ 0 ∧
      cutBlock (t : Matrix (Fin n) (Fin n) K) 0 b₀ h₀.2.1 *ᵥ w = (1 : K) • w
  · by_cases hfv₁ : ∃ w : Fin (n - a₁) → K, w ≠ 0 ∧
        cutBlock (t : Matrix (Fin n) (Fin n) K) a₁ n h₁.2.1 *ᵥ w = (1 : K) • w
    · exact (hFV h₀ h₁ hb₀a₁ hfv₀ hfv₁).elim
    · have hbig₁ : 3 ≤ n - a₁ ∨ (n - a₁ = 2 ∧ 4 ≤ Nat.card K) := by
        by_contra hnb
        exact hfv₁ (hFVnb h₁ hnb)
      obtain ⟨hs₁, hq4⟩ := hsize h₁ hbig₁ hfv₁
      have hnb₀ : ¬ (3 ≤ b₀ - 0 ∨ (b₀ - 0 = 2 ∧ 4 ≤ Nat.card K)) := fun hbig₀ =>
        false_of_two_perfect_cuts hcyc h₀ h₁ hb₀a₁ hbig₀ hbig₁
      have hb₀1 : b₀ = 1 := by have := h₀.1; omega
      rcases eq_or_lt_of_le hb₀a₁ with heq | hlt
      · exact ⟨by omega, hq4⟩
      · obtain ⟨b', hM⟩ := exists_isConsecutiveCut_of_right h₀ hb₀n
        have hb'a₁ : b' ≤ a₁ := le_of_isConsecutiveCut_of_lt hM h₁ hlt
        have hnbM : ¬ (3 ≤ b' - b₀ ∨ (b' - b₀ = 2 ∧ 4 ≤ Nat.card K)) := fun hbig =>
          false_of_two_perfect_cuts hcyc hM h₁ hb'a₁ hbig hbig₁
        exact (hFV h₀ hM le_rfl hfv₀ (hFVnb hM hnbM)).elim
  · have hbig₀ : 3 ≤ b₀ - 0 ∨ (b₀ - 0 = 2 ∧ 4 ≤ Nat.card K) := by
      by_contra hnb
      exact hfv₀ (hFVnb h₀ hnb)
    obtain ⟨hs₀, hq4⟩ := hsize h₀ hbig₀ hfv₀
    have hnb₁ : ¬ (3 ≤ n - a₁ ∨ (n - a₁ = 2 ∧ 4 ≤ Nat.card K)) := fun hbig₁ =>
      false_of_two_perfect_cuts hcyc h₀ h₁ hb₀a₁ hbig₀ hbig₁
    have ha₁ : n - a₁ = 1 := by have := h₁.1; omega
    rcases eq_or_lt_of_le hb₀a₁ with heq | hlt
    · exact ⟨by omega, hq4⟩
    · obtain ⟨b', hM⟩ := exists_isConsecutiveCut_of_right h₀ hb₀n
      have hb'a₁ : b' ≤ a₁ := le_of_isConsecutiveCut_of_lt hM h₁ hlt
      have hnbM : ¬ (3 ≤ b' - b₀ ∨ (b' - b₀ = 2 ∧ 4 ≤ Nat.card K)) := fun hbig =>
        false_of_two_perfect_cuts hcyc h₀ hM le_rfl hbig₀ hbig
      exact (hFV hM h₁ hb'a₁ (hFVnb hM hnbM) (hFVnb h₁ hnb₁)).elim

end CFSG.AGLEmbedding.ToralCensus

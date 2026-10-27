module

public import CFSG.GH74.Uniqueness.Section173Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem Sec173.suzuki_arith {q r c N : ℕ} (hr : 0 < r) (hrq : r < q) (hc : c ≡ 1 [MOD q])
    (hc1 : c ≠ 1) (hN : N = q - 1 ∨ N = q - r + 1 ∨ N = q + r + 1) (hdvd : c ∣ N) : False := by
  have hq : 1 < q := lt_of_le_of_lt hr hrq
  have hmod : c % q = 1 := by
    have := hc; unfold Nat.ModEq at this; rw [this]; exact Nat.mod_eq_of_lt hq
  have hcq := Nat.div_add_mod c q
  rw [hmod] at hcq
  have hk1 : 1 ≤ c / q := by
    rcases Nat.eq_zero_or_pos (c / q) with h | h
    · rw [h] at hcq; omega
    · exact h
  have hcq1 : q + 1 ≤ c := by nlinarith
  have hN0 : 0 < N := by omega
  have hcN : c ≤ N := Nat.le_of_dvd hN0 hdvd
  rcases hN with rfl | rfl | rfl
  · omega
  · omega
  · have hk : c / q = 1 := by
      by_contra hk
      have : 2 ≤ c / q := by omega
      nlinarith
    rw [hk, mul_one] at hcq
    obtain ⟨m, hm⟩ := hdvd
    rw [← hcq] at hm
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m <;> omega
    · nlinarith

theorem ZDSetup.lemma173
    (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (h172 : Lemma172Stmt Z M) :
    Lemma173Stmt Z M := by
  intro c n e hB
  obtain ⟨A, s, hAB, hAodd, hsB, hs2, hs1, hsA, -, hc1, hc2, -, -⟩ :=
    S.exists_pair_B0 h166 h172 c hB
  set F : Subgroup X := cenHull Z c.u with hF
  have hBF : Bender.BenderType ↥F n 2 e := S.benderType_of_benderSub hB (Or.inr rfl)
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    exact hc2 (Subgroup.relIndex_bot_right _)
  obtain ⟨hcard', hA'1, -, -, hsN⟩ := Sec173.subgroupOf_facts hAB hsB hs2 hs1 hsA hA1
  have hA'odd : Odd (Nat.card ↥(A.subgroupOf F)) := by rw [hcard']; exact hAodd
  obtain ⟨T, hAT, -, -, -, hTcard, -, -, -, hinv⟩ := hBF.suzuki_odd_subgroup hA'odd hA'1
  have hinvX : ∀ a ∈ A, s * a * s⁻¹ = a⁻¹ := by
    intro a ha
    have h1 := hinv ⟨s, hsB⟩ (Subtype.ext hs2) (fun h => hs1 (congrArg Subtype.val h)) hsN
      ⟨a, hAB ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact congrArg Subtype.val h1
  have hc : (centralizer ({s} : Set X)).relIndex A = Nat.card A :=
    Sec173.relIndex_eq_card_of_inv hAodd hinvX
  have hdvd : Nat.card A ∣ Nat.card T := by
    rw [← hcard']
    exact Subgroup.card_dvd_of_le hAT
  rw [hc] at hc1 hc2
  obtain ⟨a, ha1, hna⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases hBF.cases' with ⟨h, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨h, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  have hr : 0 < 2 ^ (a + 1) := by positivity
  have hrq : 2 ^ (a + 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Sec173.suzuki_arith hr hrq hc1 hc2 (N := Nat.card T) ?_ hdvd
  rcases hTcard with h | ⟨a', ha', h | h⟩
  · exact Or.inl h
  · have : a' = a := by omega
    subst this
    exact Or.inr (Or.inl h)
  · have : a' = a := by omega
    subst this
    exact Or.inr (Or.inr h)

end CFSG.GH74.Uniqueness

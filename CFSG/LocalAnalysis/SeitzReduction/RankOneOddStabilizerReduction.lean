module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLemmaS

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv MulAction

theorem regular_or_simple_of_odd_stabilizer_of_dvd {Ω : Type*} [Finite Ω]
    (N : Subgroup (Perm Ω))
    (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d)
    {n : ℕ} (hn : 1 ≤ n) (hΩ : Nat.card Ω = 2 ^ n) (α : Ω)
    (hodd : Odd (Nat.card ↥(N ⊓ stabilizer (Perm Ω) α))) {m : ℕ}
    (hdvd : Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) ∣ m) :
    (∃ A : Subgroup (Perm Ω), A ≤ N ∧ (A.subgroupOf N).Normal ∧
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = 2 ^ n ∧
        ∀ β γ : Ω, ∃! a : A, (a : Perm Ω) β = γ) ∨
    ∃ S : Subgroup (Perm Ω), S ≤ N ∧ (S.subgroupOf N).Normal ∧ IsSimpleGroup S ∧
      (∃ a b : S, a * b ≠ b * a) ∧ (∀ β γ : Ω, ∃ s ∈ S, s β = γ) ∧
      ∃ h : ℕ, Nat.card S = 2 ^ n * h ∧ Odd h ∧ h ∣ m := by
  rcases socle_elementary_abelian_or_simple_of_odd_stabilizer N h2 hn hΩ α hodd with hA |
    ⟨S, hSN, hSn, hs, hnab, htr, hcard, hSodd⟩
  · exact Or.inl hA
  · exact Or.inr ⟨S, hSN, hSn, hs, hnab, htr, _, hcard, hSodd,
      (Subgroup.card_dvd_of_le (inf_le_inf_right _ hSN)).trans hdvd⟩

theorem eq_of_card_eq_168 {Ω : Type*} [Finite Ω] {N S : Subgroup (Perm Ω)}
    (htr : ∀ β γ : Ω, ∃ x ∈ N, x β = γ) (hΩ : Nat.card Ω = 8) (α : Ω)
    (hdvd : Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) ∣ 21) (hSN : S ≤ N)
    (hS : Nat.card S = 168) :
    S = N ∧ Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) = 21 ∧ Nat.card N = 168 := by
  have hN := card_eq_card_mul_card_inf_stabilizer htr α
  rw [hΩ] at hN
  have h168 : 8 * 21 ∣ 8 * Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) := by
    rw [← hN, show 8 * 21 = 168 by norm_num, ← hS]
    exact Subgroup.card_dvd_of_le hSN
  have h21 : Nat.card ↥(N ⊓ stabilizer (Perm Ω) α) = 21 :=
    Nat.dvd_antisymm hdvd (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h168)
  have hN168 : Nat.card N = 168 := by rw [hN, h21]
  exact ⟨Subgroup.eq_of_le_of_card_ge hSN (by rw [hN168, hS]), h21, hN168⟩

theorem commutator_eq_self_of_isSimpleGroup_of_exists_mul_ne {G : Type*} [Group G]
    {N : Subgroup G} (hs : IsSimpleGroup N) (hnab : ∃ a b : N, a * b ≠ b * a) : ⁅N, N⁆ = N := by
  have htop : ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ with h | h
    · obtain ⟨a, b, hab⟩ := hnab
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      exact (hab (Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top b)) a
        (Subgroup.mem_top a))).elim
    · exact h
  have hmap : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hmap, ← Subgroup.map_commutator, htop]

end CFSG.SeitzReduction.RankOne

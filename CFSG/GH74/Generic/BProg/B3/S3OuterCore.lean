module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartOne.S11d.PSLRank

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterCore

open CFSG

@[expose] def OuterCore {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ N : Subgroup Y, IsQuasisimple ↥N ∧ 2 ≤ pRank 2 ↥N ∧ (∀ n ∈ N, α n = n) ∧
    (∀ g : Y, α g = g → ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
    ∃ t ∈ N, t * t = 1 ∧ t ≠ 1 ∧ ∃ k : Y, α k * k⁻¹ = t

theorem two_le_pRank_of_invols {P : Type*} [Group P] [Finite P] {a b : P} (hab : a * b = b * a)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    2 ≤ pRank 2 P := by
  have hz : ∀ c : P, c * c = 1 → ∀ i : ℤ, (Even i ∧ c ^ i = 1) ∨ (Odd i ∧ c ^ i = c) := by
    intro c hc i
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · left
      refine ⟨even_two_mul k, ?_⟩
      rw [zpow_mul, zpow_two, hc, one_zpow]
    · right
      refine ⟨odd_two_mul_add_one k, ?_⟩
      rw [zpow_add_one, zpow_mul, zpow_two, hc, one_zpow, one_mul]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  refine CFSG.RankThree.PartOne.two_le_pRank_of_two_elements Nat.prime_two hab
    (by rw [pow_two]; exact ha2) (by rw [pow_two]; exact hb2) ?_
  intro i j hij
  rcases hz a ha2 i with ⟨hi, hai⟩ | ⟨hi, hai⟩ <;> rcases hz b hb2 j with ⟨hj, hbj⟩ | ⟨hj, hbj⟩
  · exact ⟨by exact_mod_cast even_iff_two_dvd.1 hi, by exact_mod_cast even_iff_two_dvd.1 hj⟩
  · rw [hai, hbj, one_mul] at hij
    exact absurd hij hb1
  · rw [hai, hbj, mul_one] at hij
    exact absurd hij ha1
  · rw [hai, hbj] at hij
    exact absurd (by rw [← hbi]; exact eq_inv_of_mul_eq_one_left hij) hne

theorem OuterCore.of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] [Finite Y] [Finite Y']
    (e : Y ≃* Y') {α : MulAut Y} {α' : MulAut Y'} (h : ∀ y, e (α y) = α' (e y))
    (hc : OuterCore α') : OuterCore α := by
  obtain ⟨N, hq, hr, hfix, hnorm, t, ht, ht2, ht1, k, hk⟩ := hc
  refine ⟨N.map e.symm.toMonoidHom, LocalCores.isQuasisimple_of_mulEquiv (e.symm.subgroupMap N) hq,
    ?_, ?_, ?_, e.symm t, ⟨t, ht, rfl⟩, ?_, ?_, e.symm k, ?_⟩
  · have h2 := CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt (p := 2) (by norm_num)
      (e.symm.subgroupMap N)
    exact h2 ▸ hr
  · rintro _ ⟨n, hn, rfl⟩
    have h1 : e (α (e.symm n)) = e (e.symm n) := by
      rw [h, MulEquiv.apply_symm_apply]
      exact hfix n hn
    exact e.injective h1
  · rintro g hg _ ⟨n, hn, rfl⟩
    have h1 : α' (e g) = e g := by
      rw [← h, hg]
    refine ⟨e g * n * (e g)⁻¹, hnorm (e g) h1 n hn, ?_⟩
    simp
  · rw [← map_mul, ht2, map_one]
  · intro h1
    exact ht1 (e.symm.injective (h1.trans (map_one e.symm).symm))
  · have h1 : e (α (e.symm k) * (e.symm k)⁻¹) = t := by
      rw [map_mul, map_inv, h, MulEquiv.apply_symm_apply, hk]
    calc α (e.symm k) * (e.symm k)⁻¹ = e.symm (e (α (e.symm k) * (e.symm k)⁻¹)) := by simp
      _ = e.symm t := by rw [h1]

theorem OuterCore.of_conj {Y : Type*} [Group Y] [Finite Y] {α α₀ : MulAut Y} (β : MulAut Y)
    (h : α = β * α₀ * β⁻¹) (hc : OuterCore α₀) : OuterCore α :=
  OuterCore.of_mulEquiv (β⁻¹ : MulAut Y) (fun y => by rw [h]; simp) hc

end S3OuterCore

end CFSG.GH74.Generic.BProg.B3

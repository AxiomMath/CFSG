module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Subgroup

theorem mem_of_normal_sylow {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (P : Sylow p Γ) [P.Normal] {g : Γ} (hg : ∃ k : ℕ, g ^ (p ^ k) = 1) : g ∈ P := by
  obtain ⟨k, hk⟩ := hg
  have hz : IsPGroup p (zpowers g) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    refine ⟨k, Subtype.ext ?_⟩
    change (g ^ m) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq Γ P Q
  have hPQ : h • P = P := Sylow.smul_eq_of_normal
  rw [hPQ] at hQ
  exact hQ (mem_zpowers g)

theorem exists_two_odd_decomp {Γ : Type*} [Group Γ] [Finite Γ] (g : Γ) :
    ∃ a o : Γ, g = a * o ∧ (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ ∃ m : ℕ, Odd m ∧ o ^ m = 1 := by
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨k, m, hm, hnkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm))
  obtain ⟨x, y, hxy⟩ := hcop
  refine ⟨g ^ (y * (m : ℤ)), g ^ (x * ((2 ^ k : ℕ) : ℤ)), ?_, ⟨k, ?_⟩, ⟨m, hm, ?_⟩⟩
  · rw [← zpow_add]
    have : y * (m : ℤ) + x * ((2 ^ k : ℕ) : ℤ) = 1 := by linarith
    rw [this, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    have : y * (m : ℤ) * ((2 ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * y := by
      rw [hnkm]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [← zpow_natCast, ← zpow_mul]
    have : x * ((2 ^ k : ℕ) : ℤ) * (m : ℤ) = (orderOf g : ℤ) * x := by
      rw [hnkm]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem exists_twoPart {Γ : Type*} [Group Γ] [Finite Γ] {Δ : Type*} [Group Δ] (π : Γ →* Δ)
    (hker : π.ker ≤ center Γ) (h2 : ∀ d ∈ π.range, ∃ k : ℕ, d ^ (2 ^ k) = 1) :
    ∃ S : Subgroup Γ, S.Normal ∧ IsPGroup 2 S ∧
      (∀ g : Γ, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ S) ∧
      ∀ g : Γ, ∃ s ∈ S, ∃ z ∈ π.ker, g = s * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : IsPGroup 2 ↥π.range := fun d => by
    obtain ⟨k, hk⟩ := h2 d d.2
    exact ⟨k, Subtype.ext hk⟩
  haveI : Finite ↥π.range := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  haveI : Group.IsNilpotent ↥π.range := hr.isNilpotent
  have hnil : Group.IsNilpotent Γ :=
    Subgroup.isNilpotent_of_ker_le_center π.rangeRestrict
      (by rwa [MonoidHom.ker_rangeRestrict])
  obtain ⟨P⟩ : Nonempty (Sylow 2 Γ) := inferInstance
  have hPn : (P : Subgroup Γ).Normal := inferInstance
  have hmem : ∀ g : Γ, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ (P : Subgroup Γ) := fun g hg =>
    mem_of_normal_sylow P hg
  refine ⟨P, hPn, P.isPGroup', hmem, fun g => ?_⟩
  obtain ⟨a, o, hg, ha, m, hm, ho⟩ := exists_two_odd_decomp g
  refine ⟨a, hmem a ha, o, ?_, hg⟩
  rw [MonoidHom.mem_ker]
  obtain ⟨k, hk⟩ := h2 (π o) ⟨o, rfl⟩
  have h1 : (π o) ^ m = 1 := by rw [← map_pow, ho, map_one]
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  have h3 : orderOf (π o) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h4 : orderOf (π o) ∣ m := orderOf_dvd_of_pow_eq_one h1
  have h5 := Nat.dvd_gcd h3 h4
  rw [hcop.gcd_eq_one] at h5
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

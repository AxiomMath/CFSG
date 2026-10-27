module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem exists_three_part [Finite G] (g f : G) (hf : Is3Element f) :
    ∃ c : ℕ, Is3Element (g ^ c) ∧ f ^ c = f := by
  obtain ⟨j, hj⟩ := hf
  have hk0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, b, hb, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 3 (by norm_num)
  have hco : Nat.Coprime b (3 ^ (a + j + 1)) := by
    have h3 : Nat.Coprime 3 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb
    exact (Nat.Coprime.pow_left _ h3).symm
  obtain ⟨c, hc0, hc1⟩ := Nat.chineseRemainder hco 0 1
  obtain ⟨d, hd⟩ := (Nat.modEq_zero_iff_dvd).1 hc0
  refine ⟨c, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul]
    have : c * 3 ^ a = orderOf g * d := by rw [hd, hk]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  · have h1 : orderOf f ∣ 3 ^ (a + j + 1) :=
      (orderOf_dvd_of_pow_eq_one hj).trans (pow_dvd_pow 3 (by omega))
    have h2 : c ≡ 1 [MOD orderOf f] := Nat.ModEq.of_dvd h1 hc1
    rw [pow_eq_pow_iff_modEq.2 h2, pow_one]

theorem pow_act {V : Subgroup G} {g f : G} (hfV : ∀ z ∈ V, f * z * f⁻¹ ∈ V)
    (hg : ∀ z ∈ V, g * z * g⁻¹ = f * z * f⁻¹) (c : ℕ) :
    ∀ z ∈ V, g ^ c * z * (g ^ c)⁻¹ = f ^ c * z * (f ^ c)⁻¹ ∧ f ^ c * z * (f ^ c)⁻¹ ∈ V := by
  induction c with
  | zero => intro z hz; simp [hz]
  | succ c ih =>
    intro z hz
    obtain ⟨h1, h2⟩ := ih z hz
    have e1 : g ^ (c + 1) * z * (g ^ (c + 1))⁻¹ = g * (g ^ c * z * (g ^ c)⁻¹) * g⁻¹ := by
      rw [pow_succ']; group
    have e2 : f ^ (c + 1) * z * (f ^ (c + 1))⁻¹ = f * (f ^ c * z * (f ^ c)⁻¹) * f⁻¹ := by
      rw [pow_succ']; group
    refine ⟨?_, ?_⟩
    · rw [e1, e2, h1]; exact hg _ h2
    · rw [e2]; exact hfV _ h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

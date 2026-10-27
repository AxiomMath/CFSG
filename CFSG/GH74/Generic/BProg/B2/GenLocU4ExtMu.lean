module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtBd
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtFrame

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix

namespace GenLocU4ExtMu

variable {K : Type} [Field K]

@[expose] def IsSqM (q : ℕ) (a : K) : Prop := ∃ μ : K, μ ^ (q + 1) = 1 ∧ μ * μ = a

theorem isSquare_of_norm_one {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) {a : K} (ha : a ^ (p ^ f + 1) = 1) : ∃ w : K, w * w = a := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have : Fintype K := Fintype.ofFinite K
  have hF : ringChar K ≠ 2 := by rwa [ringChar.eq K p]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have hcard : Fintype.card K / 2 = (p ^ f + 1) * m := by
    rw [← Nat.card_eq_fintype_card, hK]
    have e : (p ^ f) ^ 2 = 2 * ((p ^ f + 1) * m) + 1 := by rw [hm]; ring
    omega
  have hsq : IsSquare a := by
    rw [FiniteField.isSquare_iff hF ha0, hcard, pow_mul, ha, one_pow]
  obtain ⟨w, hw⟩ := hsq
  exact ⟨w, hw.symm⟩

theorem isSqM_mul {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    {a b : K} (ha : a ^ (p ^ f + 1) = 1) (hb : b ^ (p ^ f + 1) = 1)
    (hna : ¬ IsSqM (p ^ f) a) (hnb : ¬ IsSqM (p ^ f) b) : IsSqM (p ^ f) (a * b) := by
  have key : ∀ {a : K}, a ^ (p ^ f + 1) = 1 → ¬ IsSqM (p ^ f) a →
      ∃ u : K, u * u = a ∧ u ^ (p ^ f + 1) = -1 := by
    intro a ha hna
    obtain ⟨u, hu⟩ := isSquare_of_norm_one hp hp2 hK ha
    refine ⟨u, hu, ?_⟩
    have h1 : u ^ (p ^ f + 1) * u ^ (p ^ f + 1) = 1 := by
      calc u ^ (p ^ f + 1) * u ^ (p ^ f + 1) = (u * u) ^ (p ^ f + 1) := by ring
        _ = 1 := by rw [hu]; exact ha
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact absurd ⟨u, h, hu⟩ hna
    · exact h
  obtain ⟨u, hu, hu1⟩ := key ha hna
  obtain ⟨v, hv, hv1⟩ := key hb hnb
  refine ⟨u * v, ?_, ?_⟩
  · rw [mul_pow, hu1, hv1]; norm_num
  · rw [← hu, ← hv]; ring

theorem not_isSqM_neg_one {q : ℕ} (hq : q % 4 = 1) (h2 : (2 : K) ≠ 0) : ¬ IsSqM q (-1 : K) := by
  rintro ⟨μ, hμ, hμ2⟩
  have h1 := GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hμ2
  rw [pow_succ, h1, hμ2] at hμ
  apply h2
  linear_combination -hμ

theorem not_isSqM_inv {q : ℕ} {c : K} (h : ¬ IsSqM q c) : ¬ IsSqM q c⁻¹ := by
  rintro ⟨μ, hμ, hμ2⟩
  apply h
  refine ⟨μ⁻¹, ?_, ?_⟩
  · rw [inv_pow, hμ, inv_one]
  · rw [← mul_inv, hμ2, inv_inv]

theorem exists_omega {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {c : K} (hc1 : c ^ (p ^ f + 1) = 1) (hc : ¬ IsSqM (p ^ f) c) :
    ∃ ω : K, ω ^ (p ^ f + 1) = 1 ∧ ω * ω * c = -1 := by
  have h2 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hc0 : c ≠ 0 := fun h => by rw [h] at hc1; simp at hc1
  have hm1 : (-1 : K) ^ (p ^ f + 1) = 1 := Even.neg_one_pow ⟨(p ^ f + 1) / 2, by omega⟩
  obtain ⟨ω, hω, hω2⟩ := isSqM_mul hp hp2 hK hm1 (by rw [inv_pow, hc1, inv_one])
    (not_isSqM_neg_one hq h2) (not_isSqM_inv hc)
  refine ⟨ω, hω, ?_⟩
  rw [hω2]
  field_simp

end GenLocU4ExtMu

end CFSG.GH74.Generic.BProg.B2

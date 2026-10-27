module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasicsRooting

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}

omit [Finite G] in
theorem eq_one_or_eq_of_sq_eq_one_of_unique {K : Subgroup G} {g : G}
    (hK : ∀ k ∈ K, orderOf k = 2 → k = z) (hg : g ∈ K) (hg2 : g ^ 2 = 1) : g = 1 ∨ g = z := by
  by_cases h1 : g = 1
  · exact Or.inl h1
  · exact Or.inr (hK g hg (orderOf_eq_prime hg2 h1))

variable (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  {A B : Subgroup G} (hAS : A ≤ (S : Subgroup G))
  (hgen : ∀ s ∈ (S : Subgroup G), ∃ a ∈ A, ∃ b ∈ B, a * b = s)
  (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
  (hA : ∀ a ∈ A, orderOf a = 2 → a = z) (hB : ∀ b ∈ B, orderOf b = 2 → b = z)
include hset hz hAS hgen hcomm hA hB

theorem coreSetting_rooting_central_product_false (hA4 : ∀ a ∈ A, a ^ 4 = 1) : False := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz.2.1, pow_orderOf_eq_one]
  have ha2 : ∀ a ∈ A, a ^ 2 = 1 ∨ a ^ 2 = z := fun a ha =>
    eq_one_or_eq_of_sq_eq_one_of_unique hA (A.pow_mem ha 2) (by rw [← pow_mul]; exact hA4 a ha)
  refine coreSetting_rooting_order_four_false hset hz ?_ ?_
  · intro y hyS hy4
    obtain ⟨a, ha, b, hb, rfl⟩ := hgen y hyS
    have hab := hcomm a ha b hb
    have hy1 : (a * b) ^ 4 = 1 := by rw [← hy4, pow_orderOf_eq_one]
    rw [hab.mul_pow, hA4 a ha, one_mul] at hy1
    have hb4 : (b ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hy1
    have hb2 := eq_one_or_eq_of_sq_eq_one_of_unique hB (B.pow_mem hb 2) hb4
    have hy2 : (a * b) ^ 2 ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one h
      rw [hy4] at this
      norm_num at this
    rw [hab.mul_pow] at hy2 ⊢
    rcases ha2 a ha with h | h <;> rcases hb2 with h' | h' <;> rw [h, h'] at hy2 ⊢
    · exact absurd (one_mul 1) hy2
    · exact one_mul z
    · exact mul_one z
    · exact absurd hzz hy2
  · intro t htS ht htz
    obtain ⟨a, ha, b, hb, rfl⟩ := hgen t htS
    have hab := hcomm a ha b hb
    rcases ha2 a ha with h | h
    · exfalso
      have ht2 : (a * b) ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
      rw [hab.mul_pow, h, one_mul] at ht2
      have hb2 := eq_one_or_eq_of_sq_eq_one_of_unique hB hb ht2
      have ha1 := eq_one_or_eq_of_sq_eq_one_of_unique hA ha h
      rcases ha1 with h1 | h1 <;> rcases hb2 with h2 | h2 <;> rw [h1, h2] at ht htz
      · rw [one_mul, orderOf_one] at ht
        exact absurd ht (by decide)
      · exact htz (one_mul z)
      · exact htz (mul_one z)
      · rw [hzz, orderOf_one] at ht
        exact absurd ht (by decide)
    · refine ⟨a, hAS ha, (Commute.refl a).mul_right hab, ?_⟩
      exact orderOf_eq_four_of_orderOf_sq_eq_two (by rw [h]; exact hz.2.1)

end CFSG.ProperTwoGeneratedCore.Assembly

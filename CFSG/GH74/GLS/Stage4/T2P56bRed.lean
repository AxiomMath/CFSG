module

public import CFSG.GH74.GLS.Stage4.T2Leaves

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

@[expose] def HasSDOrWreathedSylow (X : Type) [Group X] : Prop :=
  ∃ S : Sylow 2 X,
    (∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.SemidihedralGroup m)) ∨
      ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m)

@[expose] def ABGKFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsKGroupNative ↥X → HasSDOrWreathedSylow ↥X →
    ∀ p n : ℕ, p.Prime → p ≠ 2 → 5 ≤ p ^ n → ∀ z : G, z ∈ X → orderOf z = 2 →
      ∀ K : Subgroup G, K ≤ X → z ∈ K → HasSL2Model ↥K (fun q => q = p ^ n) →
        (∀ c ∈ X, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
          (∃ a ∈ X, a * z * a⁻¹ ≠ z ∧ (a * z * a⁻¹) * z = z * (a * z * a⁻¹)) →
            p ^ (3 * n) ∣ Nat.card ↥X

@[expose] def Ch6P56bSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 2 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      ∀ (z t : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂],
        Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ (H : Subgroup G) (w₁ w₂ : G), T2Four z t K₁ K₂ H w₁ w₂ →
            ∀ y ∈ H, (y ∈ K₁ ∨ y ∈ K₂) → y ∉ Subgroup.zpowers z → (orderOf y).Prime →
              Odd (orderOf y) → HasSDOrWreathedSylow ↥(centralizer ({y} : Set G))

theorem ch6P56bOrder_of_leaves (hABG : ABGKFusion) (hSyl : Ch6P56bSylow) : Ch6P56bOrder := by
  intro G _ _ hStd hr Gs _ n hn hAt z t K₁ K₂ F₁ F₂ _ _ hSet hRem H w₁ w₂ hT a haN ha3 haz hat y hyH hyK
    hyz hyp hyodd hay
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyp
    exact Nat.not_prime_one hyp
  have hX : centralizer ({y} : Set G) ≠ ⊤ := by
    intro htop
    have hy : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ centralizer ({y} : Set G) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have hsimple : IsSimpleGroup G := hStd.kps.1
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0] at hy
      exact hy1 (Subgroup.mem_bot.1 hy)
    · obtain ⟨b, c, hbc⟩ := hStd.kps.2.1
      apply hbc
      have := Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) b
      exact this
  have hKX := hStd.kps.isKGroupNative_of_ne_top hX
  have hSylX := hSyl G hStd hr Gs n hn hAt z t K₁ K₂ F₁ F₂ hSet hRem H w₁ w₂ hT y hyH hyK hyz hyp hyodd
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT.zz) hT.z_ne
  have hzX : z ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hT.H_comm z hT.z_mem_H y hyH)
  have haX : a ∈ centralizer ({y} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [hay]
  have hz₁ : z ∈ K₁ := hT.w₁_sq ▸ K₁.mul_mem hT.w₁_mem hT.w₁_mem
  have hz₂ : z ∈ K₂ := hT.w₂_sq ▸ K₂.mul_mem hT.w₂_mem hT.w₂_mem
  have hfuse : ∃ a ∈ centralizer ({y} : Set G), a * z * a⁻¹ ≠ z ∧ (a * z * a⁻¹) * z = z * (a * z * a⁻¹) := by
    refine ⟨a, haX, ?_, ?_⟩
    · intro h
      have h1 : z * a = a * z := by
        calc z * a = (a * z * a⁻¹) * a := by rw [h]
          _ = a * z := by group
      have h2 : a⁻¹ * z * a = z := by
        calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
          _ = a⁻¹ * (a * z) := by rw [h1]
          _ = z := by group
      exact hT.zu_ne (h2.symm.trans haz)
    · have h3 : a * a * a = 1 := by simpa [pow_succ] using ha3
      have h3' : a * (a * a) = 1 := by rw [← mul_assoc]; exact h3
      have e1 : z = a * t * a⁻¹ := by rw [← haz]; group
      have e2 : a * a = a⁻¹ := eq_inv_of_mul_eq_one_right h3'
      have hconj : a * z * a⁻¹ = z * t := by
        calc a * z * a⁻¹ = a * (a * t * a⁻¹) * a⁻¹ := by rw [← e1]
          _ = (a * a) * t * (a * a)⁻¹ := by group
          _ = a⁻¹ * t * (a⁻¹)⁻¹ := by rw [e2]
          _ = a⁻¹ * t * a := by group
          _ = z * t := hat
      rw [hconj]
      calc z * t * z = z * (t * z) := by group
        _ = z * (z * t) := by rw [← hT.zu_comm]
  have hSL₁ : HasSL2Model ↥K₁ (fun q => q = 3 ^ n) := by
    obtain ⟨e⟩ := hSet.iso₁
    exact ⟨F₁, inferInstance, hSet.finite₁, hSet.card₁,
      ⟨e.trans (specialLinearGroupEquivStatedSL 2 F₁)⟩⟩
  have hSL₂ : HasSL2Model ↥K₂ (fun q => q = 3 ^ n) := by
    obtain ⟨e⟩ := hSet.iso₂
    exact ⟨F₂, inferInstance, hSet.finite₂, hSet.card₂,
      ⟨e.trans (specialLinearGroupEquivStatedSL 2 F₂)⟩⟩
  have hnorm₁ : ∀ c ∈ centralizer ({y} : Set G), c * z = z * c → ∀ k ∈ K₁, c * k * c⁻¹ ∈ K₁ :=
    fun c _ hc k hk => hT.C_norm₁ c (Subgroup.mem_centralizer_singleton_iff.2 hc) k hk
  have hnorm₂ : ∀ c ∈ centralizer ({y} : Set G), c * z = z * c → ∀ k ∈ K₂, c * k * c⁻¹ ∈ K₂ :=
    fun c _ hc k hk => hT.C_norm₂ c (Subgroup.mem_centralizer_singleton_iff.2 hc) k hk
  have h5 : 5 ≤ 3 ^ n := by
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases hyK with hy₁ | hy₂
  · refine hABG G (centralizer ({y} : Set G)) hKX hSylX 3 n Nat.prime_three (by norm_num) h5 z hzX hz2 K₂ ?_ hz₂ hSL₂ hnorm₂ hfuse
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 (hT.K_comm y hy₁ k hk).symm
  · refine hABG G (centralizer ({y} : Set G)) hKX hSylX 3 n Nat.prime_three (by norm_num) h5 z hzX hz2 K₁ ?_ hz₁ hSL₁ hnorm₁ hfuse
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.2 (hT.K_comm k hk y hy₂)

end CFSG.GH74.GLS.Stage4.Rest

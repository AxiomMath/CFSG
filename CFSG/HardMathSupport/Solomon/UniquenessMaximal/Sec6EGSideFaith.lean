module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem faithful_core {G : Type*} [Group G] [Finite G] (B K F : Subgroup G)
    (hBcomm : ∀ y ∈ B, ∀ z ∈ B, y * z = z * y)
    (hFB : F ≤ B) (hBK : ∀ y ∈ B, y ∈ K → y ∈ F)
    (hBnorm : ∀ y ∈ B, ∀ z ∈ K, y * z * y⁻¹ ∈ K)
    (hexp : ∀ x ∈ F, x ^ 3 = 1)
    (hP : ∀ P : Subgroup ↥K, IsPGroup 3 P →
      P ≤ Subgroup.centralizer ((F.subgroupOf K : Subgroup ↥K) : Set ↥K) →
        F.subgroupOf K ≤ P → P ≤ F.subgroupOf K)
    {k : G} (hk : k ∈ K) (hkB : ∀ y ∈ B, k * y * k⁻¹ ∈ B)
    (hkF : ∀ f ∈ F, k * f * k⁻¹ = f) :
    ∀ y ∈ B, k * y * k⁻¹ = y := by
  have hcF : ∀ y ∈ B, k * y * k⁻¹ * y⁻¹ ∈ F := by
    intro y hy
    apply hBK
    · exact B.mul_mem (hkB y hy) (B.inv_mem hy)
    · have : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹) := by group
      rw [this]
      exact K.mul_mem hk (hBnorm y hy k⁻¹ (K.inv_mem hk))
  have hk3 : ∀ y ∈ B, k ^ 3 * y = y * k ^ 3 := by
    intro y hy
    obtain ⟨u, hu_def⟩ : ∃ u, u = k * y * k⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hu : u ∈ F := hu_def ▸ hcF y hy
    have hy1 : k * y * k⁻¹ = u * y := by rw [hu_def]; group
    have hku : k * u * k⁻¹ = u := hkF u hu
    have hu3 : u * u * u = 1 := by
      have := hexp u hu
      rw [pow_succ, pow_two] at this
      exact this
    have e : ∀ z, k * (u * z) * k⁻¹ = u * (k * z * k⁻¹) := by
      intro z
      calc k * (u * z) * k⁻¹ = (k * u * k⁻¹) * (k * z * k⁻¹) := by group
        _ = u * (k * z * k⁻¹) := by rw [hku]
    have h3 : k * (k * (k * y * k⁻¹) * k⁻¹) * k⁻¹ = u * (u * (u * y)) := by
      rw [hy1, e, hy1, e, e, hy1]
    have h4 : u * (u * (u * y)) = y := by
      rw [← mul_assoc, ← mul_assoc, hu3, one_mul]
    have h5 : k * (k * (k * y * k⁻¹) * k⁻¹) * k⁻¹ = k ^ 3 * y * (k ^ 3)⁻¹ := by rw [pow_three]; group
    rw [h5] at h3
    have : k ^ 3 * y * (k ^ 3)⁻¹ = y := h3.trans h4
    calc k ^ 3 * y = k ^ 3 * y * (k ^ 3)⁻¹ * k ^ 3 := by group
      _ = y * k ^ 3 := by rw [this]
  have ho : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨e, m, hm3, hem⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 3 (by norm_num)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m * j % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, m * j = 3 * t + 1 := ⟨m * j / 3, by omega⟩
  set kk : ↥K := ⟨k, hk⟩ with hkk
  set n : ↥K := kk ^ (m * j) with hn
  have hn_coe : (n : G) = k ^ (m * j) := by simp [hn, hkk]
  have hn_pow : n ^ (3 ^ e) = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, hn_coe, Subgroup.coe_one]
    rw [← pow_mul]
    have : m * j * 3 ^ e = orderOf k * j := by rw [hem]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  have hn_act : ∀ y ∈ B, (n : G) * y * (n : G)⁻¹ = k * y * k⁻¹ := by
    intro y hy
    have hcen : ∀ z ∈ B, (k ^ 3) ^ t * z = z * (k ^ 3) ^ t := by
      intro z hz
      have : (k ^ 3) ^ t ∈ Subgroup.centralizer (B : Set G) := by
        apply Subgroup.pow_mem
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact (hk3 h hh).symm
      rw [Subgroup.mem_centralizer_iff] at this
      exact (this z hz).symm
    have hnk : (n : G) = (k ^ 3) ^ t * k := by
      rw [hn_coe, ht, ← pow_mul, ← pow_succ]
    rw [hnk]
    have h1 : (k ^ 3) ^ t * k * y * ((k ^ 3) ^ t * k)⁻¹ =
        (k ^ 3) ^ t * (k * y * k⁻¹) * ((k ^ 3) ^ t)⁻¹ := by group
    rw [h1, hcen _ (hkB y hy)]
    group
  set F' : Subgroup ↥K := F.subgroupOf K with hF'
  have hF'comm : ∀ a ∈ F', ∀ b ∈ F', a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (hBcomm a (hFB ha) b (hFB hb))
  have hncen : n ∈ Subgroup.centralizer (F' : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply Subtype.ext
    have h1 : k * (h : G) * k⁻¹ = h := hkF h hh
    have h2 : (h : G) * k = k * h := by
      have : k * (h : G) * k⁻¹ * k = (h : G) * k := by rw [h1]
      rw [← this]; group
    have h3 : (h : G) * (n : G) = (n : G) * h := by
      rw [hn_coe]
      have : ∀ i : ℕ, (h : G) * k ^ i = k ^ i * h := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h2, ← mul_assoc]
      exact this _
    simpa using h3
  have hz_le : Subgroup.zpowers n ≤ Subgroup.centralizer (F' : Set ↥K) :=
    (Subgroup.zpowers_le).2 hncen
  have hF'_le : F' ≤ Subgroup.centralizer (F' : Set ↥K) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hF'comm h hh b hb
  have hF'p : IsPGroup 3 F' := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hexp _ g.2
  have hzp : IsPGroup 3 (Subgroup.zpowers n) := by
    have hdvd : orderOf n ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hn_pow
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have : Nat.card (Subgroup.zpowers n) = 3 ^ i := by rw [Nat.card_zpowers, hi]
    exact IsPGroup.of_card this
  have hnorm : F' ≤ Subgroup.normalizer ((Subgroup.zpowers n : Subgroup ↥K) : Set ↥K) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ f ∈ F', ∀ h' ∈ Subgroup.zpowers n, f * h' * f⁻¹ = h' := by
      intro f hf h' hh'
      have := (Subgroup.mem_centralizer_iff.1 (hz_le hh')) f hf
      rw [this]; group
    constructor
    · intro hh; rw [hc f hf h hh]; exact hh
    · intro hh
      have h1 := hc f⁻¹ (F'.inv_mem hf) _ hh
      have h2 : f⁻¹ * (f * h * f⁻¹) * f⁻¹⁻¹ = h := by group
      rw [h2] at h1
      rw [h1]; exact hh
  have hPp : IsPGroup 3 (F' ⊔ Subgroup.zpowers n : Subgroup ↥K) :=
    hF'p.to_sup_of_normal_right' hzp hnorm
  have hnF' : n ∈ F' :=
    hP _ hPp (sup_le hF'_le hz_le) le_sup_left
      ((le_sup_right : Subgroup.zpowers n ≤ F' ⊔ Subgroup.zpowers n) (Subgroup.mem_zpowers n))
  have hnF : (n : G) ∈ F := hnF'
  intro y hy
  rw [← hn_act y hy]
  have := hBcomm _ (hFB hnF) y hy
  rw [this]; group

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

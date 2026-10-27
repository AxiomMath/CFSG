module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoC2
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6HeisSD

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

open Subgroup CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem sd_or_q16 {M : Subgroup G} (hcard : Nat.card M = 16) {a q : G} (haM : a ∈ M)
    (hqM : q ∈ M) (ha : orderOf a = 8) (hq2 : q ^ 2 = a ^ 4)
    (hqa : q * a ^ 2 * q⁻¹ = (a ^ 2)⁻¹) :
    Nonempty (↥M ≃* SemidihedralGroup 4) ∨ Sec622UniqueInv M := by
  have hA : zpowers a ≤ M := (zpowers_le).mpr haM
  have hcA : Nat.card (zpowers a) = 8 := by rw [Nat.card_zpowers, ha]
  have hrel : (zpowers a).relIndex M = 2 := by
    have := Subgroup.relIndex_mul_card (zpowers a) M
    rw [inf_of_le_left hA, hcA, hcard] at this
    omega
  have ha8 : a ^ 8 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha4 : a ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [ha]; norm_num)
  have hnorm : ((zpowers a).subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hrel
  have hconj : q * a * q⁻¹ ∈ zpowers a := by
    have := hnorm.conj_mem ⟨a, haM⟩ (Subgroup.mem_subgroupOf.mpr (mem_zpowers a)) ⟨q, hqM⟩
    simpa [Subgroup.mem_subgroupOf] using this
  obtain ⟨k, hk, hqak⟩ := exists_pow_lt_of_mem_zpowers (by norm_num : 0 < 8) ha8 hconj
  have hk' : k = 3 ∨ k = 7 := by
    have h1 : (a ^ k) ^ 2 = (a ^ 2)⁻¹ := by
      rw [← hqak, ← hqa, pow_two (q * a * q⁻¹), pow_two a]; group
    have h2 : a ^ (2 * k + 2) = 1 := by
      calc a ^ (2 * k + 2) = (a ^ k) ^ 2 * a ^ 2 := by rw [← pow_mul, ← pow_add, mul_comm k 2]
        _ = 1 := by rw [h1]; exact inv_mul_cancel _
    have h3 : 8 ∣ 2 * k + 2 := ha ▸ orderOf_dvd_of_pow_eq_one h2
    omega
  rcases hk' with rfl | rfl
  · left
    have hs2 : (q * a) ^ 2 = 1 := by
      calc (q * a) ^ 2 = (q * a * q⁻¹) * q ^ 2 * a := by rw [pow_two (q * a), pow_two q]; group
        _ = a ^ 3 * a ^ 4 * a := by rw [hqak, hq2]
        _ = a ^ 8 := by group
        _ = 1 := ha8
    have hsa : (q * a) * a * (q * a)⁻¹ = a ^ 3 := by
      calc (q * a) * a * (q * a)⁻¹ = q * a * q⁻¹ := by group
        _ = a ^ 3 := hqak
    obtain ⟨hc16, ⟨e⟩⟩ := CFSG.Quasithin.SzN31.SmD6Heis.closure_semidihedral_four ha8 ha4 hs2 hsa
    have hle : closure ({a, q * a} : Set G) ≤ M := by
      rw [closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact haM
      · exact mul_mem hqM haM
    have hfin : Finite M := inferInstance
    have heq : closure ({a, q * a} : Set G) = M :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc16, hcard])
    exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩
  · right
    have hq_not : q ∉ zpowers a := by
      intro hq
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hq
      have hcomm : a ^ j * a = a * a ^ j := ((Commute.refl a).zpow_left j).eq
      have h1 : a ^ j * a * (a ^ j)⁻¹ = a := by rw [hcomm]; group
      rw [h1] at hqak
      have h2 : a ^ 6 = 1 := by
        have : a * a ^ 6 = a * 1 := by rw [mul_one, ← pow_succ']; exact hqak.symm
        exact mul_left_cancel this
      have := orderOf_dvd_of_pow_eq_one h2
      rw [ha] at this
      omega
    have hspan : ∀ e ∈ M, e ∈ zpowers a ∨ e * q⁻¹ ∈ zpowers a := by
      intro e he
      by_cases h : e ∈ zpowers a
      · exact Or.inl h
      · right
        refine (mul_mem_iff_of_relIndex_two hrel he (inv_mem hqM)).mpr ⟨fun h' => absurd h' h,
          fun h' => absurd (inv_mem_iff.mp h') hq_not⟩
    have hinv : ∀ e ∈ M, orderOf e = 2 → e = a ^ 4 := by
      intro e he he2
      have he2' : e ^ 2 = 1 := by rw [← he2]; exact pow_orderOf_eq_one e
      rcases hspan e he with h | h
      · obtain ⟨i, hi, rfl⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) ha8 h
        have h1 : a ^ (i * 2) = 1 := by rw [pow_mul]; exact he2'
        have h8 : 8 ∣ i * 2 := ha ▸ orderOf_dvd_of_pow_eq_one h1
        have : i = 0 ∨ i = 4 := by omega
        rcases this with rfl | rfl
        · exfalso
          rw [pow_zero, orderOf_one] at he2
          omega
        · rfl
      · obtain ⟨i, hi, hρ⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) ha8 h
        have he' : e = a ^ i * q := by
          calc e = (e * q⁻¹) * q := by group
            _ = a ^ i * q := by rw [hρ]
        have hqi : q * a ^ i * q⁻¹ = (a ^ 7) ^ i := by rw [← hqak, conj_pow]
        have hai : a ^ i * (a ^ 7) ^ i = 1 := by
          rw [← pow_mul, ← pow_add, show i + 7 * i = 8 * i by ring, pow_mul, ha8, one_pow]
        have hsq : e ^ 2 = a ^ 4 := by
          calc e ^ 2 = a ^ i * (q * a ^ i * q⁻¹) * q ^ 2 := by
                rw [he', pow_two (a ^ i * q), pow_two q]; group
            _ = a ^ i * (a ^ 7) ^ i * a ^ 4 := by rw [hqi, hq2]
            _ = a ^ 4 := by rw [hai, one_mul]
        exact absurd (hsq.symm.trans he2') ha4
    exact fun e₁ h₁ e₂ h₂ o₁ o₂ => (hinv e₁ h₁ o₁).trans (hinv e₂ h₂ o₂).symm

theorem case_two_finish {M : Subgroup G} {y q m a : G} (c : Config M y q m)
    (hqy : q * y * q⁻¹ = y⁻¹) (haM : a ∈ M) {e : ℕ} (he : e % 2 = 1) (ha2 : a ^ 2 = y ^ e) :
    Nonempty (↥M ≃* SemidihedralGroup 4) ∨ Sec622UniqueInv M := by
  have ht0 := c.t0
  have hy4 := ht0.y_pow_four
  have hy2e : y ^ (e * 2) = y ^ 2 := by
    rw [pow_eq_pow_iff_of_orderOf_four ht0.ord]; omega
  have ha4 : a ^ 4 = y ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2, ← pow_mul, hy2e]
  have ha : orderOf a = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h8 : orderOf a = 2 ^ (2 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 2)
        (by rw [show 2 ^ 2 = 4 from rfl, ha4]; exact ht0.y_sq_ne_one)
        (by rw [show 2 ^ (2 + 1) = 4 * 2 from rfl, pow_mul, ha4, ← pow_mul]; exact hy4)
    simpa using h8
  refine sd_or_q16 c.card haM c.w_mem ha (by rw [ht0.sq, ha4]) ?_
  rw [ha2, ← conj_pow, hqy, inv_pow]

theorem case_two {M : Subgroup G} {t y q m : G} (c : Config M y q m) (hqy : q * y * q⁻¹ = y⁻¹)
    (htq : t * q = q * t) (hty : t * y * t⁻¹ = y⁻¹) {ε κ : ℕ} (hε : ε % 2 = 1)
    (hκ : κ % 2 = 1) (hmt : m * t * m⁻¹ = y ^ ε * t) (hmq : m * q * m⁻¹ = y ^ κ * q)
    (hmy : m * y * m⁻¹ = y ∨ m * y * m⁻¹ = y⁻¹) :
    Nonempty (↥M ≃* SemidihedralGroup 4) ∨ Sec622UniqueInv M := by
  have ht0 := c.t0
  have hy4 := ht0.y_pow_four
  obtain ⟨α, β, hα, hβ, hm2⟩ := (ht0.mem_closure_iff c.wy).mp c.m_sq
  have hpar := parity ht0.ord hty htq hε hmt hm2
  have hsq : SemiconjBy m q (y ^ κ * q) := mul_inv_eq_iff_eq_mul.mp hmq
  have hβ0 : β = 0 := by
    by_contra hβ'
    have hβ1 : β = 1 := by omega
    subst hβ1
    rw [pow_one] at hm2
    have key : ∀ y' : G, m * y * m⁻¹ = y' → y ^ α = y' ^ α * y ^ κ := by
      intro y' hy'
      have hs : SemiconjBy m y y' := mul_inv_eq_iff_eq_mul.mp hy'
      have h1 : m * (y ^ α * q) = (y' ^ α * (y ^ κ * q)) * m :=
        ((hs.pow_right α).mul_right hsq).eq
      have h2 : m * (y ^ α * q) = (y ^ α * q) * m := by rw [← hm2]; group
      rw [h2] at h1
      have h3 := mul_right_cancel h1
      rw [← mul_assoc] at h3
      exact mul_right_cancel h3
    rcases hmy with hδ | hδ
    · have h1 := key y hδ
      have h2 : y ^ (α + κ) = y ^ (α + 0) := by
        rw [pow_add, pow_add, pow_zero, mul_one]; exact h1.symm
      rw [pow_eq_pow_iff_of_orderOf_four ht0.ord] at h2
      omega
    · have h1 := key y⁻¹ hδ
      have h0 := hpar.2 hδ
      rw [inv_eq_pow_three hy4, ← pow_mul, ← pow_add, pow_eq_pow_iff_of_orderOf_four ht0.ord] at h1
      omega
  subst hβ0
  have hm2' : m ^ 2 = y ^ α := by rw [hm2]; simp
  rcases hmy with hδ | hδ
  · exact case_two_finish c hqy c.m_mem (hpar.1 hδ) hm2'
  · have h0 := hpar.2 hδ
    have hqs : SemiconjBy q y y⁻¹ := mul_inv_eq_iff_eq_mul.mp hqy
    have e2 : q * y ^ α = y⁻¹ ^ α * q := (hqs.pow_right α).eq
    have ha2 : (m * q) ^ 2 = y ^ (κ + 3 * α + 2) := by
      calc (m * q) ^ 2 = (m * q * m⁻¹) * m ^ 2 * q := by
            rw [pow_two (m * q), pow_two m]; group
        _ = (y ^ κ * q) * y ^ α * q := by rw [hmq, hm2']
        _ = y ^ κ * (q * y ^ α) * q := by group
        _ = y ^ κ * (y⁻¹ ^ α * q) * q := by rw [e2]
        _ = y ^ κ * y⁻¹ ^ α * q ^ 2 := by rw [pow_two q]; group
        _ = y ^ (κ + 3 * α + 2) := by
          rw [ht0.sq, inv_eq_pow_three hy4, ← pow_mul, ← pow_add, ← pow_add]
    exact case_two_finish c hqy (mul_mem c.m_mem c.w_mem) (by omega) ha2

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

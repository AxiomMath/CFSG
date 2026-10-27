module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem caseC3_false_of_transfer {H : Type*} [Group H] [Finite H] (hperf : commutator H = ⊤)
    {S T W : Subgroup H} (hS : Nat.Coprime 2 S.index) (hTS : T ≤ S)
    (hTn : ∀ t ∈ T, ∀ s ∈ S, s * t * s⁻¹ ∈ T)
    (hidx : ∀ a ∈ S, a ∉ T → ∀ b ∈ S, b ∉ T → a * b ∈ T)
    (hexp : ∀ t ∈ T, t ^ 4 = 1) (hsq : ∀ s ∈ S, s ∉ T → s * s ∉ W)
    (Gen : H → Prop) (hGconj : ∀ a b : H, Gen a → Gen (b⁻¹ * a * b))
    (hGen : ∀ t ∈ T, Gen t → t ≠ 1 → t ∈ W)
    {g : H} (hgS : g ∈ S) (hgT : g ∉ T) (hg4 : g ^ 4 ≠ 1) (hgen : Gen (g ^ 4)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg2 : g ^ 2 ∈ T := by
    rw [pow_two]
    exact hidx g hgS hgT g hgS hgT
  have hg8 : g ^ 8 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul]
    exact hexp _ hg2
  have hinvmul : ∀ a ∈ S, a ∉ T → ∀ b ∈ S, b ∉ T → a⁻¹ * b ∈ T := fun a ha haT b hb hbT =>
    hidx a⁻¹ (S.inv_mem ha) (fun h => haT (by simpa using T.inv_mem h)) b hb hbT
  have key : ∀ a z : H, a⁻¹ * z * a = 1 → z = 1 := fun a z hz => by
    rw [show z = a * (a⁻¹ * z * a) * a⁻¹ by group, hz]
    group
  refine CFSG.Quasithin.generalized_thompson_transfer_one (p := 2) hS ⟨hTS, ?_⟩ ?_ hgS hgT
    ⟨3, by norm_num [hg8]⟩ ?_ (by rw [hperf]; exact Subgroup.mem_top g)
  · rw [Subgroup.normal_subgroupOf_iff hTS]
    intro t s ht hs
    exact hTn t ht s hs
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    by_cases haT : a ∈ T
    · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact T.mul_mem haT (hTn _ (T.inv_mem haT) b hb)
    · by_cases hbT : b ∈ T
      · exact T.mul_mem (hTn b hbT a ha) (T.inv_mem hbT)
      · rw [show a * b * a⁻¹ * b⁻¹ = (a * b) * (b * a)⁻¹ by group]
        exact T.mul_mem (hidx a ha haT b hb hbT) (T.inv_mem (hidx b hb hbT a ha haT))
  · intro m a ha
    rw [zpow_eq_zpow_emod' m hg8] at ha ⊢
    obtain ⟨r, hr⟩ : ∃ r : ℕ, m % ((8 : ℕ) : ℤ) = r :=
      ⟨(m % ((8 : ℕ) : ℤ)).toNat, by
        have := Int.emod_nonneg m (show ((8 : ℕ) : ℤ) ≠ 0 by norm_num)
        omega⟩
    have hr8 : r < 8 := by
      have := Int.emod_lt_of_pos m (show (0 : ℤ) < ((8 : ℕ) : ℤ) by norm_num)
      omega
    rw [hr, zpow_natCast] at ha ⊢
    set c := a⁻¹ * g ^ r * a with hc
    have hcpow : ∀ k : ℕ, c ^ k = a⁻¹ * g ^ (r * k) * a := fun k => by
      have := map_pow (MulAut.conj a⁻¹) (g ^ r) k
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [hc, ← this, ← pow_mul]
    rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hgr : g ^ r ∈ T := by
        rw [hk, ← two_mul, pow_mul]
        exact T.pow_mem hg2 k
      refine T.mul_mem (T.inv_mem hgr) ?_
      by_contra hcT
      have hc2 := hsq c ha hcT
      have hc2T := hidx c ha hcT c ha hcT
      have hcc : c * c = a⁻¹ * g ^ (r * 2) * a := by rw [← pow_two, hcpow 2]
      have hr' : r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6 := by omega
      rcases hr' with rfl | rfl | rfl | rfl
      · exact hc2 (by rw [hcc]; simp)
      · apply hc2
        rw [hcc] at hc2T ⊢
        exact hGen _ hc2T (hGconj _ a hgen) fun h1 => hg4 (key a _ h1)
      · exact hc2 (by rw [hcc, show 4 * 2 = 8 by norm_num, hg8]; simp)
      · apply hc2
        have h12 : g ^ (6 * 2) = g ^ 4 := by
          rw [show 6 * 2 = 8 + 4 by norm_num, pow_add, hg8, one_mul]
        rw [hcc, h12] at hc2T ⊢
        exact hGen _ hc2T (hGconj _ a hgen) fun h1 => hg4 (key a _ h1)
    · have h4r : g ^ (r * 4) = g ^ 4 := by
        rw [hk, show (2 * k + 1) * 4 = 8 * k + 4 by ring, pow_add, pow_mul, hg8, one_pow,
          one_mul]
      have hgrT : g ^ r ∉ T := fun h' => hg4 (by rw [← h4r, pow_mul]; exact hexp _ h')
      have hcT : c ∉ T := fun h' => hg4 (by
        have := hexp c h'
        rw [hcpow 4, h4r] at this
        exact key a _ this)
      exact hinvmul _ (S.pow_mem hgS r) hgrT c ha hcT

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

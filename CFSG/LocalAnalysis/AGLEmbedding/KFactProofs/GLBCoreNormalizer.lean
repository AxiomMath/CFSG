module

import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34LocalGroup
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer

open CFSG.Open

variable {K : Type*} [Group K] [Finite K] {p : ℕ}

theorem one_le_pRank_of_dvd (hp : p.Prime) {T : Subgroup K} (h : p ∣ Nat.card T) :
    1 ≤ pRank p T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  have hxo : orderOf (x : K) = p := by
    rw [Subgroup.orderOf_coe, hx]
  have hxp : (x : K) ^ p = 1 := by
    rw [← hxo]
    exact pow_orderOf_eq_one _
  have hel : IsElemAbelian p (Subgroup.zpowers (x : K)) := by
    refine ⟨inferInstance, fun z hz => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  exact CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.zpowers_le.2 x.2) hel
    (by rw [Nat.card_zpowers, hxo, pow_one])

theorem glbCore_le_normalizer (hp : p.Prime) {T : Subgroup K}
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hC : ∀ t ∈ T, t ≠ 1 → ∀ g : K, g * t = t * g → g ∈ T) :
    GLBCore p 1 T ≤ Subgroup.normalizer (T : Set K) := by
  have key : ∀ Q : Subgroup K, Q ≤ T → Q ≠ ⊥ → ∀ g ∈ Subgroup.normalizer (Q : Set K),
      ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
    intro Q hQT hQ g hg x hx
    obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
    have hq' : g * (q : K) * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg q).1 q.2
    refine hC (g * q * g⁻¹) (hQT hq') ?_ _ ?_
    · intro h1
      apply hq
      have : (q : K) = 1 := by
        have h2 : g⁻¹ * (g * (q : K) * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
        simpa [mul_assoc] using h2
      exact Subtype.ext this
    · have := hcomm x hx q (hQT q.2)
      calc g * x * g⁻¹ * (g * q * g⁻¹) = g * (x * q) * g⁻¹ := by group
        _ = g * (q * x) * g⁻¹ := by rw [this]
        _ = g * q * g⁻¹ * (g * x * g⁻¹) := by group
  unfold GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQT, hQ, rfl⟩
  have hQ' : Q ≠ ⊥ := KFactProofs.L34Local.LocalData.ne_bot_of_one_le_pRank hp.two_le hQ
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key Q hQT hQ' g hg x
  · intro hx
    have := key Q hQT hQ' g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem glbCore_eq_normalizer (hp : p.Prime) {T : Subgroup K} (hdvd : p ∣ Nat.card T)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hC : ∀ t ∈ T, t ≠ 1 → ∀ g : K, g * t = t * g → g ∈ T) :
    GLBCore p 1 T = Subgroup.normalizer (T : Set K) :=
  le_antisymm (glbCore_le_normalizer hp hcomm hC)
    (le_sSup ⟨T, le_rfl, one_le_pRank_of_dvd hp hdvd, rfl⟩)

end CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoFiveJ1

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Walter CFSG.Walter.J1Props

namespace JankoFive

theorem card_centralizer_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card (centralizer ({a} : Set A)) = Nat.card (centralizer ({e a} : Set B)) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    show x * a = a * x ↔ e x * e a = e a * e x
    rw [← map_mul, ← map_mul, e.injective.eq_iff])

end JankoFive

namespace JankoSetting

variable {Γ : Type} [Group Γ] [Finite Γ] {f t r r₁ : Γ} {D E : Subgroup Γ}
  (h : JankoSetting Γ f t r r₁ D E)

include h

theorem comm_of_mem_zpowers_of_three {r' c : Γ} (hr' : orderOf r' = 3)
    (hc : (r' * c)⁻¹ * (c * r') ∈ zpowers f) : c * r' = r' * c := by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hc
  have hct : c * r' * c⁻¹ = r' * f ^ j := by
    calc c * r' * c⁻¹ = (r' * c) * ((r' * c)⁻¹ * (c * r')) * c⁻¹ := by group
      _ = r' * (c * f ^ j * c⁻¹) := by rw [hj]; group
      _ = r' * f ^ j := by rw [h.zpow_comm c j]; group
  have h3 : r' ^ 3 = 1 := hr' ▸ pow_orderOf_eq_one r'
  have h1 : f ^ (j * 3) = 1 := by
    have e : (c * r' * c⁻¹) ^ 3 = 1 := by rw [conj_pow, h3]; group
    rw [hct, Commute.mul_pow (a := r') (b := f ^ j) (h.zpow_comm r' j) 3, h3, one_mul,
      ← zpow_natCast, ← zpow_mul] at e
    simpa using e
  have h2 : ((orderOf f : ℕ) : ℤ) ∣ j * 3 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [h.f_ord] at h2
  have h5 : ((5 : ℕ) : ℤ) ∣ j := by push_cast at h2 ⊢; omega
  have hj1 : f ^ j = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, h.f_ord]; exact h5
  have h4 : c * r' * c⁻¹ = r' := by rw [hct, hj1, mul_one]
  calc c * r' = (c * r' * c⁻¹) * c := by group
    _ = r' * c := by rw [h4]

theorem five_dvd_centralizer_three {r' : Γ} (hr' : orderOf r' = 3) :
    25 ∣ Nat.card ↥(centralizer ({r'} : Set Γ)) := by
  have hN := h.normal_zpowers
  obtain ⟨e⟩ := h.jankoHyp.nonempty_mulEquiv_walterJ1
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : r' ^ 3 = 1 := hr' ▸ pow_orderOf_eq_one r'
  have hπ1 : (QuotientGroup.mk r' : Γ ⧸ zpowers f) ≠ 1 := by
    intro h1
    have hd := orderOf_dvd_of_mem_zpowers ((QuotientGroup.eq_one_iff r').1 h1)
    rw [hr', h.f_ord] at hd
    omega
  have hπord : orderOf (QuotientGroup.mk r' : Γ ⧸ zpowers f) = 3 := by
    refine orderOf_eq_prime ?_ hπ1
    rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
  have hs : orderOf (e (QuotientGroup.mk r')) = 3 := by
    rw [MulEquiv.orderOf_eq]; exact hπord
  have h5 := walterJ1_three_five _ hs
  rw [← JankoFive.card_centralizer_mulEquiv e] at h5
  have hpre : ∀ c : Γ, c ∈ centralizer ({r'} : Set Γ) ↔
      (QuotientGroup.mk c : Γ ⧸ zpowers f) ∈
        centralizer ({(QuotientGroup.mk r' : Γ ⧸ zpowers f)} : Set (Γ ⧸ zpowers f)) := by
    intro c
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hc
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
    · intro hc
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
      exact h.comm_of_mem_zpowers_of_three hr' (QuotientGroup.eq.1 hc.symm)
  have hcard : Nat.card ↥(centralizer ({r'} : Set Γ)) = Nat.card (zpowers f) *
      Nat.card ↥(centralizer ({(QuotientGroup.mk r' : Γ ⧸ zpowers f)} : Set (Γ ⧸ zpowers f))) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.subtypeEquivRight hpre)).trans
      (Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet (zpowers f) _))
  rw [hcard, Nat.card_zpowers, h.f_ord]
  exact Nat.mul_dvd_mul_left 5 h5

end JankoSetting

end CFSG.EvenSporadicStandard.RuStd.S2

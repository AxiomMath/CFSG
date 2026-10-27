module

public import CFSG.GH74.GLS.IVK.Proofs2.PglKGamma
public import CFSG.GH74.GLS.IVK.Proofs2.PglKCoatom

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section CentralizerLE

variable {K : Type} [Group K] [Finite K]

theorem false_of_centralizer_le_of_not_mem (hD4 : HasD4Centralizers K) (hs : IsSimpleGroup K)
    (hKcard : Nat.card K = 168 ∨ Nat.card K = 360) {V₀ : Subgroup K} (hV4 : Nat.card ↥V₀ = 4)
    (hVcomm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a) (hVsq : ∀ a ∈ V₀, a ^ 2 = 1)
    {z₀ s₀ : K} (hz₀ : z₀ ∈ V₀) (hz₀1 : z₀ ≠ 1) (hs₀ : orderOf s₀ = 2) (hs₀V : s₀ ∉ V₀)
    (hcomm : s₀ * z₀ = z₀ * s₀) {Γ : Subgroup K} (hΓtop : Γ ≠ ⊤)
    (hΓV : ∀ u ∈ V₀, u ≠ 1 → centralizer ({u} : Set K) ≤ Γ)
    (hΓs : centralizer ({s₀} : Set K) ≤ Γ) : False := by
  have hVord : ∀ u ∈ V₀, u ≠ 1 → orderOf u = 2 := fun u hu hu1 =>
    orderOf_eq_prime (hVsq u hu) hu1
  obtain ⟨u₁, hu₁, u₂, hu₂, hu₁1, hu₂1, hu₁₂⟩ :=
    CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hV4
  have h₁ := hVord u₁ hu₁ hu₁1
  have h₂ := hVord u₂ hu₂ hu₂1
  have hcomm12 := hVcomm u₁ hu₁ u₂ hu₂
  have h16 : ¬ 16 ∣ Nat.card K := by
    rcases hKcard with h | h <;> rw [h] <;> norm_num
  obtain ⟨hV1, hN1⟩ := le_centralizer_normalizer_of_d4 hD4 hV4 hVcomm hu₁ h₁
  obtain ⟨-, hN2⟩ := le_centralizer_normalizer_of_d4 hD4 hV4 hVcomm hu₂ h₂
  have hG0N : centralizer ({u₁} : Set K) ⊔ centralizer ({u₂} : Set K) ≤
      normalizer (V₀ : Set K) := sup_le hN1 hN2
  have hG0 := card_gamma_eq_of_d4 hD4 hV4 hu₁ hu₂ h₁ h₂ hu₁₂ hcomm12 h16 le_sup_left le_sup_right
    hG0N
  have hcoat := isCoatom_of_card_24 hs hKcard _ hG0
  have hΓeq : Γ = centralizer ({u₁} : Set K) ⊔ centralizer ({u₂} : Set K) :=
    (hcoat.le_iff_eq hΓtop).1 (sup_le (hΓV u₁ hu₁ hu₁1) (hΓV u₂ hu₂ hu₂1))
  rw [← hΓeq] at hG0 hG0N
  have hVΓ : V₀ ≤ Γ := hV1.trans (hΓV u₁ hu₁ hu₁1)
  have hVn : (V₀.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ((Subgroup.mem_normalizer_iff.1 (hG0N g.2) _).1 hn)⟩
  have hVcard : Nat.card ↥(V₀.subgroupOf Γ) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVΓ).toEquiv]
    exact hV4
  have hquot : Nat.card (↥Γ ⧸ V₀.subgroupOf Γ) = 6 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (V₀.subgroupOf Γ)
    rw [hG0, hVcard] at this
    omega
  have hD8 : Nat.card ↥(centralizer ({s₀} : Set K)) = 8 := card_centralizer_of_d4 hD4 hs₀
  have hz₀ord : orderOf z₀ = 2 := hVord z₀ hz₀ hz₀1
  let π : ↥(centralizer ({s₀} : Set K)) →* ↥Γ ⧸ V₀.subgroupOf Γ :=
    (QuotientGroup.mk' (V₀.subgroupOf Γ)).comp (Subgroup.inclusion hΓs)
  have hker : ∀ d : ↥(centralizer ({s₀} : Set K)), d ∈ π.ker → (d : K) = 1 ∨ (d : K) = z₀ := by
    intro d hd
    have hdV : (d : K) ∈ V₀ :=
      (QuotientGroup.eq_one_iff (N := V₀.subgroupOf Γ) (Subgroup.inclusion hΓs d)).1
        (MonoidHom.mem_ker.1 hd)
    by_contra hcon
    rw [not_or] at hcon
    have hdord : orderOf (d : K) = 2 := hVord _ hdV hcon.1
    have hsd : s₀ * (d : K) = (d : K) * s₀ := (mem_centralizer_singleton_iff.1 d.2).symm
    refine hs₀V ?_
    rcases eq_of_commute_of_d4 hD4 hdord hz₀ord hcon.2 (hVcomm _ hdV _ hz₀) hsd hcomm with
      h | h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hdV
    · rw [h]; exact hz₀
    · rw [h]; exact V₀.mul_mem hz₀ hdV
  have hkerle : π.ker.map (centralizer ({s₀} : Set K)).subtype ≤ zpowers z₀ := by
    rintro x ⟨d, hd, rfl⟩
    rcases hker d hd with h | h
    · rw [Subgroup.subtype_apply, h]; exact one_mem _
    · rw [Subgroup.subtype_apply, h]; exact mem_zpowers z₀
  have hker2 : Nat.card ↥π.ker ≤ 2 := by
    have h1 := Subgroup.card_le_of_le hkerle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers,
      hz₀ord] at h1
  have hrange : Nat.card ↥π.range ∣ 6 :=
    hquot ▸ Subgroup.card_subgroup_dvd_card π.range
  have hmul := Subgroup.card_ker_mul_card_range π
  rw [hD8] at hmul
  have hapos : 0 < Nat.card ↥π.ker := Nat.card_pos
  have hb6 : Nat.card ↥π.range ≤ 6 := Nat.le_of_dvd (by norm_num) hrange
  generalize Nat.card ↥π.ker = a at *
  generalize Nat.card ↥π.range = b at *
  interval_cases a <;> interval_cases b <;> omega

end CentralizerLE

end CFSG.GH74.GLS.IVK.Proofs2

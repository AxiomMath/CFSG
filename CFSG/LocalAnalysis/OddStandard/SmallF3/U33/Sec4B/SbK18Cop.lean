module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem comm_mem_of_sup_centralized {K N Q X : Subgroup G} {ρ : G} (hρK : ρ ∈ K)
    (hQK : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (hNK : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hN : ∀ n ∈ N, ∃ q ∈ Q, ∃ x ∈ X, n = q * x) (hρX : ∀ x ∈ X, ρ * x = x * ρ) :
    ∀ g ∈ ⁅K, zpowers ρ⁆, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ Q := by
  let H : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ n ∈ N, k * n * k⁻¹ * n⁻¹ ∈ Q}
      one_mem' := by
        refine ⟨K.one_mem, fun n _hn => ?_⟩
        simpa using Q.one_mem
      mul_mem' := by
        intro a b ha hb
        obtain ⟨haK, haQ⟩ := ha
        obtain ⟨hbK, hbQ⟩ := hb
        refine ⟨K.mul_mem haK hbK, fun n hn => ?_⟩
        have h1 : a * ⁅b, n⁆ * a⁻¹ ∈ Q := hQK a haK _ (hbQ n hn)
        have h2 : ⁅a, n⁆ ∈ Q := haQ n hn
        have hkey : a * b * n * (a * b)⁻¹ * n⁻¹
            = a * ⁅b, n⁆ * a⁻¹ * ⁅a, n⁆ := by
          simp only [commutatorElement_def]
          group
        rw [hkey]
        exact Q.mul_mem h1 h2
      inv_mem' := by
        intro a ha
        obtain ⟨haK, haQ⟩ := ha
        refine ⟨K.inv_mem haK, fun n hn => ?_⟩
        have hn' : a⁻¹ * n * a ∈ N := by
          simpa using hNK a⁻¹ (K.inv_mem haK) n hn
        have h : a * (a⁻¹ * n * a) * a⁻¹ * (a⁻¹ * n * a)⁻¹ ∈ Q := haQ _ hn'
        have hkey : a⁻¹ * n * (a⁻¹)⁻¹ * n⁻¹
            = (a * (a⁻¹ * n * a) * a⁻¹ * (a⁻¹ * n * a)⁻¹)⁻¹ := by
          group
        rw [hkey]
        exact Q.inv_mem h }
  have hH_sub : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    obtain ⟨hhK, hhQ⟩ := hh
    refine ⟨K.mul_mem (K.mul_mem hk hhK) (K.inv_mem hk), fun n hn => ?_⟩
    have hn' : k⁻¹ * n * k ∈ N := by
      simpa using hNK k⁻¹ (K.inv_mem hk) n hn
    have h' : h * (k⁻¹ * n * k) * h⁻¹ * (k⁻¹ * n * k)⁻¹ ∈ Q := hhQ _ hn'
    have hkey : k * h * k⁻¹ * n * (k * h * k⁻¹)⁻¹ * n⁻¹
        = k * (h * (k⁻¹ * n * k) * h⁻¹ * (k⁻¹ * n * k)⁻¹) * k⁻¹ := by
      group
    rw [hkey]
    exact hQK k hk _ h'
  have hρH : ρ ∈ H := by
    refine ⟨hρK, fun n hn => ?_⟩
    obtain ⟨q, hq, x, hx, rfl⟩ := hN n hn
    have hx1 : ⁅ρ, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hρX x hx)
    have hkey : ⁅ρ, q * x⁆ = ⁅ρ, q⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hx1, mul_one]
      group
    show ⁅ρ, q * x⁆ ∈ Q
    rw [hkey]
    exact Q.mul_mem (hQK ρ hρK q hq) (Q.inv_mem hq)
  have hzH : zpowers ρ ≤ H := Subgroup.zpowers_le.mpr hρH
  have hle : ⁅K, zpowers ρ⁆ ≤ H :=
    Subgroup.commutator_le.mpr fun k hk g' hg' =>
      H.mul_mem (hH_sub k hk g' (hzH hg')) (H.inv_mem (hzH hg'))
  intro g hg n hn
  exact (hle hg).2 n hn

theorem commutator_commutator_zpowers_eq [Finite G] {A : Subgroup G} {ρ : G}
    (hρ3 : ρ ^ 3 = 1) (hA2 : IsPGroup 2 A) (hρA : ρ ∈ normalizer (A : Set G)) :
    ⁅⁅A, zpowers ρ⁆, zpowers ρ⁆ = ⁅A, zpowers ρ⁆ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 (zpowers ρ) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hρ3) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  have hcop : Nat.Coprime 3 (Nat.card A) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hA2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  exact CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three
    (zpowers ρ) A h3 (Subgroup.zpowers_le.mpr hρA) hcop

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

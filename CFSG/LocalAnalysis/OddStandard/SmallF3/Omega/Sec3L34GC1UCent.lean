module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Pk2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

private theorem l34g_uc_mem_normalizer {S : Subgroup A} {p : A}
    (h : CFSG.conjugate S p = S) : p ∈ normalizer (S : Set A) := by
  have h' : p⁻¹ ∈ normalizer (S : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show CFSG.conjugate S p = S
    exact h
  simpa using (Subgroup.inv_mem _ h')

private theorem l34g_uc_mul_conj_mem {S : Subgroup A} {p : A}
    (h : CFSG.conjugate S p = S) {s : A} (hs : s ∈ S) : p * s * p⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp (l34g_uc_mem_normalizer h) s).mp hs

theorem l34g_propU_cent (hC3 : Asc82FactCent3) (hF : L34GFac H 𝒮 x) {C0 : Subgroup A}
    (hodd : ∀ f ∈ H ⊓ centralizer ({x} : Set A), Odd (orderOf f) → f ∈ C0)
    (hswap : ∀ S ∈ 𝒮, CFSG.conjugate S x ≠ S → ∀ d ∈ S, d * (x * d * x⁻¹) ∈ C0)
    {p : A} {m : ℕ} (hp : p ^ 3 ^ m = 1) (hpx : p * x = x * p)
    (hnorm : ∀ S ∈ 𝒮, CFSG.conjugate S p = S) (hpC : ∀ c ∈ C0, p * c = c * p) :
    ∀ S ∈ 𝒮, ∀ s ∈ S, p * s = s * p := by
  intro S hS s hs
  by_cases hxS : CFSG.conjugate S x = S
  ·
    refine l34g_pk2 hC3 (hF.simple S hS) hF.invol hxS hp (hnorm S hS) hpx ?_ s hs
    intro c hc hcodd
    obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
    exact hpC c (hodd c ⟨hF.le S hS hcS, hcC⟩ hcodd)
  ·
    have hδC : s * (x * s * x⁻¹) ∈ C0 := hswap S hS hxS s hs
    have hDcomm : p * (s * (x * s * x⁻¹)) = (s * (x * s * x⁻¹)) * p := hpC _ hδC
    have hq : p * s * p⁻¹ ∈ S := l34g_uc_mul_conj_mem (hnorm S hS) hs
    have hpx' : x * p = p * x := hpx.symm
    have hpxi : p⁻¹ * x⁻¹ = x⁻¹ * p⁻¹ := by
      have h := congrArg Inv.inv hpx
      rw [mul_inv_rev, mul_inv_rev] at h
      exact h.symm
    have hxq : x * (p * s * p⁻¹) * x⁻¹ = p * (x * s * x⁻¹) * p⁻¹ := by
      calc x * (p * s * p⁻¹) * x⁻¹
          = (x * p) * s * (p⁻¹ * x⁻¹) := by group
        _ = (p * x) * s * (p⁻¹ * x⁻¹) := by rw [hpx']
        _ = (p * x) * s * (x⁻¹ * p⁻¹) := by rw [hpxi]
        _ = p * (x * s * x⁻¹) * p⁻¹ := by group
    have hδq : (p * s * p⁻¹) * (x * (p * s * p⁻¹) * x⁻¹)
        = p * (s * (x * s * x⁻¹)) * p⁻¹ := by
      rw [hxq]; group
    have hD : p * (s * (x * s * x⁻¹)) * p⁻¹ = s * (x * s * x⁻¹) := by
      rw [hDcomm]; group
    have heq : (p * s * p⁻¹) * (x * (p * s * p⁻¹) * x⁻¹) = s * (x * s * x⁻¹) := by
      rw [hδq, hD]
    have hps : p * s * p⁻¹ = s := L34GFac.diag_unique hF hS hxS hq hs heq
    calc p * s = p * s * p⁻¹ * p := by group
      _ = s * p := by rw [hps]

end CFSG.OddStandard.SmallF3.Omega

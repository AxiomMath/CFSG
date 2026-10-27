module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1UNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1UCent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

theorem l34g_propU (hC3 : Asc82FactCent3) (hF : L34GFac H 𝒮 x) {C0 : Subgroup A}
    (hodd : ∀ f ∈ H ⊓ centralizer ({x} : Set A), Odd (orderOf f) → f ∈ C0)
    (hfix : ∀ S ∈ 𝒮, CFSG.conjugate S x = S → ∃ c ∈ C0, c ∈ S ∧ c ≠ 1)
    (hswap : ∀ S ∈ 𝒮, CFSG.conjugate S x ≠ S → ∀ d ∈ S, d * (x * d * x⁻¹) ∈ C0)
    {p : A} {m : ℕ} (hp : p ^ 3 ^ m = 1) (hpx : p * x = x * p)
    (hperm : ∀ S ∈ 𝒮, CFSG.conjugate S p ∈ 𝒮) (hpC : ∀ c ∈ C0, p * c = c * p) : p = 1 :=
  hF.eq_one_of_centralizes (l34g_propU_cent hC3 hF hodd hswap hp hpx
    (l34g_propU_norm hF hfix hswap hp hpx hperm hpC) hpC)

end CFSG.OddStandard.SmallF3.Omega

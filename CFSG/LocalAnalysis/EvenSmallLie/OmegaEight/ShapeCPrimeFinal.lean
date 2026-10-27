module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeShape

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrime

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

theorem false_of_sup [Finite G]
    {ε : Eps} {t c a : G} {L N U Q P : Subgroup G} {ψ : V6 → G}
    {p : Fin 6 → G} {v₀ : ℕ} (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (ht : orderOf t = 2) (hc : c * c = t) (hLN : L ≤ N) (hNt : N ≤ centralizer ({t} : Set G))
    (htN : t ∉ N) (hcN : c ∈ normalizer (N : Set G))
    (hH : centralizer ({t} : Set G) = N ⊔ zpowers c) (hodd : ∀ x ∈ N, x * x ∈ L → x ∈ L)
    (hNL : N ≤ normalizer (L : Set G)) (hNQ : ∀ n ∈ N, n ∈ normalizer (Q : Set G) → n ∈ L)
    (hR : RadicalData ε L U Q P a ψ p)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hv₀ : v₀ < 64) (hq₀ : qfB ε v₀ = true)
    (hcact : ∀ v, c * ψ v * c⁻¹ = ψ (toMat 6 6 (reflRows ε v₀) *ᵥ v))
    (hcent : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) ≤ Q ⊔ zpowers t) : False := by
  have hS : ShapeCPrime t L c := ShapeCPrime.of_sup ht hc hLN hNt htN hcN hH hodd
  have hcQ : c ∈ normalizer (Q : Set G) := mem_normalizer_of_conj_mem fun x hx => by
    obtain ⟨v, rfl⟩ := hR.mem_ψ x hx
    rw [hcact]
    exact hR.ψ_mem _
  have hNE := normalizer_E_of_sup ht hc hS.not_mem hS.le_centralizer hH hcN hNL hR.Q_le_L hcQ hNQ
  rw [← hR.P_eq] at hNE
  exact false_of_shapeCPrime hG hnab hS hR ⟨hv₀, hq₀, hcact, hcU,
    sylow_of_sup hcN hH hodd hR.U_le_L hUmax, hcent, hNE⟩

theorem false_of_sup_zpowers [Finite G]
    {ε : Eps} {t c a : G} {L U Q P : Subgroup G} {ψ : V6 → G}
    {p : Fin 6 → G} {v₀ : ℕ} (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (ht : orderOf t = 2) (hc : c * c = t) (htL : t ∉ L) (hLt : L ≤ centralizer ({t} : Set G))
    (hcL : c ∈ normalizer (L : Set G)) (hH : centralizer ({t} : Set G) = L ⊔ zpowers c)
    (hR : RadicalData ε L U Q P a ψ p)
    (hUmax : ∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U)
    (hcU : ∀ u ∈ U, c * u * c⁻¹ ∈ U) (hv₀ : v₀ < 64) (hq₀ : qfB ε v₀ = true)
    (hcact : ∀ v, c * ψ v * c⁻¹ = ψ (toMat 6 6 (reflRows ε v₀) *ᵥ v))
    (hcent : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) ≤ Q ⊔ zpowers t) : False :=
  false_of_sup hG hnab ht hc le_rfl hLt htL hcL hH (fun _ hx _ => hx) le_normalizer
    (fun _ hn _ => hn) hR hUmax hcU hv₀ hq₀ hcact hcent

end CFSG.EvenSmallLie.OmegaEight.CPrime

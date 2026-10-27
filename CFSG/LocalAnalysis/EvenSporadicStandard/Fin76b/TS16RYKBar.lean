module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16Rung

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure S16KBar (G : Type) [Group G] (L : Subgroup G) (z t : G) (E : Subgroup G) (β : G)
    (S : Subgroup G) : Prop where
  S_dih : Nonempty (↥S ≃* DihedralGroup 8)
  sigma_s : ∀ σ v ξ : G, S16LData G L z t β E σ v ξ → ∀ s ∈ S, orderOf s = 8 →
    σ * s * σ⁻¹ = s ^ 3 ∨ σ * s * σ⁻¹ = s ^ 5
  zsigma : ∀ σ v ξ : G, S16LData G L z t β E σ v ξ → ∀ s ∈ S, orderOf s = 8 →
    σ * s * σ⁻¹ = s ^ 5 → ∃ g : G, g * (z * σ) * g⁻¹ = ξ
  K0 : ∃ K0 : Subgroup G, K0 ≤ centralizer ({β} : Set G) ∧
    ∀ k ∈ centralizer ({β} : Set G), k * k = 1 → k ≠ 1 →
      (k ∈ K0 → ∃ g : G, g * t * g⁻¹ = k) ∧ (k ∉ K0 → ∃ g : G, g * z * g⁻¹ = k)

@[expose] def Fin76bS16KBar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), OuterS16Hyp G L z t T E Q x B β →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → Nat.card ↥S = 16 → S16KBar G L z t E β S

end CFSG.EvenSporadicStandard.Fin76b

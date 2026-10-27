module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYDih

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

structure S16LData (G : Type) [Group G] (L : Subgroup G) (z t β : G) (E : Subgroup G)
    (σ v ξ : G) : Prop where
  σ_z : σ * z = z * σ
  σ_sq : σ * σ = 1
  σ_notL : σ ∉ L ⊔ zpowers z
  σ_L : ∀ ℓ ∈ L, σ * ℓ * σ⁻¹ ∈ L
  v_L : v ∈ L
  ξ_L : ξ ∈ L
  v_t : v * t = t * v
  ξ_t : ξ * t = t * ξ
  v4 : v ^ 4 = t
  v8 : v ^ 8 = 1
  ξ_sq : ξ * ξ = 1
  ξ_ne_one : ξ ≠ 1
  ξ_ne_t : ξ ≠ t
  ξ_v : ξ * v * ξ⁻¹ = v⁻¹
  σ_t : σ * t * σ⁻¹ = t
  σ_v : σ * v * σ⁻¹ = v * t
  σ_ξ : σ * ξ * σ⁻¹ = ξ * t
  v_β : v * β * v⁻¹ = β⁻¹
  ξ_β : ξ * β * ξ⁻¹ = β⁻¹
  σ_β : σ * β * σ⁻¹ = β⁻¹
  σ_E : σ ∈ normalizer (E : Set G)
  card_CE : Nat.card ↥(E ⊓ centralizer ({σ} : Set G)) = 8
  CE_eq : closure ({v * v, v * ξ} : Set G) = E ⊓ centralizer ({σ} : Set G)
  card_Y : Nat.card ↥(closure ({v, ξ, σ} : Set G)) = 32
  V0 : ∃ V0 : Subgroup G, V0 ≤ L ⊓ centralizer ({σ} : Set G) ∧ IsPGroup 2 V0 ∧
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ L ⊓ centralizer ({σ} : Set G) → V0 ≤ R → R ≤ V0) ∧
    Nonempty (↥V0 ≃* DihedralGroup 8)
  rank5 : ∃ C : Subgroup G, C ≤ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers σ ∧
    C ≤ centralizer ({ξ} : Set G) ∧ t ∈ C ∧ ξ ∈ C ∧ Nat.card ↥C = 32 ∧
    (∀ c ∈ C, c * c = 1 ∨ c * c = t ∨ c * c = ξ ∨ c * c = t * ξ) ∧
    ∀ c ∈ C, ∀ d ∈ C, c * d * c⁻¹ * d⁻¹ = 1 ∨ c * d * c⁻¹ * d⁻¹ = t ∨ c * d * c⁻¹ * d⁻¹ = ξ ∨
      c * d * c⁻¹ * d⁻¹ = t * ξ

end CFSG.EvenSporadicStandard.Fin76b

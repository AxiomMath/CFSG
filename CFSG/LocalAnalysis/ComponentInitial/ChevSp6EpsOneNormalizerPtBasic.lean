module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagBasic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

structure PtBase (D₂ C₂ E₂ : Subgroup G) (ν₂ : G → ↥(binarySymMatrices 3))
    (σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
      GL (Fin 3) (ZMod 2))
    (D₁ C₁ F₁ : Subgroup G) (ν₁ : G → 𝔼 × ZMod 2) : Prop
    extends LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ where
  hnd : b.Nondegenerate
  hV : finrank (ZMod 2) V = 6
  hsup : L ⊔ zpowers z = centralizer ({z} : Set G)
  hinf : L ⊓ zpowers z = ⊥
  hD₁ : D₁ = CFSG.Assembly.pCoreOf 2 𝒩₁
  hFD₁ : F₁ ≤ D₁
  hD₁N : D₁ ≤ 𝒩₁
  hBF₁ : ℬ₁ ≤ F₁
  hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁
  hF₁n : ∀ n ∈ 𝒩₁, ∀ f ∈ F₁, n * f * n⁻¹ ∈ F₁
  hD₁card : Nat.card D₁ = 2048
  hF₁card : Nat.card F₁ = 128
  hν₁z : ∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1))
  hν₁eq : ∀ d ∈ D₁, ∀ d' ∈ D₁, ν₁ d = ν₁ d' ↔ d⁻¹ * d' ∈ ℬ₁
  hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v
  hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
    d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (v + (b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε))
  hF₁mem : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ (ν₁ d).1 = 0
  hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G), m = d * c
  hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁
  hA₁n : ∀ n ∈ 𝒩₁, ∀ a ∈ 𝒜₁, n * a * n⁻¹ ∈ 𝒜₁
  hb₁c : ∀ n ∈ 𝒩₁, n * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * n
  hZF₁ : (center F₁).map F₁.subtype = 𝒜₁
  hZD₁ : (center D₁).map D₁.subtype = zpowers (ptB₁ he hb φ hzC hz)
  hAD₁ : ⁅𝒜₁, D₁⁆ = zpowers (ptB₁ he hb φ hzC hz)
  hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁
  hγF₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) ↔ d ∈ F₁
  hγeq : ∀ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G), ∀ d : G,
    z⁻¹ * ((c⁻¹ * d * c)⁻¹ * z * (c⁻¹ * d * c)) = c⁻¹ * (z⁻¹ * (d⁻¹ * z * d)) * c
  hC₁D : C₁ ≤ D₁
  hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁
  hC₁card : Nat.card C₁ = 1024
  hC₁z : zpowers z ⊔ C₁ = D₁
  hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁
  hC₁sq : closure {x | ∃ y ∈ C₁, y ^ 2 = x} = zpowers (ptB₁ he hb φ hzC hz)
  hC₁comm : ⁅C₁, C₁⁆ = zpowers (ptB₁ he hb φ hzC hz)
  hZ₁card : Nat.card (center C₁) = 4
  hZ₁A : (center C₁).map C₁.subtype ⊓ 𝒜₁ = zpowers (ptB₁ he hb φ hzC hz)
  hE₁ : (C₁ ⊓ F₁ : Subgroup G) = 𝒜₁ ⊔ (center C₁).map C₁.subtype
  hZ₁C₂ : (center C₁).map C₁.subtype ≤ C₂
  hK₀ : ((C₁ ⊓ D₂ : Subgroup G) : Set G) =
    ((C₁ ⊓ E₂ : Subgroup G) : Set G) * ((center C₁).map C₁.subtype : Set G)
  hZ₁iso : Nonempty (↥(center C₁) ≃* Multiplicative (ZMod 4))
  hZ₁sq : closure {x | ∃ y ∈ (center C₁).map C₁.subtype, y ^ 2 = x} =
    zpowers (ptB₁ he hb φ hzC hz)
  hE₁card : Nat.card (C₁ ⊓ F₁ : Subgroup G) = 64
  hK₀card : Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64
  hMcard : Nat.card (C₁ ⊓ E₂ : Subgroup G) = 32
  hK₀comm : ∀ k ∈ C₁ ⊓ D₂, ∀ k' ∈ C₁ ⊓ D₂, k * k' = k' * k
  hK₀z : conjClass (C₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G)
  hK₀A : ⁅C₁ ⊓ D₂, 𝒜₂⁆ = ⊥
  hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂
  hPcomm : ∀ x ∈ 𝒜₂ ⊔ (C₁ ⊓ D₂), ∀ y ∈ 𝒜₂ ⊔ (C₁ ⊓ D₂), x * y = y * x
  hPcard : Nat.card (𝒜₂ ⊔ (C₁ ⊓ D₂) : Subgroup G) = 512
  hN₁₂ : Nat.card (𝒩₁ ⊓ 𝒩₂ : Subgroup G) = 24576
  hO₁₂ : Nat.card (CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂)) = 4096
  hD₁₂ : Nat.card (D₁ ⊓ D₂ : Subgroup G) = 128

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

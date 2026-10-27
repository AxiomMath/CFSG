module

public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.LU.Local.SL2Aut2
public import CFSG.GH74.GLS.SP.Local.SPLOrdBr
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped commutatorElement

structure PumpXSetting (G : Type) [Group G] [Finite G] (q : ℕ) (z t : G) (I F₀ : Subgroup G) :
    Prop where
  odd_q : Odd q
  q_ge : 5 ≤ q
  gen4 : Gen4 G
  comp : ∀ L : Subgroup (CentralizerBar t), IsComponent L → InC2 ↥L ∨ InT2 ↥L
  z_ord : orderOf z = 2
  t_ord : orderOf t = 2
  zt_comm : z * t = t * z
  z_ne_t : z ≠ t
  cen : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) = (zpowers z ⊔ zpowers t) ⊔ (I ⊔ F₀)
  I_L2 : IVK.IsL2 ↥I (fun r => r = q)
  I_perf : ⁅I, I⁆ = I
  F₀_norm : ∀ f ∈ F₀, ∀ i ∈ I, f * i * f⁻¹ ∈ I
  F₀_inf : F₀ ⊓ I = ⊥
  F₀_faith : ∀ f ∈ F₀, (∀ i ∈ I, f * i = i * f) → f = 1
  F₀_odd : Odd (Nat.card ↥F₀)
  O2 : ∀ N : Subgroup G, N ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) →
    (∀ g ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
    Odd (Nat.card ↥N) → N = ⊥
  T₁ex : ∃ T₁ : Subgroup G, T₁ ≤ I ∧ IsPGroup 2 T₁ ∧
    (∀ P : Subgroup G, P ≤ I → IsPGroup 2 P → T₁ ≤ P → P = T₁) ∧
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) →
      Nat.card ↥P ≤ 2 * Nat.card ↥T₁ ^ 2

@[expose] def SPLPumpX : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (q : ℕ) (z t : G) (I F₀ : Subgroup G),
    PumpXSetting G q z t I F₀ →
      pLayerOf 2 (centralizer ({t} : Set G)) ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊔ I

end CFSG.GH74.GLS.SP.Local

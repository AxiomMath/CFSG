module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndSection4
public import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSetting
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParAbs2

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open scoped MatrixGroups
open Matrix

structure N2Out {G : Type} [Group G] (F : Type) [Field F] (d : YamadaData G) : Prop where
  D₂_le : d.D₂ ≤ d.N₂
  N₂_norm : d.N₂ ≤ normalizer (d.D₂ : Set G)
  N₂_H : d.N₂ ⊓ d.H = d.K₂ ⊔ d.A₂
  t_N₂ : d.t ∈ normalizer (d.N₂ : Set G)
  normalizer_S : normalizer (d.S : Set G) ⊓ d.H ≤
    normalizer (d.N₁ : Set G) ⊓ normalizer (d.N₂ : Set G)
  centralizer₂ : ∀ x ∈ d.N₂, x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂ → x ∈ d.K₂ ⊔ d.D₂
  type₂ : ∃ M : Subgroup G, d.D₂ ≤ M ∧ M ≤ d.N₂ ∧ d.N₂ = M ⊔ conjR M d.t ∧
    ⁅M, conjR M d.t⁆ ≤ d.D₂ ∧ d.D₂.relIndex (M ⊓ conjR M d.t) ∣ 3 ∧
    ∃ _ : (d.D₂.subgroupOf M).Normal, ∃ ψ : SL(3, F) →* M ⧸ d.D₂.subgroupOf M,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(3, F)
  P_le₂ : d.P ≤ d.N₂
  sylow_P₂ : IsSylowOf 2 d.P d.N₂
  card_P_w₁ : Nat.card (d.P ⊓ conjR d.P d.w₁ : Subgroup G) = 2 ^ 26
  N₂_gen : d.N₂ = d.P ⊔ zpowers d.w₁ ⊔ zpowers d.w₂

section Coords


structure Y13Coords {G : Type} [Group G] (d : YamadaD.Data G) (θ : d.K₁ ≃* YamadaPar.SU42b)
    (ιG : (Fin 8 → ZMod 2) → G) : Prop where
  ι_mem : ∀ u, ιG u ∈ d.A₁
  ι_add : ∀ u v, (ιG u * ιG v)⁻¹ * ιG (u + v) ∈ zpowers d.z
  ι_inj : ∀ u, ιG u ∈ zpowers d.z → u = 0
  K₁_ι : ∀ k : d.K₁, ∀ u, ((k : G) * ιG u * (k : G)⁻¹)⁻¹ *
    ιG (((θ k : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ u) ∈ zpowers d.z
  E_mem : ∀ m < 4, ((θ.symm (YamadaPar.eSU m) : d.K₁) : G) ∈ d.A₂
  ν_mem : ∀ j < 2, ((θ.symm (YamadaPar.nuSU j) : d.K₁) : G) ∈ d.K₂ ⊔ d.A₂

end Coords

end CFSG.EvenSmallLie.UnitarySix.Child5

module

public import CFSG.GH74.GLS.C3.Layer1.St1Leaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Config8

variable {G : Type} [Group G]

@[expose] def centerIn (S : Subgroup G) : Subgroup G := S ⊓ centralizer (S : Set G)

@[expose] def NoL29Component (u : G) : Prop :=
  ∀ Kh : Subgroup (CentralizerBar u), CFSG.IsComponent Kh → ¬ HasL2Model ↥Kh (fun q => q = 9)

structure Config8 [Finite G] (x : G) (S U : Subgroup G) (u : G) (K W : Subgroup G) : Prop where
  ord_x : orderOf x = 2
  oddCore : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥
  sylow_S : IsSylowOf 2 S ⊤
  sylow_T : IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G))
  four : IVK.IsFourSubgroup U
  U_le : U ≤ S
  U_normal : ∀ s ∈ S, ∀ w ∈ U, s * w * s⁻¹ ∈ U
  U_central : ¬ IsCyclic ↥(centerIn S) → U ≤ centerIn S
  U_noL29 : IsCyclic ↥(centerIn S) →
    (∃ U' : Subgroup G, IVK.IsFourSubgroup U' ∧ U' ≤ S ∧ (∀ s ∈ S, ∀ w ∈ U', s * w * s⁻¹ ∈ U') ∧
      ∃ u' ∈ U', u' ∉ centerIn S ∧ NoL29Component u') →
    ∃ u' ∈ U, u' ∉ centerIn S ∧ NoL29Component u'
  x_mem : x ∈ S ∧ ∀ w ∈ U, x * w = w * x
  u_mem : u ∈ U ∧ u ≠ 1
  unbal : IsUnbalancingTriple u x K
  u_central : (∃ (u' : G) (K' : Subgroup G), u' ∈ U ∧ u' ≠ 1 ∧ u' ∈ centerIn S ∧
      IsUnbalancingTriple u' x K') → u ∈ centerIn S
  sylow_W : IsSylowOf 2 W (NxK u K)
  x_mem_W : x ∈ W

end Config8

@[expose] def B_st1_prop81 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm5 G →
    (∃ x₀ : G, orderOf x₀ = 2 ∧ pPrimeCore 2 ↥(centralizer ({x₀} : Set G)) ≠ ⊥) →
      ∃ (x : G) (S U : Subgroup G) (u : G) (K W : Subgroup G), Config8 x S U u K W

@[expose] def B_st1_prop83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Prop51 G → St1Thm5 G → ∀ (x : G) (S U : Subgroup G) (u : G) (K W : Subgroup G),
      Config8 x S U u K W →
        HasL2Model (kBar K) (fun q => q = 9) ∧ pRank 2 ↥(W ⊓ CxK u K) = 1

@[expose] def B_st1_prop89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    St1Prop51 G → St1Thm5 G → ∀ (x : G) (S U : Subgroup G) (u : G) (K W : Subgroup G),
      Config8 x S U u K W → HasL2Model (kBar K) (fun q => q = 9) →
        pRank 2 ↥(W ⊓ CxK u K) = 1 → False

theorem thm6_of_leaves (h81 : B_st1_prop81) (h83 : B_st1_prop83) (h89 : B_st1_prop89)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) (hN : NoU2Triple G) (T7 : St1Thm7 G)
    (P41 : St1Prop41 G) (P51 : St1Prop51 G) (T5 : St1Thm5 G) : St1Thm6 G := by
  intro x hx
  by_contra hne
  obtain ⟨x', S, U, u, K, W, hc⟩ := h81 G hG hN T5 ⟨x, hx, hne⟩
  obtain ⟨h1, h2⟩ := h83 G hG hN T7 P41 P51 T5 x' S U u K W hc
  exact h89 G hG hN T7 P41 P51 T5 x' S U u K W hc h1 h2

theorem b_st1_thm6_of_leaves (h81 : B_st1_prop81) (h83 : B_st1_prop83) (h89 : B_st1_prop89) :
    B_st1_thm6 :=
  fun _ _ _ hG hN T7 P41 P51 T5 => thm6_of_leaves h81 h83 h89 hG hN T7 P41 P51 T5

end CFSG.GH74.GLS

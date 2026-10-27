module

public import CFSG.ClassicalInvolution.Q3.Sec13EndHyp

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure CaseBSit (Ω : Set (Subgroup G)) (K : Subgroup G) (P₁ P₂ : Set (Subgroup G)) (g : G) :
    Prop where
  hyp : EndHyp Ω
  hK : K ∈ P₁
  dcomp : dComp Ω K = P₁ ∪ P₂
  disj : Disjoint P₁ P₂
  comm : ∀ L ∈ P₁, ∀ L' ∈ P₂, ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  gP : conjSub g K ∈ P₂
  swap : ∀ L : Subgroup G, L ∈ P₂ ↔ conjSub g⁻¹ L ∈ P₁
  inv : ∀ L ∈ P₁, ∀ x ∈ pSpan P₁, conjSub x L ∈ P₁
  trans : ∀ L ∈ P₁, ∀ L' ∈ P₁, ∃ x ∈ pSpan P₁, conjSub x L = L'
  odd : classicalInvolutionOddCore ↥(pSpan P₁) = ⊥
  wyl : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W

structure CaseBU (Ω : Set (Subgroup G)) (K : Subgroup G) (P₁ P₂ : Set (Subgroup G)) (g u h e : G)
    (T : Subgroup G) : Prop extends CaseBSit Ω K P₁ P₂ g where
  u_ne : u ≠ 1
  z_eq : ∀ z : G, IsUniqueInvolution K z → z = u * (e⁻¹ * h⁻¹ * e * h)
  P₁_u : ∀ L ∈ P₁, ¬ L ≤ Subgroup.centralizer ({u} : Set G)
  P₂_u : ∀ L ∈ P₂, L ≤ Subgroup.centralizer ({u} : Set G)
  h_three : orderOf h = 3
  h_u : h * u = u * h
  h_P₂ : ∀ L ∈ P₂, ∀ y ∈ L, h * y = y * h
  h_mem : h ∈ pSpan P₁
  e_u : e * u = u * e
  T_mem : T ∈ Generic.centMembers Ω u
  T_not : T ∉ P₁ ∪ P₂


end CFSG.ClassicalInvolution.Q3.Sec13

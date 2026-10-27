module

public import CFSG.GH74.GLS.C3.Statements
public import CFSG.GH74.GLS.C3.Layer1.P34Stmt

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Vocab

variable {G : Type} [Group G]

@[expose] def NoV2 (G : Type) [Group G] : Prop :=
  ¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K

structure Setup1D (x : G) (K T : Subgroup G) : Prop where
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  sylowT0 : IsSylowOf 2 (T ⊓ NxK x K) (NxK x K)

@[expose] def IsFMember (x : G) (K T : Subgroup G) (f : G) : Prop :=
  f ∈ T ∧ orderOf f = 2 ∧ (∀ p ∈ T ⊓ K, f * p = p * f) ∧ f ≠ x ∧
    pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥

@[expose] def IsFU2 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  Is2TerminalU2Triple x y K ∧ ∃ T : Subgroup G, Setup1D x K T ∧ IsFMember x K T f

@[expose] def FMax1 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  IsFU2 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), IsFU2 x' y' K' f' →
    Nat.card (kBar K') ≤ Nat.card (kBar K)

@[expose] def FMax2 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  FMax1 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), FMax1 x' y' K' f' →
    twoPartCard (centralizer ({x'} : Set G)) ≤ twoPartCard (centralizer ({x} : Set G))

@[expose] def FMax3 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  FMax2 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), FMax2 x' y' K' f' →
    twoPartCard (centralizer ({f'} : Set G)) ≤ twoPartCard (centralizer ({f} : Set G))

end Vocab

@[expose] def B_thm1_P31s : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K) ∧
      (∃ Q : Subgroup G, IsSylowOf 2 Q (CMK (centralizer ({x} : Set G)) K) ∧
        (IsCyclic ↥Q ∨ C3.Layer1.P34.IsMaximalClassTwoGroup ↥Q)) ∧
      ∀ T : Subgroup G, Setup1D x K T →
        (∃ f : G, IsFMember x K T f ∧ C3.Layer1.P34.InducesFAutL2A7 f K) ∧
        (∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n) ∧
        ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
          ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z

@[expose] def Thm1P31a : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      ¬ CFSG.GH74.IsCentralInvolution x ∧
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      ∀ T : Subgroup G, Setup1D x K T →
        (∃ n : ℕ, 3 ≤ n ∧ IVK.IsDihedralTwoGroup ↥(T ⊓ K) n) ∧
        ∃ z ∈ T ⊓ K, orderOf z = 2 ∧ (∀ p ∈ T ⊓ K, z * p = p * z) ∧
          ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z

@[expose] def B_thm1_L39 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    (∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K) →
    ∃ (x y : G) (K T : Subgroup G) (f : G), FMax3 x y K f ∧ Setup1D x K T ∧ IsFMember x K T f ∧
      ∀ V : Subgroup G, IsSylowOf 2 V (centralizer ({f} : Set G)) → (∀ t ∈ T, f * t = t * f → t ∈ V) →
        IsSylowOf 2 V ⊤

@[expose] def B_thm1_L310 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K : Subgroup G) (f : G), FMax3 x y K f →
      ∀ T V : Subgroup G, Setup1D x K T → IsFMember x K T f →
        IsSylowOf 2 V (centralizer ({f} : Set G)) → (∀ t ∈ T, f * t = t * f → t ∈ V) → IsSylowOf 2 V ⊤ →
          (∀ v ∈ V, ∀ p ∈ T ⊓ K, v * p * v⁻¹ ∈ T ⊓ K) ∧
          ∃ V₀ : Subgroup G, V₀ ≤ V ∧ (∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) ∧ x ∉ V₀ ∧
            (∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) ∧ T ⊓ K ⊔ zpowers f ≤ V₀ ∧
            ∀ u ∈ V₀, u * u = 1 → u ∈ T ⊓ K ⊔ zpowers f

@[expose] def B_thm1_fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2 G →
    ∀ (x y : G) (K T : Subgroup G) (f : G), Is2TerminalU2Triple x y K → Setup1D x K T → IsFMember x K T f →
      ∀ z ∈ T ⊓ K, orderOf z = 2 → (∀ p ∈ T ⊓ K, z * p = p * z) →
        ∀ u ∈ T ⊓ K ⊔ zpowers f, orderOf u = 2 →
          ∃ g : G, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z

end CFSG.GH74.GLS

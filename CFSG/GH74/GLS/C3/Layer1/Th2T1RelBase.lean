module

public import CFSG.GH74.GLS.C3.Layer1.Thm1Lemmas
public import CFSG.GH74.GLS.C3.Layer1.Th2T1Rel

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1

@[expose] def B_thm1_P31_unique_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      ∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K

@[expose] def B_thm1_P31_comp_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) ∧
      (∀ K' : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G)) K' → K' = K)

@[expose] def B_thm1_P31_layer_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K →
      (HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      (∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      ∀ T : Subgroup G, Setup1D x K T → ∀ f z : G, f ∈ T → orderOf f = 2 →
        (∀ p ∈ T ⊓ K, f * p = p * f) → P34.InducesFAutL2A7 f K →
        z ∈ T ⊓ K → orderOf z = 2 → (∀ p ∈ T ⊓ K, z * p = p * z) →
        ¬ HasL2Model (kBar K) (fun q => q = 5) →
        pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥ ∨
          (Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
            pLayerOf 2 (K ⊓ centralizer ({f * z} : Set G)) ≠ ⊥)

@[expose] def B_thm1_L33c'_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Hyp33 x y K T V W f z →
      8 ≤ Nat.card ↥(secD K f V) → V ≠ W →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
        IsConj z f ∧
        ∀ b : G, b ∈ W → b ∈ normalizer (V : Set G) → b ∉ V → b ^ 2 ∈ V →
          zpowers (z * f) = zCenter (V ⊔ zpowers b) ∧
          secD K f V ⊓ (secD K f V).map (MulAut.conj b).toMonoidHom = ⊥ ∧
          ∀ d ∈ secD K f V, ∀ e ∈ (secD K f V).map (MulAut.conj b).toMonoidHom, d * e = e * d

@[expose] def B_thm1_L33d_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Hyp33 x y K T V W f z →
      Nat.card ↥(secD K f V) = 4 →
      (V ≠ W ∨ ∃ g ∈ normalizer (V : Set G), (secD K f V).map (MulAut.conj g).toMonoidHom ≠ secD K f V) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
        x ∈ zCenter V ∧ omega1 V = (T ⊓ K) ⊔ secD K f V ∧ (T ⊓ K) ⊓ secD K f V = ⊥ ∧
          ∀ p ∈ T ⊓ K, ∀ d ∈ secD K f V, p * d = d * p

@[expose] def B_thm1_L33e_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Hyp33 x y K T V W f z →
      ¬ IsConj z f → ¬ HasL2Model (kBar K) (fun q => q = 5) →
      ∀ v ∈ V, ∀ p ∈ T ⊓ K, v * p * v⁻¹ ∈ T ⊓ K

@[expose] def B_thm1_L33f_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Hyp33 x y K T V W f z →
      IsConj z f → ¬ HasL2Model (kBar K) (fun q => q = 5) →
      V ≠ W ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7))

@[expose] def B_thm1_L34a_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T : Subgroup G) (f : G), FMax3 x y K f → Setup1D x K T → IsFMember x K T f →
      layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
        ∃ w : G, orderOf w = 2 ∧ Is2TerminalU2Triple f w (pumpJ K f)

@[expose] def B_thm1_L34_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T : Subgroup G) (f : G), FMax3 x y K f → Setup1D x K T → IsFMember x K T f →
      layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
        (∃ w : G, orderOf w = 2 ∧ Is2TerminalU2Triple f w (pumpJ K f)) ∧
          IsSylowOf 2 (zpowers f) (CxK f (pumpJ K f))

@[expose] def B_thm1_L35_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z →
      Nonempty (kBar K ≃* alternatingGroup (Fin 7)) → ¬ HasL2Model (kBar K) (fun q => q = 5) → V = W

@[expose] def B_thm1_L36_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z →
      ¬ HasL2Model (kBar K) (fun q => q = 5) → V = W ∨ Nat.card ↥V ≤ Nat.card ↥T

@[expose] def B_thm1_L36A7_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z →
      layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) < pumpJ K f →
      Nonempty (kBar (pumpJ K f) ≃* alternatingGroup (Fin 7)) →
      HasL2Model (kBar K) (fun q => q = 5 ^ 2) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) → Nat.card ↥V ≤ Nat.card ↥T

@[expose] def B_thm1_L39core_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V W : Subgroup G) (f z : G), Cfg3 x y K T V W f z → IsSpecial x y K T f → V ≠ W →
      ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) → Nat.card ↥V ≤ Nat.card ↥T →
      ¬ HasL2Model (kBar K) (fun q => q = 5) → False

@[expose] def B_thm1_L310_V0_rel : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoV2Fine G →
    ∀ (x y : G) (K T V : Subgroup G) (f z : G), Cfg3 x y K T V V f z →
      pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f) → (∀ v ∈ V, ∀ p ∈ T ⊓ K, v * p * v⁻¹ ∈ T ⊓ K) →
      ¬ HasL2Model (kBar K) (fun q => q = 5) →
        ∃ V₀ : Subgroup G, V₀ ≤ V ∧ (∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) ∧ x ∉ V₀ ∧
          (∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) ∧ T ⊓ K ⊔ zpowers f ≤ V₀ ∧
          ∀ u ∈ V₀, u * u = 1 → u ∈ T ⊓ K ⊔ zpowers f

end CFSG.GH74.GLS

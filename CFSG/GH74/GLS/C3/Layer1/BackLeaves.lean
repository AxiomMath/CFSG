module

public import CFSG.GH74.GLS.C3.Layer1.BackStmt

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Defs

variable {G : Type} [Group G]

@[expose] def gammaIn (L V : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ V) (_ : 1 ≤ pRank 2 ↥E), normalizer (E : Set G) ⊓ L

end Defs

@[expose] def B_iv2_8_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (M L Q : Subgroup G),
    IsCoatom M → IsPCompIn 2 M L → (∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) →
    IsSylowOf 2 Q (CMK M L) → gammaK 2 Q 1 ≤ M →
    ∀ g : G, CFSG.conjugate Q g ⊓ M ≠ ⊥ → L ≤ CFSG.conjugate M g → g ∈ M

@[expose] def B_lemma92 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M V : Subgroup G),
    L ≤ M → (∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) →
    (HasL2Model (kBar L) Odd ∨ Nonempty (kBar L ≃* alternatingGroup (Fin 7))) →
    IsPGroup 2 ↥V → V ≤ M → 2 ≤ CFSG.pRank 2 ↥V → gammaIn L V ≠ L →
      (HasL2Model (kBar L) Odd →
        ∃ q ∈ ({5, 7, 9} : Finset ℕ), HasL2Model (kBar L) (fun r => r = q)) ∧
      (CFSG.IsElementaryAbelian 2 ↥V ∧ Nat.card ↥V = 4) ∧
      V ≤ L ⊔ CMK M L ∧ V ⊓ CMK M L = ⊥

@[expose] def B_ivk_10_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsLocallyUnbalancing x y K → InU2 (kBar K)

@[expose] def B_ivk_10_2a : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K : Subgroup G),
    IsV2Triple x y K → HasL2Model (kBar K) IsFM9 →
      y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def B_prop91_PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K L M T Q : Subgroup G) (g : G),
    Hyp9A x K L M T Q → IsV2Triple x y K →
    y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K) →
    HasL2Model (kBar K) (fun r => r = 7 ∨ r = 9) → g ∉ M → CFSG.conjugate Q g ≤ M →
    ¬ L ≤ CFSG.conjugate M g →
    (CFSG.IsElementaryAbelian 2 ↥(CFSG.conjugate Q g) ∧ Nat.card ↥(CFSG.conjugate Q g) = 4) →
    CFSG.conjugate Q g ≤ (T ⊓ K) ⊔ Q → CFSG.conjugate Q g ⊓ Q = ⊥ → False

@[expose] def B_lemma113a : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → ¬ HasL2Model (kBar K) (fun r => r = 7) →
      ¬ IsSylowOf 2 T ⊤

@[expose] def B_lemma113_L27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → ¬ HasL2Model (kBar K) (fun r => r = 7)

@[expose] def B_lemma113_d6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → K = L →
      Nonempty (kBar K ≃* alternatingGroup (Fin 6)) →
        ∃ ψ : ↥M →* Equiv.Perm (Fin 6), ψ.ker = (CMK M K).subgroupOf M

@[expose] def B_lemma114_nonEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ¬ IsEvenType G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → Lemma113Concl x K L M T Q →
      pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥

@[expose] def B_gen4_noL34_elem : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (x : G) (K : Subgroup G), orderOf x = 2 →
    IsPCompIn 2 (centralizer ({x} : Set G)) K →
      ¬ (IsL34Quotient (kBar K) ∧ CFSG.IsElementaryAbelian 2 ↥(center (kBar K)) ∧
        Nat.card ↥(center (kBar K)) ≤ 4)

end CFSG.GH74.GLS

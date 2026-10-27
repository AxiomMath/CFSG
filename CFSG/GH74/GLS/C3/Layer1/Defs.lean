module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Defs

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage1.Thm3.Sec7 (IsHalfTwoCentral)

section Notation

variable {G : Type} [Group G]

abbrev kBar (K : Subgroup G) : Type := ↥K ⧸ pPrimeCore 2 ↥K

@[expose] def CMK (M K : Subgroup G) : Subgroup G :=
  M ⊓ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] noncomputable def twoPartCard (H : Subgroup G) : ℕ :=
  2 ^ (Nat.card ↥H).factorization 2

@[expose] def IsStar2 (x : G) : Prop :=
  orderOf x = 2 ∧ pRank 2 ↥(centralizer ({x} : Set G)) = pRank 2 G

end Notation

section Unbalancing

variable {G : Type} [Group G]

@[expose] def IsLocallyUnbalancing (x y : G) (K : Subgroup G) : Prop :=
  IsIL2Pair x K ∧ orderOf y = 2 ∧ y ∈ centralizer ({x} : Set G) ∧ y ∈ normalizer (K : Set G) ∧
    ¬ pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) ≤ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def IsUnbalancingTriple (x y : G) (K : Subgroup G) : Prop :=
  IsIL2Pair x K ∧ orderOf y = 2 ∧ y ∈ centralizer ({x} : Set G) ∧ y ∈ normalizer (K : Set G) ∧
    ¬ pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ centralizer ({x} : Set G) ≤
      centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def Is2TerminalU2Triple (x y : G) (K : Subgroup G) : Prop :=
  IsLocallyUnbalancing x y K ∧ IsTwoTerminal x K ∧ IsStar2 x ∧
    (IsL34Quotient (kBar K) → IsHalfTwoCentral x) ∧
    (HasL2Model (kBar K) (fun q => q = 9) →
      2 ≤ pRank 2 ↥(CxK x K) ∧ (IsHalfTwoCentral x ∨ pRank 2 G = 2 + pRank 2 ↥(CxK x K)))

end Unbalancing

section V2

variable {G : Type} [Group G]

@[expose] def IsExceptionalA7Triple (x y : G) (K : Subgroup G) : Prop :=
  Is2TerminalU2Triple x y K ∧ Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧
    ∃ (T S : Subgroup G) (a : G),
      IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ IsSylowOf 2 (T ⊓ NxK x K) (NxK x K) ∧
      IsSylowOf 2 (T ⊓ CxK x K) (CxK x K) ∧
      IsSylowOf 2 S ⊤ ∧ T < S ∧ a ∈ S ∧ a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T ∧
      S = T ⊔ zpowers a ∧
      (T ⊓ K) ⊓ (T ⊓ K).map (MulAut.conj a).toMonoidHom = ⊥ ∧
      (∀ p ∈ T ⊓ K, ∀ q ∈ (T ⊓ K).map (MulAut.conj a).toMonoidHom, p * q = q * p) ∧
      T = (T ⊓ K) ⊔ (T ⊓ K).map (MulAut.conj a).toMonoidHom ∧
      Nonempty (↥(T ⊓ K) ≃* DihedralGroup 4) ∧
      Nonempty (↥(T ⊓ CxK x K) ≃* Multiplicative (ZMod 4))

@[expose] def IsV2Triple (x y : G) (K : Subgroup G) : Prop :=
  IsLocallyUnbalancing x y K ∧ IsTwoTerminal x K ∧
    (2 ≤ pRank 2 ↥(CxK x K) ∨ IsExceptionalA7Triple x y K) ∧
    (IsL34Quotient (kBar K) → Is2TerminalU2Triple x y K)

@[expose] def U2Succ (H J : Type) [Group H] [Group J] : Prop :=
  InU2 H ∧ InU2 J ∧
    ((Nonempty (H ≃* alternatingGroup (Fin 7)) ∧ ¬ Nonempty (J ≃* alternatingGroup (Fin 7))) ∨
      (¬ InC2 H ∧ InC2 J) ∨
      (((InC2 H ∧ InC2 J) ∨
          ((¬ InC2 H ∧ ¬ Nonempty (H ≃* alternatingGroup (Fin 7))) ∧
            (¬ InC2 J ∧ ¬ Nonempty (J ≃* alternatingGroup (Fin 7))))) ∧
        Nat.card J < Nat.card H))

@[expose] def V2Max1 (x y : G) (K : Subgroup G) : Prop :=
  IsV2Triple x y K ∧ ∀ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' →
    ¬ U2Succ (kBar K') (kBar K)

@[expose] def V2Max2 (x y : G) (K : Subgroup G) : Prop :=
  V2Max1 x y K ∧ ∀ (x' y' : G) (K' : Subgroup G), V2Max1 x' y' K' →
    pRank 2 ↥(CxK x' K') ≤ pRank 2 ↥(CxK x K)

@[expose] def V2Max3 (x y : G) (K : Subgroup G) : Prop :=
  V2Max2 x y K ∧ ∀ (x' y' : G) (K' : Subgroup G), V2Max2 x' y' K' →
    twoPartCard (CxK x' K') ≤ twoPartCard (CxK x K)

@[expose] def IsV2StarTriple (x y : G) (K : Subgroup G) : Prop :=
  V2Max3 x y K ∧ ∀ (x' y' : G) (K' : Subgroup G), V2Max3 x' y' K' →
    twoPartCard (NxK x' K') ≤ twoPartCard (NxK x K)

end V2

section Hyp9

variable {G : Type} [Group G]

structure Hyp9A (x : G) (K L M T Q : Subgroup G) : Prop where
  twoTerminal : IsTwoTerminal x K
  maximal : IsCoatom M
  K_le_L : K ≤ L
  L_normal : L ≤ M ∧ ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L
  L_comp : IsPCompIn 2 M L
  bar_eq : K ⊔ pPrimeCoreOf 2 M = L ⊔ pPrimeCoreOf 2 M
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hQ : Q = T ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (CMK M L)
  rankQ : 2 ≤ pRank 2 ↥Q
  gamma : gammaK 2 Q 1 ≤ M
  sylowTM : IsSylowOf 2 T M
  cent5 : ∀ u ∈ Q, (∀ t ∈ T, u * t = t * u) → orderOf u = 2 → IsSylowOf 2 T (centralizer ({u} : Set G))
  terminal_eq : IsTerminalPair 2 x K → K = L

structure Hyp9B1 (x : G) (K T Q : Subgroup G) : Prop where
  v2star : ∃ y : G, IsV2StarTriple x y K
  nonTerminal : ¬ IsTerminalPair 2 x K → Nat.card ↥Q = 4 →
    (Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) →
      IsSylowOf 2 T ⊤

structure Hyp9B2 (x : G) (K M T Q : Subgroup G) : Prop where
  evenType : IsEvenType G
  notRestricted : ¬ IsRestrictedEvenType G
  noV2 : ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K'
  isL2 : HasL2Model ↥K IsFM9
  M_eq : M = normalizer (K : Set G)
  five : Nonempty (↥K ≃* alternatingGroup (Fin 5)) → T = (T ⊓ K) ⊔ Q → IsSylowOf 2 T ⊤
  terminal : IsTerminalPair 2 x K

structure Hyp9 (x : G) (K L M T Q : Subgroup G) : Prop where
  a : Hyp9A x K L M T Q
  b : Hyp9B1 x K T Q ∨ Hyp9B2 x K M T Q

end Hyp9

end CFSG.GH74.GLS

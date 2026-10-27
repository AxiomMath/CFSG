module

public import CFSG.GH74.Generic.BProg.B3.S3Boot292
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure H29 (G : Type) [Group G] [Finite G] (x : G) (K A B Q : Subgroup G) (y : G) : Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  circ : IsJ2Circ x K
  shape : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)
  src : IsSource2 x K A
  ext : IsExtSource2 x K A B
  rankB : pRank 2 ↥B = 4
  C_rank : pRank 2 ↥(CxK x K) = 2
  B0_le_C : B ⊓ cSec K ≤ CxK x K
  Q_syl : IsSylowOf 2 Q (CxK x K)
  Q_cent : Q ≤ centralizer (A : Set G)
  B0_le_Q : B ⊓ cSec K ≤ Q
  y_mem : y ∈ A ⊓ K
  y_ord : orderOf y = 2
  notG : ¬ (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)

@[expose] def ImageF0F1 (B J : Subgroup G) (e : kBar J ≃* alternatingGroup (Fin 7))
    (F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))) : Prop :=
  GLS.Th2.Obs.IsRootFour F₀ ∧
    (F₁ = ⊥ ∨ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧ F₁ = zpowers t ∧
      ∀ i, (∃ f ∈ F₀, f i ≠ i) → t i = i) ∧
    (B.subgroupOf (normalizer (J : Set G))).map (GLS.Th2.Obs.a7Act J e) = F₀ ⊔ F₁

@[expose] def Exists29H (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a : G) (K A D J : Subgroup G), Ctx21 G x K A a D J →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → 1 < pRank 2 ↥(CxK x K) →
    (∀ B : Subgroup G, IsExtSource2 x K A B → pRank 2 ↥B = 4 →
      ¬ (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)) →
    ∃ (y : G) (B Q : Subgroup G), H29 G x K A B Q y

@[expose] def Lemma2910Full (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a y : G) (K A D J₀ B₁ Q₁ : Subgroup G), Ctx21 G x K A a D J₀ → H29 G x K A B₁ Q₁ y →
    ∃ J : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J ∧ IsA7Bar J ∧
      (∀ J'' : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J'' → IsA7Bar J'' → J'' = J) ∧
      ∀ B Q : Subgroup G, H29 G x K A B Q y → B ≤ normalizer (J : Set G) ∧
        ∃ (e : kBar J ≃* alternatingGroup (Fin 7)) (F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))),
          ImageF0F1 B J e F₀ F₁

@[expose] def Lemma2912 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a y : G) (K A D J₀ B Q J : Subgroup G), Ctx21 G x K A a D J₀ → H29 G x K A B Q y →
    (∀ B' : Subgroup G, IsExtSource2 x K A B' → pRank 2 ↥B' = 4 →
      ¬ (A7InGamma K A B' ∧ IsKBal 3 B' ∧ IsWeakKBal 2 B')) →
    IsPCompIn 2 (centralizer ({y} : Set G)) J → IsA7Bar J →
    (∀ J'' : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J'' → IsA7Bar J'' → J'' = J) →
    (∀ B' Q' : Subgroup G, H29 G x K A B' Q' y → B' ≤ normalizer (J : Set G) ∧
      ∃ (e : kBar J ≃* alternatingGroup (Fin 7)) (F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))),
        ImageF0F1 B' J e F₀ F₁) →
    ∃ u ∈ B ⊓ cSec K, orderOf u = 2 ∧ pLayerOf 2 (J ⊓ centralizer ({u} : Set G)) ≠ ⊥

@[expose] def FinalE8 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a y u : G) (K A D J₀ B Q J : Subgroup G), Ctx21 G x K A a D J₀ → H29 G x K A B Q y →
    IsPCompIn 2 (centralizer ({y} : Set G)) J → IsA7Bar J → B ≤ normalizer (J : Set G) →
    u ∈ B ⊓ cSec K → orderOf u = 2 → pLayerOf 2 (J ⊓ centralizer ({u} : Set G)) ≠ ⊥ →
    ∃ S : Subgroup G, S ≤ CxK x K ∧ CFSG.IsElementaryAbelian 2 ↥S ∧ 3 ≤ pRank 2 ↥S

theorem sec29Final_of_nodes (hN1 : Exists29H G) (hN2 : Lemma2910Full G) (hN3 : Lemma2912 G)
    (hN4 : FinalE8 G) : Sec29Final G := by
  intro x a K A D J hc hSD hC hnoG
  obtain ⟨y, B, Q, hB⟩ := hN1 x a K A D J hc hSD hC hnoG
  obtain ⟨J', hJ', hJA7, huniq, hall⟩ := hN2 x a y K A D J B Q hc hB
  obtain ⟨hBN, -⟩ := hall B Q hB
  obtain ⟨u, hu, hu2, hJu⟩ := hN3 x a y K A D J B Q J' hc hB hnoG hJ' hJA7 huniq hall
  obtain ⟨S, hSC, -, hS3⟩ := hN4 x a y u K A D J B Q J' hc hB hJ' hJA7 hBN hu hu2 hJu
  have h1 := C3.Layer1.Back.pRank_mono' hSC
  have h2 := hB.C_rank
  omega

end CFSG.GH74.Generic.BProg.B3

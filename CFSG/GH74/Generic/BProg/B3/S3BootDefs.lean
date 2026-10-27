module

public import CFSG.GH74.Generic.BProg.B3.S3Theta52
public import CFSG.GH74.Generic.BProg.Stage2Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

section SD

variable {G : Type} [Group G] [Finite G]

@[expose] def A7InGamma (K A B : Subgroup G) : Prop :=
  ∀ a₀ ∈ A ⊓ K, a₀ ≠ 1 → ∀ D₀ J₀ : Subgroup G, Obs32 A a₀ D₀ J₀ →
    Nonempty ((↥J₀ ⧸ pPrimeCore 2 ↥J₀) ≃* alternatingGroup (Fin 7)) → J₀ ≤ gammaK 2 B 3

structure Obs52 (B : Subgroup G) (b : G) (D J : Subgroup G) : Prop where
  b_ord : orderOf b = 2
  b_cent : b ∈ centralizer (B : Set G)
  D_le : IsE 2 B D
  D_rank : pRank 2 ↥D ≤ 3
  comp : IsPCompIn 2 (centralizer ({b} : Set G)) J
  D_norm : D ≤ normalizer (J : Set G)
  D_faith : ∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)
  unbal : (pRank 2 ↥D = 3 ∧
      ¬ AG D ⊓ centralizer ({b} : Set G) ≤ centralizerSection J (pPrimeCoreOf 2 J)) ∨
    (pRank 2 ↥D = 2 ∧ ∃ c ∈ AG D ⊓ centralizer ({b} : Set G), ∃ e ∈ B,
      ⁅c, e⁆ ∉ centralizerSection J (pPrimeCoreOf 2 J))

structure Boot15A (G : Type) [Group G] [Finite G] (x : G) (K A B M : Subgroup G) : Prop where
  hyp : Hyp2 G
  noAlt : NoAltJ2 G
  term : IsTwoTerminal x K
  shape : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)
  src : IsSource2 x K A
  notAllow : ¬ IsAllowable x K A
  theta : thetaHalfPrime A ≠ ⊥
  AB : A ≤ B
  B_cent : B ≤ centralizer ({x} : Set G)
  B_E4 : IsE 4 ⊤ B
  B_rank : pRank 2 ↥B = 4
  theta52 : thetaHalf 2 B ≠ ⊥
  bal52 : IsKBal 3 B ∧ IsWeakKBal 2 B
  M_ne : M ≠ ⊤
  M_norm : normalizer (thetaHalf 2 B : Set G) ≤ M
  K_le : K ≤ M
  locM : thetaHalf 1 (A.subgroupOf M) ≤ pPrimeCore 2 ↥M
  a7 : A7InGamma K A B

@[expose] def Hyp15A7 (G : Type) [Group G] : Prop :=
  ∀ (t : G) (J : Subgroup G), IsILo 2 t J →
    IsEmpty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 11)) ∧
    (Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin 7)) → center (kBar J) = ⊥)

structure Boot15B (G : Type) [Group G] [Finite G] (x : G) (K A B M : Subgroup G) : Prop
    extends Boot15A G x K A B M where
  locM' : thetaHalfPrime (A.subgroupOf M) ≤ pPrimeCore 2 ↥M
  a15A7 : Hyp15A7 G

structure BootKG (G : Type) [Group G] [Finite G] : Prop where
  a7id : ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
    a ∈ A → Obs32 A a D J →
    (∃ w ∈ pPrimeCoreOf 2 M, w ∈ centralizer ({a} : Set G) ∧ w ∈ normalizer (J : Set G) ∧
      w ∉ centralizerSection J (pPrimeCoreOf 2 J)) →
    Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7))
  excl : ∀ (x : G) (K A B M : Subgroup G) (a : G) (D J : Subgroup G), Boot15B G x K A B M →
    a ∈ A → Obs32 A a D J → Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) →
      a ∉ K → False
  h175 : ∀ (x : G) (K A B M H : Subgroup G), Hyp2 G → IsTwoTerminal x K →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
    M ≠ ⊤ → K ≤ M → gammaK 2 B 3 ≤ M → IsMinSubnormalIn K M H → barIn M H ≠ barIn M K →
      B ⊓ centralizerSection K (pPrimeCoreOf 2 K) ≤ zpowers x
  loc28 : ∀ (x : G) (K A B M : Subgroup G), Hyp2 G → IsTwoTerminal x K →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
    M ≠ ⊤ → K ≤ M → gammaK 2 B 3 ≤ M →
      ∃ _hN : (A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ≤
          normalizer (barIn M K : Set (Mbar M)),
        IsLocBal32 (↥(barIn M K) ⧸ center ↥(barIn M K))
          ((((A.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))).subgroupOf
            (normalizer (barIn M K : Set (Mbar M)))).map (rhoL (barIn M K)))
  hKB : ∀ (x : G) (K A B : Subgroup G), Hyp2 G → IsTwoTerminal x K →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
      K ≤ gammaK 2 B 3
  l15A7 : ∀ (x : G) (K A : Subgroup G) (a : G) (D J : Subgroup G), Ctx21 G x K A a D J →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → Hyp15A7 G

end SD

end CFSG.GH74.Generic.BProg.B3

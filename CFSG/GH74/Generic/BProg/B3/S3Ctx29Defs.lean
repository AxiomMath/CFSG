module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

section P0

variable {G : Type} [Group G] [Finite G]

abbrev cSec (K : Subgroup G) : Subgroup G := centralizerSection K (pPrimeCoreOf 2 K)

abbrev IsA7Bar (J : Subgroup G) : Prop :=
  Nonempty ((↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7))

abbrev IsL2OddNonSquare (J : Subgroup G) : Prop :=
  ∃ r m : ℕ, r.Prime ∧ r ≠ 2 ∧ (¬ ∃ k : ℕ, m = 2 ^ k) ∧
    LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 r m

end P0

structure Ctx29 (G : Type) [Group G] [Finite G] (x : G) (K A B Q : Subgroup G) (y b : G)
    (D J : Subgroup G) : Prop where
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
  b_mem : b ∈ B
  type : IsA7Bar J ∨ IsL2OddNonSquare J
  obs : Obs52 B b D J ∨
    (b = y ∧ Obs32 A y D J ∧ D ≤ A ∧ IsA7Bar J ∧ ¬ J ≤ gammaK 2 B 3)

@[expose] def K26 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A E : Subgroup G) (y : G), IsTwoTerminal x K → QShape3 (↥K ⧸ pPrimeCore 2 ↥K) →
    IsSource2 x K A → E ≤ K → A = E ⊔ zpowers x → y ∈ E → y ≠ 1 →
      IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))) ∧
      y ∈ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) ∧
      HasSL2Model (↥(pLayerOf 2 (K ⊓ centralizer ({y} : Set G))) ⧸
        pPrimeCore 2 ↥(pLayerOf 2 (K ⊓ centralizer ({y} : Set G)))) (fun q => Odd q ∧ 5 ≤ q) ∧
      E ⊓ cSec (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))) = zpowers y

noncomputable abbrev Ly29 {G : Type} [Group G] [Finite G] (K : Subgroup G) (y : G) : Subgroup G :=
  pLayerOf 2 (K ⊓ centralizer ({y} : Set G))

end CFSG.GH74.Generic.BProg.B3

module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3
  CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def Tab52 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B : Subgroup G) (b : G) (D J : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 →
    Obs52 B b D J → IsA7Bar J ∨ IsL2OddNonSquare J

@[expose] def NTrans (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B E : Subgroup G) (y a₀ : G), IsTwoTerminal x K → QShape3 (↥K ⧸ pPrimeCore 2 ↥K) →
    IsSource2 x K A → IsExtSource2 x K A B → pRank 2 ↥B = 4 → E ≤ K → A = E ⊔ zpowers x →
    CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 4 → y ∈ E → y ≠ 1 → a₀ ∈ E → a₀ ≠ 1 →
      ∃ g ∈ K ⊓ normalizer (A : Set G) ⊓ normalizer (B : Set G), g * a₀ * g⁻¹ = y

@[expose] noncomputable def Jstar {G : Type} [Group G] [Finite G] (B J : Subgroup G) : Subgroup G :=
  ⨆ g ∈ B, J.map (MulAut.conj g).toMonoidHom

@[expose] noncomputable def Jss {G : Type} [Group G] [Finite G] (y : G) (L : Subgroup G) : Subgroup G :=
  ⨆ (J' : Subgroup G) (_ : IsPCompIn 2 (centralizer ({y} : Set G)) J') (_ : J' ≤ cSec L), J'

abbrev Zstar {G : Type} [Group G] [Finite G] (X : Subgroup G) : Subgroup G := X ⊓ centralizerSection X (pPrimeCoreOf 2 X)

@[expose] noncomputable def perfectCoreOf {G : Type} [Group G] [Finite G] (X : Subgroup G) : Subgroup G :=
  (⨅ n : ℕ, derivedSeries ↥X n).map X.subtype

end CFSG.GH74.Generic.BProg.B3

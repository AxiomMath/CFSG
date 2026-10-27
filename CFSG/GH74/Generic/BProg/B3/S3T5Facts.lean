module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools

namespace S3T5

@[expose] def AltLocBal2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 8 ≤ n → n ≤ 10 →
    Nonempty (K ≃* alternatingGroup (Fin n)) → Th2.Bal.IsLocallyKBalanced 2 K

@[expose] def L3OuterOddCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsL3OddGt3 K →
    ∀ H : Subgroup (MulAut K), (MulAut.conj : K →* MulAut K).range ≤ H →
      ∀ u : H, u * u = 1 → (u : MulAut K) ∉ (MulAut.conj : K →* MulAut K).range →
        CFSG.Assembly.Dichotomy.involutionOddCore u = ⊥

@[expose] def NoTwoA11Obs52 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (K A B : Subgroup G) (b : G) (D J : Subgroup G), Hyp2 G → NoAltJ2 G → IsJ2Circ x K →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → IsSource2 x K A → IsExtSource2 x K A B →
    pRank 2 ↥B = 4 → Obs52 B b D J → IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) 11 → False

end S3T5

end CFSG.GH74.Generic.BProg.B3

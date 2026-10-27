module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Lemma11_1_star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (z t : G) (Q : Subgroup G),
    z * z = 1 → t * t = 1 → z * t = t * z → IsPGroup p ↥Q → Cen z ≤ normalizer (Q : Set G) →
    z ∈ ⁅Cen z, zpowers t⁆ → ¬ Q ≤ Cen z → ¬ (Q ⊓ centralizer ({t} : Set G) ≤ Cen z)

end CFSG.GH74.GLS.Stage2.Bender.Thm2

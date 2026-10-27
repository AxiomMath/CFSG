module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.CGT.Hall82.TheoremA

open CFSG.RankThree.PartTwo (altHeart)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)
open CFSG.CGT.Timmesfeld75 (WeaklyClosedIn)
open scoped commutatorElement

@[expose] def HallTheoremANat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (θ : ↥M →* Equiv.Perm (Fin 6)) (z : G)
    (π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)),
    Function.Surjective θ → θ.ker = (CFSG.Open.pCoreOf 2 M).subgroupOf M →
    z ∈ CFSG.Open.pCoreOf 2 M → z ≠ 1 → z * z = 1 → (∀ m ∈ M, m * z = z * m) →
    Function.Surjective π → π.ker = (Subgroup.zpowers z).subgroupOf (CFSG.Open.pCoreOf 2 M) →
    (∀ (m : ↥M) (q q' : ↥(CFSG.Open.pCoreOf 2 M)), (q' : G) = m * q * m⁻¹ →
      Multiplicative.toAdd (π q') = altAct (θ m) (Multiplicative.toAdd (π q))) →
    Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) = M →
    Subgroup.centralizer ({z} : Set G) = M →
      CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 M) ∧
      WeaklyClosedIn (CFSG.Open.pCoreOf 2 M) M ∧
      WeaklyClosedIn (Subgroup.zpowers z) (CFSG.Open.pCoreOf 2 M) ∧
      ∃ P : Sylow 2 G, (P : Subgroup G) ≤ M

end CFSG.CGT.Hall82.TheoremA

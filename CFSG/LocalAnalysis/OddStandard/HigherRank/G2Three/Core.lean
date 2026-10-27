module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open

structure Case3Core (G : Type) [Group G] (z : G) (K : Subgroup G) : Prop where
  orderOf_eq : orderOf z = 2
  le_centralizer : K ≤ centralizer ({z} : Set G)
  quasisimple : CFSG.IsQuasisimple ↥K
  mem : z ∈ K
  isCyclic_twoCore : IsCyclic ↥(pCoreOf 2 K)
  card_twoCore : Nat.card ↥(pCoreOf 2 K) = 4
  quotient : IsSU43 (↥K ⧸ CFSG.oddCore ↥K)
  tight : ∀ u : G, u ∈ pCoreOf 2 K → orderOf u = 4 →
    centralizer ({u} : Set G) ≤ normalizer (K : Set G)

@[expose] def YamadaCase3Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L →
    HRG23 (L ⧸ center L) → ∃ (z : G) (K : Subgroup G), Case3Core G z K

@[expose] def PSLUnitU43Leaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (n r : ℕ), 0 < n → 0 < r →
    (CFSG.Blueprint.LieModel S .PSL (2 * n) 3 r ∨ CFSG.Blueprint.LieModel S .PSU (2 * n) 3 r) →
    ∀ t : S, orderOf t = 2 → ∀ J : Subgroup S, J ≤ centralizer ({t} : Set S) →
      (J.subgroupOf (centralizer ({t} : Set S))).IsSubnormal → t ∈ J → CFSG.IsQuasisimple ↥J →
      CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .PSU 4 3 1 →
        ∃ x : ↥J, x ∈ center ↥J ∧ orderOf x = 4

end CFSG.OddStandard.HigherRank.G2Three

module

public import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

@[expose] def GMSUnitaryCentreStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsKGroupCat H →
    ∀ (n : ℕ) (J : Subgroup H) (t : H),
      CFSG.Open.IsQuasisimple ↥J → LieModel (↥J ⧸ center ↥J) .PSU 3 2 n → orderOf t = 2 →
      t ∈ centralizer (J : Set H) → (J.subgroupOf (centralizer ({t} : Set H))).Normal →
      (∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2) →
      ¬ (J.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore H))).Normal →
      (center ↥J).map J.subtype ≤ CFSG.Open.standardComponentOddCore H

end CFSG.LocalAnalysis.EvenBN.GMSK

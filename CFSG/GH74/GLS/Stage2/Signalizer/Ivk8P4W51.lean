module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Concl51w' {G : Type} [Group G] [Finite G] (k : Kind) (p : ℕ) (H P : Subgroup G) :
    Prop :=
  H ≤ normalizer ((kInfty P : Subgroup G) : Set G) ∨
    (k = Kind.ly ∧ p = 3 ∧ IsDoubleCoverOfAlt ↥(layer (HBar H)) 11)

@[expose] def Prop5_1w' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      Concl51w' k p H P

theorem prop_5_1w'_of_m (hsd : SDWr_rank2) (h52 : Lemma5_2) (h53 : Lemma5_3)
    (h55 : Lemma5_5m) : Prop5_1w' := by
  intro G _ _ z k S ctx T Tstar p H P hc
  by_contra hnot
  have hn : ¬ Concl51 k S p H P := by
    intro h
    rcases h with h | h | ⟨hk, hp, hK, -⟩
    · exact hnot (Or.inl h)
    · exact not_SDorWr hsd ctx h
    · exact hnot (Or.inr ⟨hk, hp, hK⟩)
  have l52 := h52 G z k S ctx T Tstar p H P hc hn
  obtain ⟨g, X, Y, hs53⟩ := h53 G z k S ctx T Tstar p H P hc hn l52
  have l55 := h55 G z k S ctx T Tstar p H P hc hn l52 g X Y hs53
  exact hnot (Or.inr ⟨l55.2.2.1, l55.2.2.2, l55.2.1⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

module

public import CFSG.LieType.Chevalley.ExceptionalSmallRankSchreier
public import CFSG.LieType.Chevalley.DiagramFixedModelSchreier
public import CFSG.LieType.Chevalley.AdjointCenter

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem nonempty_mulEquiv_adjointGroup
    {G : Type} [Group G] (τ : Tag) {q : ℕ}
    (h : UntwistedChevalleyModel G τ q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (G ≃* adjointGroup τ K) := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := h
  have hZ := center_adjointGroup_eq_bot (τ := τ) (K := K)
  exact ⟨K, inferInstance, inferInstance, hcard,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩⟩

theorem exceptional_G2_F4_model_Schreier
    (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ)
    (ht : t = .G2 ∨ t = .F4) (h : ChevalleyExceptionalModel G t p f) :
    (t = .G2 → derivedSeries (Outer G) 3 = ⊥) ∧ (t = .F4 → derivedSeries (Outer G) 5 = ⊥) ∧
      Group.IsSolvable (Outer G) := by
  rcases ht with rfl | rfl
  · have hm : UntwistedChevalleyModel G .G2 (p ^ f) := h.2
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hm
    have h3 : derivedSeries (Outer G) 3 = ⊥ := derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .G2 K).1 rfl)
    exact ⟨fun _ => h3, fun h' => absurd h' (by decide), ⟨⟨3, h3⟩⟩⟩
  · have hm : UntwistedChevalleyModel G .F4 (p ^ f) := h.2
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hm
    have h5 : derivedSeries (Outer G) 5 = ⊥ := derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_ordinary_small_rank_Schreier .F4 K).2 (Or.inl rfl))
    exact ⟨fun h' => absurd h' (by decide), fun _ => h5, ⟨⟨5, h5⟩⟩⟩

end CFSG.LieType.Chevalley

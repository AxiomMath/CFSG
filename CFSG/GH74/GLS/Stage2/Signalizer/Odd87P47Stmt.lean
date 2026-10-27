module

public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.GH74.GLS.Bg.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Stmt

variable {G : Type} [Group G]

@[expose] def T4CS (z : G) (k : Kind) (S T : Subgroup G) : Prop :=
  (TypeOneCase G k ∧ T = S) ∨
    (¬ TypeOneCase G k ∧ ∃ U : Subgroup G, U ≤ S ∧ IVK.IsFourSubgroup U ∧ z ∈ U ∧
      (∃ t ∈ U, IsConj z t ∧ SwapsComps z t) ∧ pLayerOf 2 (centralizer (U : Set G)) ≠ ⊥ ∧
      T = S ⊓ centralizer (U : Set G) ∧ CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer (U : Set G)))

end Stmt

@[expose] def Prop4_7S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H X T : Subgroup G) (p : ℕ), Sig4Sub G z H p X → T ≤ H ⊓ S → T4CS z k S T →
      T ≤ normalizer (X : Set G) →
      X ≤ Op p H ∨ (SDorWr S ∧ (∃ n : ℕ, LieModel (↥(nclIn H X) ⧸ pCore p ↥(nclIn H X)) .PSL 3 p n) ∧
        z ∈ nclIn H X)

@[expose] def Prop4_7cS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (H X T : Subgroup G) (p : ℕ), Sig4Sub G z H p X → T ≤ H ⊓ S → T4CS z k S T →
      T ≤ normalizer (X : Set G) → X ≤ Op p H

theorem prop4_7S_of_cS (h : Prop4_7cS) : Prop4_7S :=
  fun G _ _ z k S ctx H X T p sig hTHS hT hTX =>
    Or.inl (h G z k S ctx H X T p sig hTHS hT hTX)

theorem prop_4_7S_of (hsd : SDWr_rank2) (h47 : Prop4_7S) : Prop4_7cS := by
  intro G _ _ z k S ctx H X T p sig hTHS hT hTX
  rcases h47 G z k S ctx H X T p sig hTHS hT hTX with h | ⟨hS, -, -⟩
  · exact h
  · exact absurd hS (not_SDorWr hsd ctx)

end CFSG.GH74.GLS.Stage2.Signalizer

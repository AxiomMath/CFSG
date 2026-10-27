module

public import CFSG.ClassicalInvolution.Q3.Q3LFinal

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification

section Cases


@[expose] def TightNormalizesComponent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ →
        ¬ T ≤ Subgroup.centralizer ({z} : Set Y) → L ≤ Subgroup.normalizer (T : Set Y)

@[expose] def TightNormalInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) → classicalInvolutionOddCore Y = ⊥ →
    ∀ (z : Y) (L : Subgroup Y), IsClassicalMember3 L z →
      ∀ T : Subgroup Y, IsComponentOf T ⊤ → T ⊔ L = ⊤ → T.Normal →
        ¬ T ≤ Subgroup.centralizer ({z} : Set Y) → L ≤ T ⊔ Subgroup.centralizer (T : Set Y)

theorem solvableMemberInnerTight_of_normalizes_of_normalInner
    (h1 : TightNormalizesComponent) (h2 : TightNormalInner) : SolvableMemberInnerTight := by
  intro Y _ _ hBelow hO z L hz T hT hTL
  by_cases hTz : T ≤ Subgroup.centralizer ({z} : Set Y)
  · exact le_sup_of_le_right (hz.le_centralizer_of_le_centralizer hT hTz)
  · have hN : L ≤ Subgroup.normalizer (T : Set Y) := h1 Y hBelow hO z L hz T hT hTL hTz
    have hTn : T.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hTL]
      exact sup_le Subgroup.le_normalizer hN
    exact h2 Y hBelow hO z L hz T hT hTL hTn hTz

theorem tightNormalizesComponent_of_innerTight (h : SolvableMemberInnerTight) :
    TightNormalizesComponent := by
  intro Y _ _ hBelow hO z L hz T hT hTL _
  exact (h Y hBelow hO z L hz T hT hTL).trans
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _))

theorem tightNormalInner_of_innerTight (h : SolvableMemberInnerTight) : TightNormalInner := by
  intro Y _ _ hBelow hO z L hz T hT hTL _ _
  exact h Y hBelow hO z L hz T hT hTL

end Cases

end CFSG.ClassicalInvolution.Q3

module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open

structure O97Red (X : Type) [Group X] [Finite X] (E Y S : Subgroup X) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  core : CFSG.pPrimeCore 3 X = ⊥
  elem_E : IsElemAbelian 3 E
  card_E : Nat.card E = 9
  E_le : E ≤ Y
  gamma_le : rankThreeGamma 1 3 E ≤ Y
  rank_Y : pRank 3 Y ≤ 3
  rank23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
    pRank 3 (Subgroup.normalizer (T : Set X)) ≤ 3
  two_S : IsPGroup 2 S
  S_le : S ≤ Y
  normal_S : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S

theorem O98Red.toO97Red {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} {z : X}
    (h : O98Red X E Y S z) : O97Red X E Y S :=
  ⟨h.catalog, h.core, h.elem_E, h.card_E, h.E_le, h.gamma_le, h.rank_Y, h.rank23, h.two_S,
    h.S_le, h.normal_S⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15

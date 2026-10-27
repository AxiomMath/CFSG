module

public import CFSG.GH74.GLS.C3.Layer1.Th2P85Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2CaseI
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P85

@[expose] def B_thm2_p88b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x y : G) (K T S M L : Subgroup G),
    P85Struct x y K T S M L → ¬ IsTerminalPair 2 x K → gammaK 2 (T ⊓ CxK x K) 1 ≤ M

theorem gammaK_le_M_of_p88b (h : B_thm2_p88b) {G : Type} [Group G] [Finite G] {x y : G}
    {K T S M L : Subgroup G} (hstruct : P85Struct x y K T S M L) :
    gammaK 2 (T ⊓ CxK x K) 1 ≤ M := by
  by_cases hterm : IsTerminalPair 2 x K
  · rcases hstruct.choice with hM1 | ⟨ρ, B, hM2⟩
    · exact (Th2.CaseI.gammaK_le_normalizer_of_standard hM1.standard hM1.sylowQ).trans hM1.le_M
    · exact absurd hterm hM2.nonterminal
  · exact h G x y K T S M L hstruct hterm

theorem centralizer_le_M_of_p88b (h : B_thm2_p88b) {G : Type} [Group G] [Finite G] {x y : G}
    {K T S M L : Subgroup G} (hstruct : P85Struct x y K T S M L) :
    centralizer ({x} : Set G) ≤ M := by
  have hstd := hstruct.choice
  have hstd' : Th2Std x y K T S := by
    rcases hstd with hM1 | ⟨ρ, B, hM2⟩
    · exact hM1.std
    · exact hM2.std
  exact (C3.Layer1.U1a.centralizer_le_gammaK (Q := T ⊓ CxK x K)
    ⟨hstd'.x_mem_T, hstd'.x_mem_CxK⟩ hstd'.orderOf_x).trans (gammaK_le_M_of_p88b h hstruct)

end CFSG.GH74.GLS

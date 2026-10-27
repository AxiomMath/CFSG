module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25End
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M7

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Statements

@[expose] def A7C25_16inv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → ¬ IsFAut R' a

end Statements

section Reductions

theorem mirror_c25_11 (h11 : A7C25_11) : Hat2A7M.Asc77.C25_11 :=
  fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ h => h11 G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror h)

theorem a7C25_16_of_inv (h11 : A7C25_11) (hinv : A7C25_16inv) : A7C25_16 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS
  have hinv' : Hat2A7M.Asc77.T7U.C25_16inv :=
    fun G _ _ _ Ω K K' W S R R' z t u₁ u₂ h a haS ha2 =>
      hinv G Ω K K' W S R R' z t u₁ u₂ (Hyp25A7.of_mirror h) a haS ha2
  exact Hat2A7M.Asc77.T7U.c25_16_of_inv (mirror_c25_11 h11) hinv' G Ω K K' W S R R' z t u₁ u₂
    hyp.toMirror a haS

theorem a7C25_E4_of_6_16inv (h6 : A7C25_6) (hinv : A7C25_16inv) (hexit : A7ExitTF4) :
    A7C25_E4 :=
  a7C25_E4_of_parts (a7C25_11_of_5_6 a7C25_5_proved h6)
    (a7C25_16_of_inv (a7C25_11_of_5_6 a7C25_5_proved h6) hinv) hexit

end Reductions

end CFSG.ClassicalInvolution.Hat2A7S

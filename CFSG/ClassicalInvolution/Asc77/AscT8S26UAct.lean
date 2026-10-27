module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26Four
import CFSG.ClassicalInvolution.Asc77.AscT8S26UActEng

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def S26Act : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoS4 Ω W →
        ∀ P ∈ DSet Ω W, ∀ M ∈ Ω, P ≤ M → M ≠ K → M ≠ J → ∀ u : G, IsUniqueInvolution M u →
          ∃ ε : ℕ, ε ≤ 1 ∧
            ∀ x ∈ omegaNbrGen Ω K, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (omegaNbrGen Ω K)

variable {p f}

theorem c26_2_u_of_act (h : S26Act p f) : C26_2_u p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hW : W ∈ WSet Ω := hs.hW.1
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have hPsyl : IsSylow2In P M := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hMΩ hPD.1 hPM
  have huW : u ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW hMΩ hPD hPsyl hu).2
  have htW : t ∈ W := (uniqueInvolution_mem_W hp hq hΩ hW hJΩ hTD hTsyl hs.ht).2
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  exact c26_2_u_of_actE hs.hJ hTJ hTS hWS hs.ht huW htW
    (h G Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu)

end CFSG.ClassicalInvolution.Asc77

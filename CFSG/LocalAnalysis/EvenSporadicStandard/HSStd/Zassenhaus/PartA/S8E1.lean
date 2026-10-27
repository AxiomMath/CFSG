module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Local

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section E1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem componentLayerOf_le (H : Subgroup G) : GorensteinWalter.componentLayerOf H ≤ H :=
  sSup_le fun _ hX => hX.1

theorem card_alt6_sq : Nat.card (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) = 129600 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem PA7.E1_not_cent_t (hb : PAB G L t E W z) (a : PA7 L t E z) :
    ¬ ∀ e ∈ a.E₁, e * t = t * e := by
  intro h
  have hub : ∀ e ∈ a.E₁, e * a.ub = a.ub * e := fun e he =>
    mem_Cen.1 (componentLayerOf_le _ (a.E₁_le he))
  have hle := PA5.perfect_le_J hb a.toPA6.toPA5 a.E₁ h hub a.E₁_perf
  have h1 : Nat.card ↥a.E₁ ≤ Nat.card ↥(derivedIn a.Abar) := Subgroup.card_le_of_le hle
  rw [s8_J_card a.Abar a.eAbar] at h1
  obtain ⟨f, hf, -⟩ := a.E₁_cover
  have h2 := Nat.card_le_card_of_surjective f hf
  rw [card_alt6_sq] at h2
  omega

end E1

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

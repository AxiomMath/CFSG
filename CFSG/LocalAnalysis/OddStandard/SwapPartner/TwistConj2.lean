module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTwist

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem twist_facts_conj (hC : CentData z ι) {x : G}
    {π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)} (hOS : OneSided z ι x π)
    (κ : ↥(centralizer ({x} : Set G)) →* ℤˣ) :
    ∃ ε χ : Perm (Fin 8) →* ℤˣ, (ε = 1 ∨ ε = sign) ∧ (χ = 1 ∨ χ = sign) ∧
      ∀ (ρ : Perm (Fin 8)) (hρx : ι (liftS8 ρ) ∈ centralizer ({x} : Set G))
        (hzρ : z * ι (liftS8 ρ) ∈ centralizer ({x} : Set G)),
        κ ⟨ι (liftS8 ρ), hρx⟩ = χ ρ ∧
          (ρ * ρ = 1 →
            Multiset.card (π ⟨ι (liftS8 ρ), hρx⟩).cycleType =
                Multiset.card ρ.cycleType + (if ε ρ = -1 then 1 else 0) ∧
              Multiset.card (π ⟨z * ι (liftS8 ρ), hzρ⟩).cycleType =
                Multiset.card ρ.cycleType + (if ε ρ = -1 then 0 else 1)) := by
  let β : Perm (Fin 8) →* Perm (Fin 10) := beta (ι := ι) (π := π) hOS.eq
  have hβ : β = beta (ι := ι) (π := π) hOS.eq := rfl
  have hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ := beta_comm_τ₀ hC hOS
  obtain ⟨ε, hε⟩ := exists_swapIndicator β hcomm
  refine ⟨ε, κ.comp (liftS8Centralizer (ι := ι) hOS.eq), ?_, ?_, ?_⟩
  · exact eq_one_or_eq_sign ε
  · exact eq_one_or_eq_sign (κ.comp (liftS8Centralizer (ι := ι) hOS.eq))
  · intro ρ hρx hzρ
    have hval : (κ.comp (liftS8Centralizer (ι := ι) hOS.eq)) ρ =
        κ ⟨ι (liftS8 ρ), hρx⟩ := by
      show κ (liftS8Centralizer (ι := ι) hOS.eq ρ) = κ ⟨ι (liftS8 ρ), hρx⟩
      exact congrArg κ (Subtype.ext rfl)
    refine ⟨hval.symm, ?_⟩
    intro hρ2
    have hβinj : Function.Injective β := by rw [hβ]; exact beta_injective hC hOS
    have hβne : ∀ ρ, β ρ ≠ τ₀ := by rw [hβ]; exact beta_ne_τ₀ hC hOS
    have hcard := card_cycleType_of_commute_swap β hβinj hcomm hβne hρ2
    have hπρ : π ⟨ι (liftS8 ρ), hρx⟩ = β ρ := by
      rw [hβ]
      exact (beta_apply (ι := ι) (π := π) hOS.eq ρ hρx).symm
    have hπzρ : π ⟨z * ι (liftS8 ρ), hzρ⟩ = τ₀ * β ρ := by
      have hzx : z ∈ centralizer ({x} : Set G) := z_mem_centralizer_of_oneSided hC hOS
      have hdecomp : (⟨z * ι (liftS8 ρ), hzρ⟩ : ↥(centralizer ({x} : Set G))) =
          (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) *
            liftS8Centralizer (ι := ι) hOS.eq ρ :=
        Subtype.ext rfl
      rw [hdecomp, map_mul, hOS.swap hzx, hβ]
      rfl
    have hiff : ε ρ = -1 ↔ β ρ 8 = 9 := by
      rw [hε ρ]
      by_cases h8 : β ρ 8 = 9
      · rw [if_pos h8]
        exact ⟨fun _ => h8, fun _ => rfl⟩
      · rw [if_neg h8]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h8⟩
    have hif1 : (if β ρ 8 = 9 then (1 : ℕ) else 0) =
        (if ε ρ = -1 then 1 else 0) := by
      by_cases h8 : β ρ 8 = 9
      · rw [if_pos h8, if_pos (hiff.mpr h8)]
      · rw [if_neg h8, if_neg (fun h => h8 (hiff.mp h))]
    have hif2 : (if β ρ 8 = 9 then (0 : ℕ) else 1) =
        (if ε ρ = -1 then 0 else 1) := by
      by_cases h8 : β ρ 8 = 9
      · rw [if_pos h8, if_pos (hiff.mpr h8)]
      · rw [if_neg h8, if_neg (fun h => h8 (hiff.mp h))]
    exact ⟨by rw [hπρ, hcard.1, hif1], by rw [hπzρ, hcard.2, hif2]⟩

end CFSG.OddStandard.AltStdSec.SwapPartner

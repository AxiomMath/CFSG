module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermBound

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS
open scoped commutatorElement
open AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem altFixOf_eq_map_ofSubtype (σ : Perm (Fin n)) :
    altFixOf σ = (alternatingGroup {x : Fin n // σ x = x}).map
      (Equiv.Perm.ofSubtype : Perm {x : Fin n // σ x = x} →* Perm (Fin n)) := by
  classical
  ext g
  constructor
  · intro hg
    have hcomm : g * σ = σ * g := comm_of_forall_fixed hg.1
    have hg1 : ∀ x, σ (g x) = g x ↔ σ x = x := fun x => by
      have : σ (g x) = g (σ x) := by
        have := congrArg (fun e : Perm (Fin n) => e x) hcomm.symm
        simpa [Perm.mul_apply] using this
      rw [this]
      exact g.injective.eq_iff
    have hg2 : ∀ x, g x ≠ x → σ x = x := fun x hx => by
      by_contra h
      exact hx (hg.1 x h)
    refine ⟨g.subtypePerm hg1, ?_, Equiv.Perm.ofSubtype_subtypePerm hg1 hg2⟩
    rw [SetLike.mem_coe, Perm.mem_alternatingGroup, Perm.sign_subtypePerm g hg1 hg2]
    exact hg.2
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨fun x hx => ?_, ?_⟩
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx)
    · rw [Equiv.Perm.sign_ofSubtype]
      exact Perm.mem_alternatingGroup.1 hτ

theorem card_altFixOf_mul_two (σ : Perm (Fin n)) (hf : 2 ≤ n - σ.support.card) :
    Nat.card (altFixOf σ) * 2 = (n - σ.support.card).factorial := by
  classical
  have hF : Nat.card {x : Fin n // σ x = x} = n - σ.support.card := by
    rw [Nat.card_eq_fintype_card]
    have := Equiv.Perm.card_fixedPoints σ
    rw [Equiv.Perm.sum_cycleType, Fintype.card_fin] at this
    exact this
  have h1 := card_alternatingGroup_mul_two (β := {x : Fin n // σ x = x}) (by omega)
  rw [hF] at h1
  rw [altFixOf_eq_map_ofSubtype, Subgroup.card_map_of_injective Equiv.Perm.ofSubtype_injective]
  exact h1

theorem center_le_altFixOf_comap (C : AhatData.CoverSetup n K) (σ : Perm (Fin n)) :
    center K ≤ (altFixOf σ).comap C.ρ := fun x hx => by
  rw [Subgroup.mem_comap, (C.ρ_eq_one_iff).2 hx]
  exact (altFixOf σ).one_mem

end CFSG.OddStandard.Solomon75

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Equiv

theorem tableVII_perm_card_centralizer (σ : Perm (Fin 5)) (h2 : σ * σ = 1)
    (hs : Perm.sign σ = -1) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 5)))) = 12 := by
  have key : ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
      (Finset.univ.filter (fun τ : Perm (Fin 5) => τ * σ = σ * τ)).card = 12 := by
    decide +kernel
  rw [← key σ h2 hs, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => Subgroup.mem_centralizer_singleton_iff)

theorem tableVII_perm_klein (v : Perm (Fin 5)) (h2 : v * v = 1) (h1 : v ≠ 1)
    (hs : Perm.sign v = 1) :
    ∃ g : Perm (Fin 5), g * v * g⁻¹ * v = v * (g * v * g⁻¹) ∧ g * v * g⁻¹ ≠ v ∧
      g * (g * v * g⁻¹) * g⁻¹ = v * (g * v * g⁻¹) := by
  have key : ∀ v : Perm (Fin 5), v * v = 1 → v ≠ 1 → Perm.sign v = 1 →
      ∃ g : Perm (Fin 5), g * v * g⁻¹ * v = v * (g * v * g⁻¹) ∧ g * v * g⁻¹ ≠ v ∧
        g * (g * v * g⁻¹) * g⁻¹ = v * (g * v * g⁻¹) := by
    decide +kernel
  exact key v h2 h1 hs

theorem tableVII_perm_commutator : commutator (Perm (Fin 5)) = alternatingGroup (Fin 5) :=
  alternatingGroup.commutator_perm_eq (by simp)

theorem tableVII_perm_card_alternating : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem tableVII_perm_alternating_le {N : Subgroup (Perm (Fin 5))} (hN : N.Normal)
    (hne : N ≠ ⊥) : alternatingGroup (Fin 5) ≤ N := by
  haveI := hN
  exact Perm.alternatingGroup_le_of_normal (by simp) ((Subgroup.nontrivial_iff_ne_bot N).2 hne)

theorem tableVII_perm_eq_top_of_normal {N : Subgroup (Perm (Fin 5))} (hN : N.Normal)
    {σ : Perm (Fin 5)} (hσ : σ ∈ N) (hs : Perm.sign σ = -1) : N = ⊤ := by
  have hne : N ≠ ⊥ := by
    rintro rfl
    rw [(Subgroup.mem_bot).1 hσ, map_one] at hs
    exact absurd hs (by decide)
  have hA := tableVII_perm_alternating_le hN hne
  refine (Subgroup.eq_top_iff' N).2 fun τ => ?_
  rcases Int.units_eq_one_or (Perm.sign τ) with h | h
  · exact hA ((Perm.mem_alternatingGroup).2 h)
  · have hm : τ * σ⁻¹ ∈ N := hA ((Perm.mem_alternatingGroup).2 (by simp [h, hs]))
    simpa using N.mul_mem hm hσ

end CFSG.EvenSporadicStandard.HNRecog.Section3

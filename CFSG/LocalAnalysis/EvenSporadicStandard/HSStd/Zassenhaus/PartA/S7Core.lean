module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

section Core

variable {T : Type} [Group T] [Finite T]

theorem commutator_le_self_of_subgroup (E : Subgroup T) : ⁅E, E⁆ ≤ E := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact E.mul_mem (E.mul_mem (E.mul_mem ha hb) (E.inv_mem ha)) (E.inv_mem hb)

theorem exists_perfect_core (P : Subgroup T) :
    ∃ E : Subgroup T, E ≤ P ∧ ⁅E, E⁆ = E ∧ ∀ H : Subgroup T, H ≤ P → ⁅H, H⁆ = H → H ≤ E := by
  let S : Set (Subgroup T) := {H | H ≤ P ∧ ⁅H, H⁆ = H}
  refine ⟨sSup S, sSup_le (fun H hH => hH.1), ?_, fun H hH hp => le_sSup ⟨hH, hp⟩⟩
  apply le_antisymm (commutator_le_self_of_subgroup _)
  apply sSup_le
  intro H hH
  calc H = ⁅H, H⁆ := hH.2.symm
    _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hH) (le_sSup hH)

theorem conj_le_perfectCore {P E : Subgroup T} (hE : ⁅E, E⁆ = E) (hEP : E ≤ P)
    (hmax : ∀ H : Subgroup T, H ≤ P → ⁅H, H⁆ = H → H ≤ E) {g : T}
    (hg : ∀ x ∈ P, g * x * g⁻¹ ∈ P) {x : T} (hx : x ∈ E) : g * x * g⁻¹ ∈ E := by
  have hH : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    apply hmax
    · rintro _ ⟨z, hz, rfl⟩
      exact hg z (hEP hz)
    · rw [← Subgroup.map_commutator, hE]
  exact hH ⟨x, hx, rfl⟩

theorem exists_perfect_subgroup_map_eq {X : Type} [Group X] (κ : T →* X)
    (hκ : Function.Surjective κ) {N : Subgroup X} (hN : ⁅N, N⁆ = N) :
    ∃ H : Subgroup T, H ≤ N.comap κ ∧ ⁅H, H⁆ = H ∧ H.map κ = N := by
  let S : Set (Subgroup T) := {H | H ≤ N.comap κ ∧ H.map κ = N}
  have hne : (N.comap κ) ∈ S := ⟨le_rfl, Subgroup.map_comap_eq_self_of_surjective hκ N⟩
  obtain ⟨H₀, hH₀, hmin⟩ := (measure fun H : Subgroup T => Nat.card H).wf.has_min S ⟨_, hne⟩
  refine ⟨H₀, hH₀.1, ?_, hH₀.2⟩
  have hle : ⁅H₀, H₀⁆ ≤ H₀ := commutator_le_self_of_subgroup H₀
  have hmem : ⁅H₀, H₀⁆ ∈ S := by
    refine ⟨hle.trans hH₀.1, ?_⟩
    rw [Subgroup.map_commutator, hH₀.2, hN]
  have h1 : ¬ Nat.card ↥⁅H₀, H₀⁆ < Nat.card ↥H₀ := hmin _ hmem
  exact Subgroup.eq_of_le_of_card_ge hle (not_lt.1 h1)

theorem map_perfectCore_eq {X : Type} [Group X] (κ : T →* X) (hκ : Function.Surjective κ)
    {N : Subgroup X} (hN : ⁅N, N⁆ = N) {E : Subgroup T} (hEP : E ≤ N.comap κ)
    (hmax : ∀ H : Subgroup T, H ≤ N.comap κ → ⁅H, H⁆ = H → H ≤ E) : E.map κ = N := by
  obtain ⟨H, hHP, hHp, hHN⟩ := exists_perfect_subgroup_map_eq κ hκ hN
  apply le_antisymm
  · rintro _ ⟨e, he, rfl⟩
    exact hEP he
  · rw [← hHN]
    exact Subgroup.map_mono (hmax H hHP hHp)

end Core

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

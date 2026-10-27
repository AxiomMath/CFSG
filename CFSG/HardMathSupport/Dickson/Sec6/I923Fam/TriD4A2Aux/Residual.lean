module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

theorem exists_derivedSeries_stable (G : Type*) [Group G] [Finite G] :
    ∃ n, derivedSeries G (n + 1) = derivedSeries G n := by
  by_contra hcon
  push Not at hcon
  have key : ∀ n, Nat.card (derivedSeries G n) + n ≤ Nat.card G := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt : derivedSeries G (n + 1) < derivedSeries G n :=
        lt_of_le_of_ne (derivedSeries_antitone G (Nat.le_succ n)) (hcon n)
      have := Subgroup.card_lt_of_lt hlt
      omega
  have := key (Nat.card G + 1)
  omega

theorem exists_residual (G : Type*) [Group G] [Finite G] :
    ∃ S : Subgroup G, ∃ _ : S.Normal, ⁅S, S⁆ = S ∧ Group.IsSolvable (G ⧸ S) := by
  obtain ⟨n, hn⟩ := exists_derivedSeries_stable G
  haveI := derivedSeries_normal G n
  refine ⟨derivedSeries G n, this, hn, ?_⟩
  refine ⟨⟨n, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (derivedSeries G n)) n]
  simp

theorem perfect_le_derivedSeries {G : Type*} [Group G] {E : Subgroup G} (hE : ⁅E, E⁆ = E)
    (n : ℕ) : E ≤ derivedSeries G n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    calc E = ⁅E, E⁆ := hE.symm
      _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ := Subgroup.commutator_mono ih ih

theorem perfect_le_of_solvable_quotient {G : Type*} [Group G] {E : Subgroup G} (hE : ⁅E, E⁆ = E)
    (N : Subgroup G) [N.Normal] (hN : Group.IsSolvable (G ⧸ N)) : E ≤ N := by
  obtain ⟨n, hn⟩ := hN.solvable
  have h1 := perfect_le_derivedSeries hE n
  have h2 : (derivedSeries G n).map (QuotientGroup.mk' N) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective N) n]
    exact hn
  intro x hx
  have : (QuotientGroup.mk' N) x ∈ (derivedSeries G n).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ (h1 hx)
  rw [h2, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 this

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

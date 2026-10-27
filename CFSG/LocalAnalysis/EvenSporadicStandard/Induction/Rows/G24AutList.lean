module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutRep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow

public section

namespace CFSG.EvenSporadicStandard.G24Aut

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Induction.AutBound
open Subgroup

section Rmul

variable {γ : ℕ → PP} {gs : Array (Array ℕ)}
  (hgs : ∀ j < gs.size, Rep nn gs[j]! (γ j)) {par pg : Array ℕ}

include hgs in
theorem rmulList_gen (hpar : ∀ k < par.size, par[k]! ≤ k) (hpg : ∀ k < par.size, pg[k]! < gs.size) :
    ∀ i, i < (buildList (idA nn) par (rmulOp gs pg)).size →
      ∃ w ∈ Subgroup.closure (γ '' {j | j < gs.size}),
        Rep nn (buildList (idA nn) par (rmulOp gs pg))[i]! w := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · refine ⟨1, one_mem _, ?_⟩
      rw [buildList_zero]
      exact rep_idA
    · have hk : k < par.size := by
        rw [buildList_size] at hi
        omega
      rw [buildList_succ (idA nn) par (rmulOp gs pg) hk (hpar k hk)]
      have hpk := hpar k hk
      obtain ⟨w, hw, hrep⟩ := ih (par[k]!) (by omega) (by rw [buildList_size]; omega)
      exact ⟨w * γ (pg[k]!), mul_mem hw (subset_closure ⟨pg[k]!, hpg k hk, rfl⟩),
        rep_compA hrep (hgs _ (hpg k hk))⟩

end Rmul

end CFSG.EvenSporadicStandard.G24Aut

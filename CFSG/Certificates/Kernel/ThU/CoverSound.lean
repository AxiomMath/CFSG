module

public import Certificates.Data.Kernel.ThU.CoverW

public section

namespace CFSG.KC.ThU

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem pg_eq_of_mem_iff {m : ℕ} {ws ws' : List (List (Fin m × Bool))}
    (h : ∀ w, w ∈ ws ↔ w ∈ ws') : PG m ws = PG m ws' := by
  have e : {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} =
      {r : FreeGroup (Fin m) | r ∈ ws'.map FreeGroup.mk} := by
    ext r
    simp only [Set.mem_setOf_eq, List.mem_map, h]
  exact congrArg PresentedGroup e

theorem pg_thUCover_eq : PG 3 thUCover = PG 3 thUCoverW :=
  pg_eq_of_mem_iff fun w => by
    rw [thUCover, mem_cover₃Words, thUCoverW, List.mem_append, List.mem_append, or_assoc]

theorem card_thUCover_of {N : ℕ} (h : Finite (PG 3 thUCoverW) ∧ Nat.card (PG 3 thUCoverW) ≤ N) :
    Finite (PG 3 thUCover) ∧ Nat.card (PG 3 thUCover) ≤ N := by
  rw [pg_thUCover_eq]
  exact h

end CFSG.KC.ThU

end

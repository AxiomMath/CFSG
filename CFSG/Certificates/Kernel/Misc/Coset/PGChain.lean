module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.KC.MiscCoset

open CFSG.CosetTable

theorem card_le_of_index_restrict {m : ℕ} (ws : List (List (Fin m × Bool))) (T : List (Fin m))
    {n N : ℕ}
    (hi : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index ≤ n)
    (hr : Finite (PG T.length (restrictWords T ws)) ∧
      Nat.card (PG T.length (restrictWords T ws)) ≤ N) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * N := by
  obtain ⟨hf, hc⟩ := hr
  obtain ⟨hfinH, hsub⟩ := card_genSub_le ws T
  have := hi.1
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T) :=
      Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T)
  refine ⟨hfin, ?_⟩
  rw [← (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} T).index_mul_card]
  exact Nat.mul_le_mul hi.2 (hsub.trans hc)

end CFSG.KC.MiscCoset

end

module

public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

theorem index_le_of_genSub {m : ℕ} {ws : List (List (Fin m × Bool))} {S : List (Fin m)} {n : ℕ}
    (h : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S).index ≤ n)
    (H : Subgroup (PG m ws)) (hH : ∀ i ∈ S, (PresentedGroup.of i : PG m ws) ∈ H) :
    H.FiniteIndex ∧ H.index ≤ n := by
  obtain ⟨hfi, hidx⟩ := h
  have hle : genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} S ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hH i hi
  have hHfi : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  refine ⟨hHfi, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hfi.index_ne_zero)
    (Subgroup.index_dvd_of_le hle)) hidx⟩

end CFSG.CosetTable

end

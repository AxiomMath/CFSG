
module

public import CFSG.CGT.M24R.L2TabBase

@[expose] public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

theorem getElem!_map_of_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {i : ℕ} (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

theorem ctx_tt {k : ℕ} (hk : k < 16) : (mkCtx ()).tt[k]! = wTab (tw k) := by
  show ((Array.range 16).map fun k => wTab (tw k))[k]! = wTab (tw k)
  rw [getElem!_map_of_lt _ _ (by simpa using hk), getElem!_pos _ _ (by simpa using hk),
    Array.getElem_range]

theorem tab_size (c : ℕ) : ((mkCtx ()).tab c).size = 16 := compT_size _ _

theorem mem_codes {c : ℕ} : c ∈ (mkCtx ()).codes ↔ c < 1048576 ∧ (mkCtx ()).valid c = true := by
  rw [Ctx8.codes, List.mem_filter, List.mem_range]

theorem codes_nodup : (mkCtx ()).codes.Nodup :=
  List.nodup_range.sublist (List.filter_sublist)

section Ctx

@[expose] def el (c : ℕ) : N8 := n8 ((mkCtx ()).word c)

end Ctx

end CFSG.CGT.M24R

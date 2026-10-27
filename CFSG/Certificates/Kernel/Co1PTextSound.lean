module

public import CFSG.Certificates.Kernel.Griess13.SLPTextSound
public import Certificates.Data.Kernel.Co1PText
public import CFSG.Sporadic.Co1Patterson.GraphRonanDataInputs

public section

namespace CFSG.KC.Co1P

open CFSG.KC.G13

theorem splitOn_comma (cs : List Char) :
    (String.ofList cs).splitOn "," = (cs.splitOn ',').map String.ofList :=
  splitOn_one "," ',' rfl rfl (by decide) rfl (by decide) cs

theorem splitOn_semi'' (cs : List Char) :
    (String.ofList cs).splitOn ";" = (cs.splitOn ';').map String.ofList :=
  splitOn_one ";" ';' rfl rfl (by decide) rfl (by decide) cs

theorem comma_not_mem_natC (n : Nat) : ',' ∉ natC n :=
  (natC_ok [] n).not_mem (by decide) (by simp)

theorem parseNats_natsC {L : List Nat} (hL : L ≠ []) :
    CFSG.Sporadic.Co1Patterson.Native.parseNats (String.ofList (natsC L)) = L := by
  unfold CFSG.Sporadic.Co1Patterson.Native.parseNats natsC
  rw [splitOn_comma, List.splitOn_intercalate ',' (fun l hl => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.1 hl
      exact comma_not_mem_natC n) (by simpa using hL),
    List.map_map, List.filterMap_map]
  have e : (String.toNat? ∘ String.ofList ∘ natC) = some := by
    funext n
    exact natC_toNat n
  rw [e, List.filterMap_some]

theorem parsePairs_pairsC {P : List (Nat × Nat)} (hP : P ≠ []) :
    CFSG.Sporadic.Co1Patterson.Native.parsePairs (String.ofList (pairsC P)) = P := by
  unfold CFSG.Sporadic.Co1Patterson.Native.parsePairs pairsC
  rw [splitOn_semi'', List.splitOn_intercalate ';' (fun l hl => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
      exact (intercalate_ok (sep_ok (List.mem_singleton.2 rfl))
        (fun m hm => by
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with rfl | rfl <;> exact natC_ok _ _)).not_mem (by decide) (by simp)) (by simpa using hP),
    List.map_map, List.filterMap_map]
  refine (List.filterMap_congr fun p _ => ?_).trans List.filterMap_some
  simp only [Function.comp_apply]
  unfold pairC
  rw [splitOn_comma, List.splitOn_intercalate ',' (fun l hl => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl
      · exact comma_not_mem_natC _
      · exact comma_not_mem_natC _) (by simp)]
  simp only [List.map_cons, List.map_nil, List.filterMap_cons, natC_toNat, List.filterMap_nil]

end CFSG.KC.Co1P

end

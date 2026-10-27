module

public import CFSG.Certificates.Kernel.SporSch.TitsCntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem surv5K_memT {kS BP M k : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {P : Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds 1755 11 PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK 1755 11 (mask 11) (1755 * 11) (PS j) (PSI j)) = true)
    (hl : LevelsOK 1755 11 PS PSI LR TR TRI kS 5 BP) (hP : Agrees LR TR P p)
    (h : all5K 1755 (1755 * 11) LR TR (survQ P M) = true) (hk : k < tot5 LR)
    (hM : hasBit M k = true) :
    unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) LR TR k) ∈
      survivors5 1755 (rawLevels 1755 S base) p := by
  rw [survivors5_mask hb hp hl hP h]
  exact List.mem_map.2 ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk, hM⟩, rfl⟩

end CFSG.KS.SporSch

end

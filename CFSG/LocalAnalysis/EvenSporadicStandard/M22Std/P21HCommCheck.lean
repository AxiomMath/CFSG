module

public import CFSG.GH74.KGroups.NativeChecks2

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21H

open CFSG.KGroups.Native CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2

variable {n : ℕ}

theorem toA_mem_enumA_of_mem {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) : toA g ∈ enumA Q := by
  rw [enumA_eq]
  exact List.mem_map.2 ⟨g, (mem_elemsT Q hQ g).2 hg, rfl⟩

end CFSG.EvenSporadicStandard.M22Std.P21H

module

public import Certificates.Data.Kernel.HMathieu.PickJ
public import CFSG.Certificates.Kernel.HMathieu.FixCertSound

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu

theorem rankJ_sound {n r : Nat} {M J : List Nat} (h : rankJ n r M J = true) :
    ((List.range (2 ^ n)).filter fun m => actM M m == m).length ≤ 2 ^ (n - r) := by
  simp only [rankJ, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hr, hJ⟩, hok⟩ := h
  rw [length_filter_eq_card, ← hr]
  exact fix_le_of_imgOK hJ hok

theorem rankOK_sound {n r : Nat} {M : List Nat} (h : rankOK n r M = true) :
    ((List.range (2 ^ n)).filter fun m => actM M m == m).length ≤ 2 ^ (n - r) :=
  rankJ_sound h

theorem rankOK_matOf {n r : Nat} {f : Nat → Nat} (hf : XorLin f) (h : rankOK n r (matOf n f) = true) :
    ((List.range (2 ^ n)).filter fun m => f m == m).length ≤ 2 ^ (n - r) := by
  have e : ((List.range (2 ^ n)).filter fun m => f m == m) =
      (List.range (2 ^ n)).filter fun m => actM (matOf n f) m == m :=
    List.filter_congr fun m hm => by rw [actM_matOf hf n m (List.mem_range.1 hm)]
  rw [e]
  exact rankOK_sound h

end CFSG.KC.HMathieu

end

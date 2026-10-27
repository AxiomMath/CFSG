module

import CFSG.Certificates.Kernel.Fi22LH.Prim
public import Certificates.Data.CFSGNative.Fi22.LH
public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Data.Kernel.Fi22.Letters

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.F4.Native CFSG.KC.Enum CFSG.KS

theorem hy_hypC_all : allN 4096 (fun c => hy 0 c == hypC 0 c && hy 1 c == hypC 1 c &&
    hy 2 c == hypC 2 c) = true := by
  decide +kernel

theorem hy_hypC : ∀ c < 4096, hy 0 c = hypC 0 c ∧ hy 1 c = hypC 1 c ∧ hy 2 c = hypC 2 c := by
  intro c hc
  have := allN_iff.1 hy_hypC_all c hc
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem upP_all : allN 4096 (fun c =>
    (notB (Nat.beq c 0) && (Nat.beq (hm c c) 0 && Nat.beq (nm c) c)) ==
      (c != 0 && hermC c c == 0 && normC c == c)) = true := by
  decide +kernel

theorem upP_eq : ∀ c < 4096, (notB (Nat.beq c 0) && (Nat.beq (hm c c) 0 && Nat.beq (nm c) c)) =
    (c != 0 && hermC c c == 0 && normC c == c) := fun c hc =>
  beq_iff_eq.1 (allN_iff.1 upP_all c hc)

theorem pd_size : phiData.size = 693 := by
  decide +kernel

theorem pd_lt : ∀ i < 693, phiData[i]! < 693 := by
  decide +kernel

theorem pd_mem : ∀ u < 693, phiData.contains u = true := by
  decide +kernel

theorem star_count :
    (List.range 3510).countP (fun k => k != 0 && ent (CFSG.KS.Fi22L.orbT 0) k == k) = 693 := by
  decide +kernel

end CFSG.KS.Fi22LH

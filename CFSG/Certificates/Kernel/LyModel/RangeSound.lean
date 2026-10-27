module

public import Certificates.Data.Kernel.LyModel.Range
public import CFSG.Certificates.Kernel.LyBase.Sound
import CFSG.Certificates.Kernel.KDense.SortSound

public section

namespace CFSG.KC.LyModel

open CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel.Sem

theorem rangeOK_sound {n N : Nat} (hn : n ≤ 2 ^ 17) (hv : StagesValid 17 N)
    (h : rangeOK n N = true) : ∀ p < n, benesPerm 17 N p < n := by
  intro p hp
  have e := congrArg (fun x => Nat.testBit x p) (Nat.eq_of_beq_eq_true h)
  have hv' : ∀ M ∈ [N], StagesValid 17 M := by
    intro M hM
    rw [List.mem_singleton.1 hM]
    exact hv
  rw [CFSG.KC.LyBase.testBit_netsApply17 hv' (ones n) (by omega),
    KDense.SortAux.testBit_ones, KDense.SortAux.testBit_ones] at e
  have e' : compN 17 [N] p = benesPerm 17 N p := rfl
  rw [e'] at e
  exact of_decide_eq_true (e.trans (decide_eq_true hp))

end CFSG.KC.LyModel

end


module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CountBase

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model
public import Certificates.Certificate26011
public import Certificates.Certificate26012
public import Certificates.Certificate26013

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43

section Counts

theorem card_sq_coset {k N : ℕ} (hkN : (k, N) ∈ cosetCount) :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * tP k * ((g : Equiv.Perm (Fin 820)) * tP k) =
      1} = N := by
  have h := Certificates.certificate26011
  simp only [cosetCounts, List.all_eq_true, beq_iff_eq] at h
  have hk : k < 8 := by
    simp only [cosetCount, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkN
    omega
  rw [card_eq_countW_P (f := sqW (tArr k)) (Pr := fun g => g * tP k * (g * tP k) = 1)]
  · exact h (k, N) hkN
  · intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    exact allLt_sq_iff hH

theorem card_comm_rep {j : ℕ} (hj : j < 9) :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * rP j = rP j * g} = repCent[j]! := by
  have h := Certificates.certificate26012
  simp only [centCounts, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [card_eq_countW_P (f := commW (idA 820) [reps[j]!])
    (Pr := fun g => g * rP j = rP j * g)]
  · exact h j hj
  · intro w g hw _
    have hH : RepW 820 (idA 820 :: w) (g * 1) := RepW.cons rep_idA hw
    rw [mul_one] at hH
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
    exact allLt_comm_iff hH (rep_rP hj)

theorem card_comm_gens {k : ℕ} (hk : k < 8) :
    Nat.card {g : P // CommGens k g} = if k = 0 then 1 else 0 := by
  classical
  have h := Certificates.certificate26013
  simp only [injCounts, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hk' := h k hk
  rw [card_eq_countW_P (f := commW (tArr k) [tabA, tabB]) (Pr := CommGens k)]
  · simpa using hk'
  · intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact and_congr (allLt_comm_iff hH rep_tabA) (allLt_comm_iff hH rep_tabB)

end Counts

end CFSG.EvenSporadicStandard.M24Std.CU43

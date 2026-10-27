
module

public import CFSG.Certificates.Kernel.SporSch.ThColsProvedBase
public import CFSG.Sporadic.ThSchreier.UASpaceInputs

public section

namespace CFSG.KS.SporSch.Pf

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th

theorem idRows_get {i : Nat} (hi : i < 248) : (idRows ())[i]! = v4OfNat (2 ^ i) := by
  have hsz : (idRows ()).size = 248 := idRows_size
  have hwf : ∀ x ∈ idRows (), x.wf = true := idRows_wf
  have hM : rowsMatrix (idRows ()) = 1 := rowsMatrix_idRows
  generalize idRows () = I at hsz hwf hM ⊢
  have h2 : i < I.size := by rw [hsz]; exact hi
  rw [getElem!_pos I i h2]
  apply V4.eq_of_toVec_eq (hwf _ (Array.getElem_mem h2))
    (v4OfNat_wf (Nat.pow_lt_pow_right (by norm_num) hi))
  funext j
  rw [toVec_v4OfNat, rowOfNat]
  have e := congrFun (congrFun hM ⟨i, hi⟩) j
  rw [rowsMatrix_apply, Array.getElem?_eq_getElem h2, Option.getD_some, Matrix.one_apply] at e
  rw [e, Nat.testBit_two_pow]
  by_cases hij : i = j.val
  · subst hij
    simp
  · have : (⟨i, hi⟩ : Fin 248) ≠ j := fun e' => hij (by rw [← e'])
    simp [hij, this]

theorem v4OfNat_zero : v4OfNat 0 = V4.zero := by
  apply V4.eq_of_toVec_eq (v4OfNat_wf (by norm_num)) V4.zero_wf
  rw [toVec_v4OfNat, V4.toVec_zero]
  funext j
  simp [rowOfNat]

end CFSG.KS.SporSch.Pf

end

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open CFSG.KS.SporSch.Pf

theorem mulD120_sound_proved {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248)
    (h : ∀ i < 248, vmT Y (X i) = if i < 120 then 2 ^ i else 0) :
    eqRows (mulRows (rowsV X) (rowsV Y)) rowsD120 = true := by
  rw [mulRows_sound_proved hX hY h, eqRows_iff]
  apply Array.ext (by rw [rowsV_size, rowsD120, Array.size_ofFn])
  intro i h1 h2
  have hi : i < 248 := by rw [rowsV_size] at h1; exact h1
  rw [getElem_rowsV _ h1]
  simp only [rowsD120, Array.getElem_ofFn]
  by_cases h120 : i < 120
  · rw [ite_eq_left h120, ite_eq_left h120, idRows_get hi]
  · rw [ite_eq_right h120, ite_eq_right h120, v4OfNat_zero]

theorem rowsAmI_sound_proved {A : Nat → Nat} (hA : CFSG.Sporadic.Th.Max3.rowsA = rowsV A)
    (hb : ∀ i < 248, A i < 2 ^ 248) :
    rowsAmI = rowsV (fun i => Nat.xor (A i) (2 ^ i)) := by
  unfold rowsAmI
  apply Array.ext (by rw [rowsV_size, Array.size_ofFn])
  intro i h1 h2
  have hi : i < 248 := by rw [rowsV_size] at h2; exact h2
  rw [getElem_rowsV _ h2, Array.getElem_ofFn]
  change (CFSG.Sporadic.Th.Max3.rowsA[i]!).xor ((idRows ())[i]!) = _
  have hAi : CFSG.Sporadic.Th.Max3.rowsA[i]! = v4OfNat (A i) := by
    rw [hA, getElem!_pos _ i (by rw [rowsV_size]; exact hi), getElem_rowsV]
  rw [hAi, idRows_get hi, v4OfNat_xor (hb i hi) (Nat.pow_lt_pow_right (by norm_num) hi)]

end CFSG.KS.SporSch

end

module

public import Certificates.Data.Kernel.Co1Odd71
public import CFSG.Certificates.Kernel.Co1FixCount
public import CFSG.Certificates.Kernel.Co1BTrSound
public import CFSG.Certificates.Kernel.Co1M.FixRank

public section

namespace CFSG.KC.Co1M

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.KD.Co1Odd CFSG.KC.Co1F2
  CFSG.KC.M1F2 Matrix

theorem mulVec_unpack (M w : ℕ) :
    rowsMatrix 24 (unpackR 24 M) *ᵥ toVecD 24 w = toVecD 24 (vmF 24 (trK 24 M) w) := by
  rw [rowsMatrix_mulVec, CFSG.KC.F2W.transposeRows_unpackR, CFSG.KC.F2W.vecMulN_unpackR]

theorem sub_eq_add2 (a b : Fin 24 → ZMod 2) : a - b = a + b := by
  funext j
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a j = x
  generalize b j = y
  revert x y
  decide

theorem fix_le_of_rankOK {M : ℕ} {W : List ℕ} (h : rankOK M W = true) :
    {v : Fin 24 → ZMod 2 | rowsMatrix 24 (unpackR 24 M) *ᵥ v = v}.ncard ≤ 2 ^ 15 := by
  unfold rankOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hpiv⟩ := h
  obtain ⟨L, hL⟩ : ∃ L, L = W.map fun v => vmF 24 (trK 24 M) v ^^^ v := ⟨_, rfl⟩
  rw [← hL] at hpiv
  obtain ⟨hlow, hnd⟩ := CFSG.KC.Co1Fix.pivK_spec L 0 hpiv
  have hLl : L.length = 9 := by rw [hL, List.length_map, hlen]
  have himg : ∀ i : Fin 9, rowsMatrix 24 (unpackR 24 M) *ᵥ toVecD 24 (W.getD i 0) -
      toVecD 24 (W.getD i 0) = CFSG.KC.Co1Fix.vecOf (L.getD i 0) := by
    intro i
    have hi : i.val < W.length := by rw [hlen]; exact i.isLt
    have e : L.getD i 0 = vmF 24 (trK 24 M) (W.getD i 0) ^^^ W.getD i 0 := by
      rw [hL, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
        List.getD_eq_getElem _ _ hi, List.getElem_map]
    rw [e, mulVec_unpack, CFSG.KC.Co1Fix.vecOf, toVecD_xor, sub_eq_add2]
  exact CFSG.KC.FixRank.ncard_fix_le_of_indep (k := 9) _
    (fun g hg => CFSG.KC.Co1Fix.piv_indep (n := 9) (by omega) (fun v hv => (hlow v hv).1) hnd g hg)
    fun i => ⟨_, himg i⟩

end CFSG.KC.Co1M

end

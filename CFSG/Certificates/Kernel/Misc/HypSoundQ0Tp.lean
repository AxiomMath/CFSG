module

public import CFSG.Certificates.Kernel.Misc.HypSoundQ0Geom
public import CFSG.Certificates.Kernel.Misc.XiTab
import CFSG.Certificates.Kernel.Misc.LinesAlg

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK
  CFSG.KC.Misc.O73 CFSG.KC.Misc.T46

private theorem genK_of_htab {UP : Nat} {TP : Nat → Nat}
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) {f : Nat} (hf : f < 693) :
    genK UP (at' 12 UP f) (TP f) = true := by
  have h1 := htab (f / 33) (by omega)
  unfold tabK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (f % 33) (by omega)
  have e : 33 * (f / 33) + f % 33 = f := by omega
  have hb : Nat.blt f 693 = true := Nat.blt_eq.mpr hf
  simp only [Nat.add_eq, e, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or] at h2
  exact h2

private theorem getD_eq_uPts {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) (i : Nat) :
    UL.getD i 0 = (uPts ())[i]! := by
  rw [pts_eq_uPts_toList H, ← Array.getElem!_toList, List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rfl

private theorem fd_fix_iff {UL : List Nat} {UP PP : Nat} {TP : Nat → Nat} (H : Pts UL UP PP)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) {f z : Nat} (hf : f < 693) (hz : z < 693) :
    fd 10 (TP f) z = z ↔ hermC (UL.getD z 0) (UL.getD f 0) = 0 := by
  obtain ⟨hz0, hzi, hzn⟩ := (isPt_iff _).1 (H.pt z hz)
  have hcy : UL.getD z 0 < 4096 := H.lt z hz
  have hcx : UL.getD f 0 < 4096 := H.lt f hf
  have h1 : fd 10 (TP f) z = ap ((tvTabsG UL.toArray)[f]!) z :=
    ((tvTabs_TR H htab hf).2 z hz).1.symm
  have h2 : (tvTabsG UL.toArray)[f]! = tvTableG UL.toArray (UL.getD f 0) := by
    rw [tvTabs_getElem hf, list_toArray_getElem! UL f]
  have h3 : ap (tvTableG UL.toArray (UL.getD f 0)) z =
      (UInt32.ofNat ((uPosG UL.toArray)[normC (tvC (UL.getD f 0) (UL.getD z 0))]!)).toNat := by
    rw [ap_tvTableG _ _ hz, list_toArray_getElem! UL z]
  have h4 : (uPosG UL.toArray)[normC (tvC (UL.getD f 0) (UL.getD z 0))]! =
      fd 10 PP (normC (tvC (UL.getD f 0) (UL.getD z 0))) := H.uPosG_get (normC_lt _)
  have h5 : (UInt32.ofNat (fd 10 PP (normC (tvC (UL.getD f 0) (UL.getD z 0))))).toNat =
      fd 10 PP (normC (tvC (UL.getD f 0) (UL.getD z 0))) := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (fd_lt 10 PP _) (by norm_num))
  rw [h1, h2, h3, h4, h5]
  constructor
  · intro h
    exact (normC_tvC_eq_iff hcy hcx hz0 hzi hzn).1 (H.eq_of_pos (normC_lt _) hz h)
  · intro h
    rw [(normC_tvC_eq_iff hcy hcx hz0 hzi hzn).2 h]
    exact H.pos_getD hz

private theorem fd_zero_of_lt_pow {P m j : Nat} (hP : P < 2 ^ m) (hm : m ≤ 10 * j) :
    fd 10 P j = 0 := by
  unfold fd
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) hm))]

theorem tp_centers_geom {UL : List Nat} {UP PP : Nat} {TP : Nat → Nat} (H : Pts UL UP PP)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) :
    (∀ z, 0 < z → z < 693 → ∃ k < 31, fd 10 (TP (23 * k)) z = z) ∧
    (∀ k < 31, ∃ p < 693, fd 10 (TP (23 * k)) p ≠ p) ∧
    (∀ k < 31, ∀ p, p < 693 → fd 10 (TP (23 * k)) p < 693) ∧
    (∀ k < 31, ∀ p, 693 ≤ p → p < 1024 → fd 10 (TP (23 * k)) p = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz0 hz
    obtain ⟨k, hk, hh⟩ := uPts_cover_centers z hz hz0
    refine ⟨k, hk, ?_⟩
    have hklt : 23 * k < 693 := by omega
    rw [fd_fix_iff H htab hklt hz, getD_eq_uPts H z, getD_eq_uPts H (23 * k)]
    exact hh
  · intro k hk
    obtain ⟨p, hp, hh⟩ := uPts_move_centers k hk
    refine ⟨p, hp, ?_⟩
    have hklt : 23 * k < 693 := by omega
    intro h
    apply hh
    have h0 := (fd_fix_iff H htab hklt hp).1 h
    rwa [getD_eq_uPts H p, getD_eq_uPts H (23 * k)] at h0
  · intro k hk p hp
    have hklt : 23 * k < 693 := by omega
    have hperm : IsPermN 693 (fd 10 (TP (23 * k))) := (genK_spec (genK_of_htab htab hklt)).2.1
    exact hperm.1 p hp
  · intro k hk p hp1 hp2
    have hklt : 23 * k < 693 := by omega
    have hG := (genK_spec (genK_of_htab htab hklt)).1
    generalize hm : 10 * 693 = m at hG
    exact fd_zero_of_lt_pow hG (by rw [← hm]; exact Nat.mul_le_mul_left 10 hp1)

end CFSG.KC.Misc.Hyp

end

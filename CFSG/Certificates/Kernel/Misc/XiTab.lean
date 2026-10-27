module

public import CFSG.Certificates.Kernel.Spor.PK.NatLetters
public import CFSG.Certificates.Kernel.Misc.LinesPerp
public import Certificates.Data.Kernel.Misc.Xi
public import Std.Tactic.BVDecide.Normalize.Bool

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines
  CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KS.TW

theorem tvTable_TR {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {v G : Nat}
    (hg : genK UP v G = true) : TR 693 (tvTableG UL.toArray v) (fd 10 G) := by
  obtain ⟨-, hperm, hG⟩ := genK_spec hg
  refine ⟨by simp [tvTableG], fun i hi => ⟨?_, hperm.1 i hi⟩⟩
  have hj : fd 10 G i < 693 := hperm.1 i hi
  have h2 : normC (tvC v UL.toArray[i]!) = UL.getD (fd 10 G i) 0 := by
    rw [list_toArray_getElem! UL i, ← H.fd12 i hi, ← hG i hi, H.fd12 _ hj]
  rw [ap_tvTableG _ _ hi, h2, H.uPosG_get (by have := H.lt _ hj; exact this), H.pos_getD hj,
    UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem tvTabs_getElem {U : Array Nat} {f : Nat} (hf : f < 693) :
    (tvTabsG U)[f]! = tvTableG U U[f]! := by
  unfold tvTabsG
  rw [getElem!_pos _ f (by simpa using hf), Array.getElem_ofFn]

theorem tvTabs_TR {UL : List Nat} {UP PP : Nat} {TP : Nat → Nat} (H : Pts UL UP PP)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true) {f : Nat} (hf : f < 693) :
    TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f)) := by
  have h1 := htab (f / 33) (by omega)
  unfold tabK at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (f % 33) (by omega)
  have e : 33 * (f / 33) + f % 33 = f := by omega
  have hb : Nat.blt f 693 = true := Nat.blt_eq.mpr hf
  simp only [Nat.add_eq, e, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or, at'_eq] at h2
  rw [tvTabs_getElem hf, list_toArray_getElem!, ← H.fd12 f hf]
  exact tvTable_TR H h2

theorem tvGensG_eq (UL : List Nat) : tvGensG UL.toArray = (gensK UL).toArray := by
  unfold tvGensG
  rw [List.filter_toArray, List.push_toArray, gensK_eq]

theorem gens_getElem (UL : List Nat) (k : Nat) :
    (tvGensG UL.toArray)[k]! = (gensK UL).getD k 0 := by
  rw [tvGensG_eq, list_toArray_getElem!]

theorem genG_TR {UL : List Nat} {UP PP : Nat} {GP : List Nat} (H : Pts UL UP PP)
    (hgen : ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true) {z : Int}
    (hz : 1 ≤ z.natAbs ∧ z.natAbs ≤ 46) :
    TR 693 (genG UL.toArray z) (fd 10 (GP.getD (z.natAbs - 1) 0)) := by
  unfold genG
  rw [gens_getElem]
  exact tvTable_TR H (hgen _ (by omega))

theorem tp_word {UL : List Nat} {UP PP : Nat} {GP : List Nat} (H : Pts UL UP PP)
    (hgen : ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true) {w : List Int}
    (hw : lettersOK 46 w = true) :
    TR 693 (wordT 693 (genG UL.toArray) w) (fd 10 (wordG GP w)) ∧
      wordG GP w < 2 ^ (10 * 693) := by
  have hw' := (lettersOK_iff 46 w).1 hw
  have hT := wordT_TR (n := 693) (by norm_num) (gens := genG UL.toArray)
    (G := fun z => fd 10 (GP.getD (z.natAbs - 1) 0)) w fun z hz => genG_TR H hgen (hw' z hz)
  have hv : ∀ x < 693, wordGF GP w x < 2 ^ 10 := fun x hx => by
    have h1 : wordGF GP w x < 693 := (hT.2 x hx).2
    omega
  refine ⟨⟨hT.1, fun i hi => ?_⟩, ?_⟩
  · have : fd 10 (wordG GP w) i = wordGF GP w i := by
      rw [wordG_eq]
      exact fd_enc hv hi
    rw [this]
    exact hT.2 i hi
  · rw [wordG_eq]
    exact enc_lt hv

theorem tp_powG {UL : List Nat} {UP PP : Nat} {GP : List Nat} (H : Pts UL UP PP)
    (hgen : ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true) {w : List Int}
    (hw : lettersOK 46 w = true) (e : Nat) :
    TR 693 (powG UL.toArray e w) (fd 10 (powP e (wordG GP w))) ∧
      powP e (wordG GP w) < 2 ^ (10 * 693) := by
  obtain ⟨hT, hP⟩ := tp_word H hgen hw
  have hc := powT_TR (n := 693) (by norm_num) hT e
  have hv : ∀ x < 693, itr (fd 10 (wordG GP w)) e x < 2 ^ 10 := fun x hx => by
    have := (hc.2 x hx).2
    omega
  refine ⟨⟨hc.1, fun i hi => ?_⟩, ?_⟩
  · have : fd 10 (powP e (wordG GP w)) i = itr (fd 10 (wordG GP w)) e i := by
      rw [powP_eq]
      exact fd_enc hv hi
    rw [this]
    exact hc.2 i hi
  · rw [powP_eq]
    exact enc_lt hv

theorem fd_idP {i : Nat} (hi : i < 693) : fd 10 (idP 693 10) i = i := by
  rw [idP_eq (by norm_num)]
  exact fd_enc (fun j hj => by
    have : (693 : Nat) ≤ 2 ^ 10 := by norm_num
    omega) hi

theorem fd_compP (A B : Nat) {i : Nat} (hi : i < 693) :
    fd 10 (compP 693 10 A B) i = fd 10 A (fd 10 B i) := by
  rw [compP_eq]
  exact fd_enc (fun x _ => fd_lt _ _ _) hi

theorem fd_powP (P e : Nat) {i : Nat} (hi : i < 693) :
    fd 10 (powP e P) i = itr (fd 10 P) e i := by
  rw [powP_eq]
  refine fd_enc (fun x hx => ?_) hi
  cases e with
  | zero => exact Nat.lt_of_lt_of_le hx (by norm_num)
  | succ e => exact fd_lt _ _ _

theorem conjK_spec {TP : Nat → Nat} {X Y : Nat} (h : ∀ k < 21, conjK TP X Y (33 * k) 33 = true)
    {p : Nat} (hp : p < 693) :
    (∀ q < 693, fd 10 X (fd 10 (TP p) (fd 10 X q)) = fd 10 (TP (fd 10 X p)) q) ∧
    (∀ q < 693, fd 10 Y (fd 10 (TP p) (fd 10 Y (fd 10 Y q))) = fd 10 (TP (fd 10 Y p)) q) := by
  have h1 := h (p / 33) (by omega)
  unfold conjK at h1
  simp only [letB_eq] at h1
  rw [allN_lqt_iff] at h1
  have h2 := h1 (p % 33) (by omega)
  have e : Nat.add (33 * (p / 33)) (p % 33) = p := by rw [Nat.add_eq]; omega
  have hb : Nat.blt p 693 = true := Nat.blt_eq.mpr hp
  simp only [e, letB_eq, impB_eq, hb, Bool.not_true, Bool.false_or, andB_eq, Bool.and_eq_true,
    Nat.beq_eq, at'_eq] at h2
  obtain ⟨h3, h4⟩ := h2
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have := congrArg (fun z => fd 10 z q) h3
    simp only [fd_compP _ _ hq] at this
    exact this
  · have := congrArg (fun z => fd 10 z q) h4
    simp only [fd_compP _ _ hq] at this
    exact this

theorem xy_facts {UL : List Nat} {UP PP : Nat} {GP : List Nat} {XP YP : Nat} {xw yw : List Int}
    (H : Pts UL UP PP)
    (hgen : ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true)
    (hxy : xyK GP xw yw = true) (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true)
    (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true) :
    TR 693 (powG UL.toArray 3 xw) (fd 10 XP) ∧ TR 693 (powG UL.toArray 2 yw) (fd 10 YP) ∧
      XP < 2 ^ (10 * 693) ∧ YP < 2 ^ (10 * 693) ∧
      (∀ p < 693, fd 10 XP (fd 10 XP p) = p) ∧
      (∀ p < 693, fd 10 YP (fd 10 YP (fd 10 YP p)) = p) := by
  obtain ⟨hxl, hyl, hx2, -, hy3, -, -, -⟩ := xyK_spec hxy
  rw [Nat.beq_eq] at hX hY
  obtain ⟨hTX, hPX⟩ := tp_powG H hgen hxl 3
  obtain ⟨hTY, hPY⟩ := tp_powG H hgen hyl 2
  subst hX hY
  refine ⟨hTX, hTY, hPX, hPY, fun p hp => ?_, fun p hp => ?_⟩
  · have h1 := congrArg (fun z => fd 10 z p) hx2
    simp only [fd_powP _ _ hp, fd_idP hp] at h1
    exact h1
  · have h1 := congrArg (fun z => fd 10 z p) hy3
    simp only [fd_powP _ _ hp, fd_idP hp] at h1
    exact h1

end CFSG.KC.Misc.Xi

end

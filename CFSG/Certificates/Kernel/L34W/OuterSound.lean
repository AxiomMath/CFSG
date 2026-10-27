
module

public import Certificates.Data.Kernel.L34W.Outer
public import CFSG.Certificates.Kernel.L34W.Tab42Sound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelBBase

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bNot_iff {b : Bool} : bNot b = true ↔ b = false := by cases b <;> simp [bNot]

theorem bEq_iff {a b : Bool} : bEq a b = true ↔ a = b := by cases a <;> cases b <;> simp [bEq, bNot]

theorem outI_iff : ∀ i < 36, (outI i = true ↔ repInS.contains i = false) := by decide +kernel

variable {G Y OT RK CM : ℕ → ℕ}

theorem Y_eq (hy : yOK G Y = true) {t i : ℕ} (ht : t < 64) (hi : i < 36) :
    Y (64 * i + t) = yK G t i := by
  unfold yOK at hy
  have h1 := allN_spec hy i hi
  rw [strictB_eq] at h1
  exact Nat.eq_of_beq_eq_true (allN_spec h1 t ht)

theorem tabRep_Y (hG : GensG G) (hy : yOK G Y = true) {t i : ℕ} (ht : t < 64) (hi : i < 36) :
    Cn (Y (64 * i + t)) ∧ TabRep (unpack 42 6 (Y (64 * i + t))) (yPerm t i) := by
  rw [Y_eq hy ht hi]
  obtain ⟨hc, e⟩ := yK_eq hG t hi
  exact ⟨hc, e ▸ tabRep_yTab hi⟩

theorem isOut_iff (hG : GensG G) (hy : yOK G Y = true) {t i : ℕ} (ht : t < 64) (hi : i < 36) :
    isOutK Y (64 * i + t) = true ↔ repInS.contains i = false ∧ yPerm t i * yPerm t i = 1 := by
  obtain ⟨hc, hr⟩ := tabRep_Y hG hy ht hi
  have e : (64 * i + t) / 64 = i := by omega
  unfold isOutK
  rw [bAnd_iff]
  change outI ((64 * i + t) / 64) = true ∧ _ ↔ _
  rw [e, outI_iff i hi, CFSG.KC.L34KSnd.invPt_iff hc, (hr.comp hr).eq_iff TabRep.idTab]

theorem out_parts (ho : outOK Y OT RK = true) :
    (∀ n < 2304, RK n < 144 → OT (RK n) = n ∧ isOutK Y n = true) ∧
      (∀ n < 2304, 144 ≤ RK n → isOutK Y n = false) ∧ ∀ j < 144, OT j < 2304 ∧ RK (OT j) = j := by
  unfold outOK at ho
  rw [bAnd_iff] at ho
  obtain ⟨h1, h2⟩ := ho
  have A : ∀ n < 2304, bIf(Nat.blt (RK n) 144, bAnd(Nat.beq (OT (RK n)) n, isOutK Y n),
      bNot (isOutK Y n)) = true := fun n hn => by
    have h := allN_spec h1 n hn
    rwa [strictB_eq] at h
  refine ⟨fun n hn hr => ?_, fun n hn hr => ?_, fun j hj => ?_⟩
  · have h := A n hn
    have hb : Nat.blt (RK n) 144 = true := Nat.blt_eq.mpr hr
    rw [hb] at h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
    exact ⟨Nat.eq_of_beq_eq_true h3, h4⟩
  · have h := A n hn
    have hb : Nat.blt (RK n) 144 = false := by
      cases h' : Nat.blt (RK n) 144
      · rfl
      · exact absurd (Nat.blt_eq.mp h') (by omega)
    rw [hb] at h
    exact bNot_iff.1 h
  · have h := allN_spec h2 j hj
    rw [strictB_eq, bAnd_iff] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem outer_mem (hG : GensG G) (hy : yOK G Y = true) (ho : outOK Y OT RK = true) {t i : ℕ}
    (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : yPerm t i * yPerm t i = 1) : ∃ j < 144, OT j = 64 * i + t := by
  obtain ⟨h1, h3, -⟩ := out_parts ho
  have hn : 64 * i + t < 2304 := by omega
  have hout := (isOut_iff hG hy ht hi).2 ⟨hS, h2⟩
  by_cases hr : RK (64 * i + t) < 144
  · exact ⟨_, hr, (h1 _ hn hr).1⟩
  · rw [h3 _ hn (by omega)] at hout
    exact absurd hout Bool.false_ne_true

theorem ot_lt (ho : outOK Y OT RK = true) {j : ℕ} (hj : j < 144) : OT j < 2304 :=
  ((out_parts ho).2.2 j hj).1

theorem ot_eq {j : ℕ} : 64 * (OT j / 64) + OT j % 64 = OT j := Nat.div_add_mod _ _

theorem outer_of (hG : GensG G) (hy : yOK G Y = true) (ho : outOK Y OT RK = true) {j : ℕ}
    (hj : j < 144) : OT j % 64 < 64 ∧ OT j / 64 < 36 ∧ repInS.contains (OT j / 64) = false ∧
      yPerm (OT j % 64) (OT j / 64) * yPerm (OT j % 64) (OT j / 64) = 1 := by
  obtain ⟨h1, -, h3⟩ := out_parts ho
  obtain ⟨hlt, hrk⟩ := h3 j hj
  have hout := (h1 (OT j) hlt (by rw [hrk]; exact hj)).2
  have ht : OT j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hi : OT j / 64 < 36 := by omega
  rw [← ot_eq (OT := OT) (j := j)] at hout
  exact ⟨ht, hi, (isOut_iff hG hy ht hi).1 hout⟩

theorem tabRep_OT (hG : GensG G) (hy : yOK G Y = true) (ho : outOK Y OT RK = true) {j : ℕ}
    (hj : j < 144) :
    Cn (Y (OT j)) ∧ TabRep (unpack 42 6 (Y (OT j))) (yPerm (OT j % 64) (OT j / 64)) := by
  obtain ⟨ht, hi, -⟩ := outer_of hG hy ho hj
  have h := tabRep_Y hG hy ht hi
  rwa [ot_eq] at h

theorem comm_iff (hG : GensG G) (hy : yOK G Y = true) (ho : outOK Y OT RK = true)
    (hc : commOK Y OT CM = true) {j j' : ℕ} (hj : j < 144) (hj' : j' < 144) :
    hasBit (CM j) j' = true ↔
      yPerm (OT j % 64) (OT j / 64) * yPerm (OT j' % 64) (OT j' / 64) =
        yPerm (OT j' % 64) (OT j' / 64) * yPerm (OT j % 64) (OT j / 64) := by
  obtain ⟨c1, r1⟩ := tabRep_OT hG hy ho hj
  obtain ⟨c2, r2⟩ := tabRep_OT hG hy ho hj'
  unfold commOK at hc
  have h := allN_spec hc j hj
  rw [strictB_eq, strictB_eq] at h
  rw [bEq_iff.1 (allN_spec h j' hj'), CFSG.KC.L34KSnd.commPt_iff c1 c2, (r1.comp r2).eq_iff (r2.comp r1)]

variable {T A BT : ℕ → ℕ}

theorem bt_spec (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (ho : ∀ j < 144, OT j < 2304) (hbt : betaOK T A OT BT = true) {j k : ℕ} (hj : j < 144)
    (hk : k < 64) : pg 10 (mask 10) (BT j) k < 1024 ∧
      dec (pg 10 (mask 10) (BT j) k) = betaYM (OT j % 64) (OT j / 64) (k, 0, 0) := by
  have hlt := ho j hj
  unfold betaOK at hbt
  have h := allN_spec hbt j hj
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq] at h
  have e : pg 10 (mask 10) (BT j) k = betaC T A (OT j % 64) (OT j / 64) (16 * k) :=
    Nat.eq_of_beq_eq_true (allN_spec h k hk)
  have ht : OT j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hi : OT j / 64 < 36 := by omega
  rw [e, dec_betaC hT hA hb ht hi (by omega), dec_sixteen]
  exact ⟨betaC_lt hb ht hi (by omega), rfl⟩

theorem kv_iff (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (ho : ∀ j < 144, OT j < 2304) (hbt : betaOK T A OT BT = true) {j k : ℕ} (hj : j < 144)
    (hk : k < 64) : kvK T BT j k = true ↔ k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧
      (betaYM (OT j % 64) (OT j / 64) (k, 0, 0)).1 = k) := by
  have e1 : (mulM (k, 0, 0) (k, 0, 0)).1 = mulC T (16 * k) (16 * k) / 16 := by
    rw [← dec_sixteen k, ← dec_mulC hT (by omega) (by omega)]
    rfl
  have e2 : (betaYM (OT j % 64) (OT j / 64) (k, 0, 0)).1 = pg 10 (mask 10) (BT j) k / 16 := by
    rw [← (bt_spec hT hA hb ho hbt hj hk).2]
    rfl
  rw [e1, e2]
  cases hk0 : Nat.beq k 0
  · have hne : k ≠ 0 := Nat.ne_of_beq_eq_false hk0
    simp only [kvK, hk0]
    rw [bAnd_iff, Nat.beq_eq, Nat.beq_eq]
    change mulC T (16 * k) (16 * k) / 16 = 0 ∧ pg 10 (mask 10) (BT j) k / 16 = k ↔ _
    simp [hne]
  · have h0 : k = 0 := Nat.eq_of_beq_eq_true hk0
    simp only [kvK, hk0]
    simp [h0]

end CFSG.KC.L34W

end

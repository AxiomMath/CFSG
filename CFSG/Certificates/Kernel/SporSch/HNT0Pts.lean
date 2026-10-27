module

public import CFSG.Certificates.Kernel.SporSch.HNT0Inv
public import CFSG.Certificates.Kernel.SporSch.HNXPtLSound

public section

set_option maxRecDepth 100000

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.EnumBase CFSG.KS.SporSch CFSG.KS.Ord
  Finset Matrix

theorem fld_packL {w : ℕ} : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ w) →
    CFSG.KS.PF.Fld w (packL w l) (fun i => l.getD i 0)
  | [], _ => CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero w) fun i => by simp
  | x :: l, h => by
    have h1 := CFSG.KS.PF.fld_or (CFSG.KS.PF.fld_one (w := w) (h x List.mem_cons_self))
      (CFSG.KS.PF.fld_shl 1 (fld_packL l fun y hy => h y (List.mem_cons_of_mem x hy)))
    rw [Nat.mul_one] at h1
    change CFSG.KS.PF.Fld w (Nat.lor x (Nat.shiftLeft (packL w l) w)) _
    refine CFSG.KS.PF.fld_congr h1 fun i => ?_
    rcases i with _ | i <;> simp

theorem fldW_of_fld {w X : ℕ} {g : ℕ → ℕ} (hX : CFSG.KS.PF.Fld w X g) {i : ℕ}
    (hg : g i < 2 ^ w) : fldW X (w * i) w = g i := by
  rw [← CFSG.KS.PF.pg_of_fld hX hg, fldW_eq']
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, CFSG.KS.PF.testBit_pgM, Nat.add_comm]

theorem fldW_packL {w : ℕ} {l : List ℕ} (h : ∀ x ∈ l, x < 2 ^ w) (i : ℕ) :
    fldW (packL w l) (Nat.mul w i) w = l.getD i 0 := by
  refine fldW_of_fld (fld_packL l h) ?_
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.two_pow_pos w

theorem omK_spec {n N : ℕ} {OM : List ℕ} (hN : N ≤ 2 ^ 21) (h : omK n N OM = true) :
    OM.length = n ∧ (∀ x ∈ OM, x < N) ∧
      ∀ i < n, ∀ j < n, OM.getD i 0 = OM.getD j 0 → i = j := by
  unfold omK at h
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlt : ∀ x ∈ OM, x < N := fun x hx => by
    have := allL_spec h2 x hx
    rwa [blt_eq, decide_eq_true_eq] at this
  have h21 : ∀ x ∈ OM, x < 2 ^ 21 := fun x hx => Nat.lt_of_lt_of_le (hlt x hx) hN
  refine ⟨by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h1, hlt, ?_⟩
  have key : ∀ i < n, ∀ j < i, OM.getD j 0 ≠ OM.getD i 0 := by
    intro i hi j hj e
    have h4 := allN_spec h3 i hi
    rw [strictB_eq] at h4
    have h5 := allN_spec h4 j hj
    rw [bIf_eq, fldW_packL h21, fldW_packL h21, e, if_pos (Nat.beq_refl _)] at h5
    exact Bool.false_ne_true h5
  intro i hi j hj e
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd e (key j hj i hij)
  · rfl
  · exact absurd e.symm (key i hi j hij)

theorem ptsK_sound {n : ℕ} {T : ℕ → ℕ} {MS CM3 M W : ℕ} {OM : List ℕ} {g : ℕ}
    (hc : constsOK CM3 M = true) (hm : masksOK MS = true)
    (hv : Canon 5 133 13 W) (h21 : ∀ x ∈ OM, x < 2 ^ 21) (h : ptsK n T MS CM3 M W OM g = true) :
    ∀ i < n, pg 8 255 g i < n ∧
      HNXP.xvec T (OM.getD (pg 8 255 g i) 0) = ordMat 5 133 13 1729 W *ᵥ HNXP.xvec T (OM.getD i 0) := by
  unfold ptsK at h
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq, strictB_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hg : ∀ k, OM.getD k 0 < 2 ^ 21 := fun k => by
    rcases Nat.lt_or_ge k OM.length with hk | hk
    · rw [List.getD_eq_getElem _ _ hk]
      exact h21 _ (List.getElem_mem hk)
    · rw [List.getD_eq_default _ _ hk]
      exact Nat.two_pow_pos 21
  have e := HNXP.ptsFn_sound hc hm hv h2 fun k _ => by
    rw [fldW_packL h21, fldW_packL h21]
    exact ⟨hg _, hg _⟩
  intro i hi
  refine ⟨?_, ?_⟩
  · have := allN_spec h1 i hi
    rwa [blt_eq, decide_eq_true_eq] at this
  · have := e i hi
    rwa [fldW_packL h21, fldW_packL h21] at this

theorem mulVec_xvec (W : ℕ) (T : ℕ → ℕ) (i : ℕ) (l : Fin 133) :
    (ordMat 5 133 13 1729 W *ᵥ HNXP.xvec T i) l =
      (((∑ k ∈ range 133, HNXP.xe T i k * HNXP.ent13 W l k) % 5 : ℕ) : ZMod 5) := by
  change ∑ k : Fin 133, ordMat 5 133 13 1729 W l k * HNXP.xvec T i k = _
  rw [ZMod.natCast_mod, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => ((HNXP.xe T i k * HNXP.ent13 W l.val k : ℕ) : ZMod 5))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, mul_comm]
  rfl

theorem unit_lane (r l : ℕ) (hl : l < 133) :
    1 <<< (13 * r) / 2 ^ (13 * l) % 2 ^ 13 = if l = r then 1 else 0 := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  by_cases e : l = r
  · subst e
    rw [if_pos rfl, Nat.div_self (Nat.two_pow_pos _)]
    norm_num
  · rw [if_neg e]
    rcases Nat.lt_or_gt_of_ne e with h | h
    · obtain ⟨d, rfl⟩ : ∃ d, r = l + 1 + d := ⟨r - l - 1, by omega⟩
      rw [show 13 * (l + 1 + d) = 13 * l + 13 * (d + 1) by ring, Nat.pow_add,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), show 13 * (d + 1) = 13 + 13 * d by ring,
        Nat.pow_add, Nat.mul_mod_right]
    · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.zero_mod]

theorem rankK_sound {n : ℕ} {T : ℕ → ℕ} {CM3 M RI : ℕ} {OM RK : List ℕ}
    (hc : constsOK CM3 M = true) (hn : n ≤ 2 ^ 8)
    (h21 : ∀ x ∈ OM, x < 2 ^ 21) (h : rankK n T CM3 M RI OM RK = true) :
    RK.length = 133 ∧ (∀ x ∈ RK, x < n) ∧ Canon 5 133 13 RI ∧
      ∀ r < 133, ordMat 5 133 13 1729 RI *ᵥ HNXP.xvec T (OM.getD (RK.getD r 0) 0) =
        fun l => if l.val = r then 1 else 0 := by
  unfold rankK at h
  simp only [bAnd_eq, Bool.and_eq_true, strictB_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen : RK.length = 133 := by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h1
  have hlt : ∀ x ∈ RK, x < n := fun x hx => by
    have := allL_spec h2 x hx
    rwa [blt_eq, decide_eq_true_eq] at this
  have hv : Canon 5 133 13 RI := HNXP.canon_of_validHN h3
  refine ⟨hlen, hlt, hv, fun r hr => ?_⟩
  have h8 : ∀ x ∈ RK, x < 2 ^ 8 := fun x hx => Nat.lt_of_lt_of_le (hlt x hx) hn
  have hb : r / 64 < 3 := by omega
  have h5 := allN_spec h4 (r / 64) hb
  have hcnt : r % 64 < bCnt 133 (r / 64) ∧ bCnt 133 (r / 64) ≤ 64 := by
    rw [HNXP.bCnt_eq]
    split <;> omega
  have hf : ∀ k < bCnt 133 (r / 64), fldW (packL 21 OM) (Nat.mul 21
      (fldW (packL 8 RK) (Nat.mul 8 (64 * (r / 64) + k)) 8)) 21 < 2 ^ 21 := fun k _ => by
    rw [fldW_eq']
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have h6 := allN_spec h5 (r % 64) hcnt.1
  have ek : 64 * (r / 64) + r % 64 = r := Nat.div_add_mod r 64
  have e : fldW (mulC CM3 (listA T M (packF (fun i => fldW (packL 21 OM) (Nat.mul 21
      (fldW (packL 8 RK) (Nat.mul 8 i) 8)) 21) (64 * (r / 64)) (bCnt 133 (r / 64)))
      (bCnt 133 (r / 64))) (trM RI)) (1729 * (r % 64)) 1729 =
      1 <<< (13 * (64 * (r / 64) + r % 64)) := Nat.eq_of_beq_eq_true h6
  rw [ek] at e
  funext l
  have e1 : fldW (mulC CM3 (listA T M (packF (fun i => fldW (packL 21 OM) (Nat.mul 21
      (fldW (packL 8 RK) (Nat.mul 8 i) 8)) 21) (64 * (r / 64)) (bCnt 133 (r / 64)))
      (bCnt 133 (r / 64))) (trM RI)) (1729 * (r % 64)) 1729 / 2 ^ (13 * l.val) % 2 ^ 13 =
      1 <<< (13 * r) / 2 ^ (13 * l.val) % 2 ^ 13 := by rw [e]
  rw [HNXP.listA_lane hc hv T hcnt.2 hcnt.1 l.isLt, HNXP.fldW_packF (f := fun i => fldW (packL 21 OM) (Nat.mul 21
    (fldW (packL 8 RK) (Nat.mul 8 i) 8)) 21) (lo := 64 * (r / 64)) hf hcnt.1, unit_lane _ _ l.isLt,
    ek] at e1
  have e2 : fldW (packL 21 OM) (Nat.mul 21 (fldW (packL 8 RK) (Nat.mul 8 r) 8)) 21 =
      OM.getD (RK.getD r 0) 0 := by
    rw [fldW_packL h8]
    exact fldW_packL h21 _
  rw [mulVec_xvec, ← e2, e1]
  split <;> simp

module

public import Certificates.Data.Kernel.SporSch.HNXSub
public import CFSG.Certificates.Kernel.SporSch.HNXPtLSound

public section

set_option maxRecDepth 100000

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord Finset Matrix

@[expose] noncomputable def rf (U : Nat → Nat) (o w i : Nat) : Nat := fldW (getRec U 76 i) o w

theorem fldW_fldW (x a w1 o w : Nat) (h : o + w ≤ w1) :
    fldW (fldW x a w1) o w = fldW x (a + o) w := by
  rw [fldW_eq, fldW_eq, fldW_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < w
  · have h2 : i + o < w1 := by omega
    rw [decide_eq_true hi, decide_eq_true h2, Bool.true_and, Bool.true_and, Bool.true_and]
    congr 1
    omega
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

theorem fldW_lt (x o w : Nat) : fldW x o w < 2 ^ w := by
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem getRec76_leaf (U : Nat → Nat) (b r : Nat) (hr : r < 64) :
    getRec U 76 (64 * b + r) = fldW (U b) (Nat.mul 76 r) 76 := by
  rw [getRec_eq, fldW_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r 76]
  rfl

theorem rf_leaf (U : Nat → Nat) (b r o w : Nat) (hr : r < 64) (h : o + w ≤ 76) :
    rf U o w (64 * b + r) = fldW (U b) (Nat.add (Nat.mul 76 r) o) w := by
  rw [rf, getRec76_leaf U b r hr, fldW_fldW _ _ _ _ _ h]
  rfl

theorem qv0_leaf (T : Nat → Nat) (b r : Nat) (hr : r < 64) :
    qv T 0 (64 * b + r) = fldW (T b) (Nat.add (Nat.mul 464 r) 399) 21 := by
  rw [qv, ← core_rec T b r hr, fldW_fldW _ _ _ _ _ (by norm_num)]

theorem recAnd_spec {P : Nat → Bool} : ∀ c, Nat.rec (motive := fun _ => Bool) true
    (fun r ih => Bool.rec (motive := fun _ => Bool) false ih (P r)) c = true → ∀ r < c, P r = true
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | c + 1, h, r, hr => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
        (fun r ih => Bool.rec (motive := fun _ => Bool) false ih (P r)) c) (P c) = true := h
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · exact recAnd_spec c h2 r hr
    · exact h1

theorem fldPack_eq (L RB o : Nat) : ∀ c,
    fldPack L RB o c = packF (fun r => fldW L (Nat.add (Nat.mul RB r) o) 21) 0 c
  | 0 => rfl
  | c + 1 => by
    change Nat.lor (fldPack L RB o c)
        (Nat.shiftLeft (fldW L (Nat.add (Nat.mul RB c) o) 21) (Nat.mul 21 c)) =
      Nat.lor (packF (fun r => fldW L (Nat.add (Nat.mul RB r) o) 21) 0 c)
        (Nat.shiftLeft (fldW L (Nat.add (Nat.mul RB (Nat.add 0 c)) o) 21) (Nat.mul 21 c))
    have e : Nat.add 0 c = c := Nat.zero_add c
    rw [fldPack_eq L RB o c, e]

theorem lane_cast (T : Nat → Nat) (W i : Nat) (l : Fin 133) :
    (((∑ k ∈ range 133, xe T i k * ent13 W l.val k) % 5 : Nat) : ZMod 5) =
      (ordMat 5 133 13 1729 W *ᵥ xvec T i) l := by
  change _ = ∑ k : Fin 133, ordMat 5 133 13 1729 W l k * xvec T i k
  rw [ZMod.natCast_mod, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun k => ((xe T i k * ent13 W l.val k : Nat) : ZMod 5))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Nat.cast_mul, mul_comm]
  rfl

theorem imgLeaf_sound {T U : Nat → Nat} {CM3 M W o b : Nat} (hc : constsOK CM3 M = true)
    (hv : Canon 5 133 13 W) (hb : b < 17813)
    (h : imgLeaf T U CM3 M (trM W) (trM CFSG.KD.OrdHN.ONE) o b = true) :
    ∀ k < hnxC b, xvec T (fldW (U b) (Nat.add (Nat.mul 76 k) o) 21) =
      ordMat 5 133 13 1729 W *ᵥ xvec T (64 * b + k) := by
  intro k hk
  have hc64 := hnxC_le b
  unfold imgLeaf at h
  rw [letB_eq', letB_eq'] at h
  have e := Nat.eq_of_beq_eq_true h
  have hone := (one_sound CFSG.KD.OrdHN.consts).1
  have hFL : fldW (packF (fun x => x) (Nat.mul 64 b) (hnxC b)) (21 * k) 21 = 64 * b + k := by
    rw [fldW_packF (fun j hj => by
      change 64 * b + j < 2 ^ 21
      rw [hnxC_eq] at hj
      split at hj <;> omega) hk]
    try rfl
  have hIL : fldW (fldPack (U b) 76 o (hnxC b)) (21 * k) 21 =
      fldW (U b) (Nat.add (Nat.mul 76 k) o) 21 := by
    rw [fldPack_eq]
    exact (fldW_packF (fun j _ => fldW_lt _ _ _) hk).trans
      (congrArg (fun r => fldW (U b) (Nat.add (Nat.mul 76 r) o) 21) (Nat.zero_add k))
  funext l
  have e1 := congrArg (fun Y => fldW Y (1729 * k) 1729 / 2 ^ (13 * l.val) % 2 ^ 13) e
  beta_reduce at e1
  rw [listA_lane hc hv T hc64 hk l.isLt, listA_lane hc hone T hc64 hk l.isLt, hFL, hIL] at e1
  have e2 := congrArg (fun x : Nat => (x : ZMod 5)) e1
  rw [lane_cast, lane_cast, one_ord, Matrix.one_mulVec] at e2
  exact e2.symm

theorem eqLeaf_sound {T U : Nat → Nat} {b : Nat} (h : eqLeaf T U b = true) :
    ∀ r < hnxC b, fldW (U b) (Nat.mul 76 r) 21 = fldW (T b) (Nat.add (Nat.mul 464 r) 399) 21 := by
  unfold eqLeaf at h
  rw [letB_eq', letB_eq'] at h
  intro r hr
  exact Nat.eq_of_beq_eq_true (recAnd_spec _ h r hr)

theorem orbLeaf_sound {U : Nat → Nat} {REPS b : Nat} (h : orbLeaf U REPS b = true) :
    ∀ r < hnxC b, orbRec U REPS (Nat.add (Nat.mul 64 b) r) (fldW (U b) (Nat.mul 76 r) 76) = true := by
  unfold orbLeaf at h
  rw [letB_eq'] at h
  exact recAnd_spec _ h

theorem bIf_true {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => absurd h' (by decide), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

theorem orbRec_sound {U : Nat → Nat} {REPS i rec : Nat} (h : orbRec U REPS i rec = true) :
    fldW rec 0 21 < 1140000 ∧ fldW rec 21 21 < 1140000 ∧ fldW rec 42 4 < 12 ∧
    labOf U (fldW rec 0 21) = fldW rec 42 4 ∧ labOf U (fldW rec 21 21) = fldW rec 42 4 ∧
    fldW REPS (21 * fldW rec 42 4) 21 ≤ i ∧
    (fldW rec 46 8 = 0 → i = fldW REPS (21 * fldW rec 42 4) 21) ∧
    (fldW rec 46 8 ≠ 0 → fldW rec 54 21 < 1140000 ∧
      fldW (getRec U 76 (fldW rec 54 21)) 46 8 + 1 = fldW rec 46 8 ∧
      fldW (getRec U 76 (fldW rec 54 21)) (21 * fldW rec 75 1) 21 = i) := by
  unfold orbRec at h
  simp only [letB_eq'] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h4, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h5, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h6, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hd0, hd1⟩ := bIf_true h
  refine ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.ble_eq.mp h6, fun hd => ?_, fun hd => ?_⟩
  · exact Nat.eq_of_beq_eq_true (hd0 (Nat.beq_eq.mpr hd))
  · have hb : Nat.beq (fldW rec 46 8) 0 = false := by
      cases e : Nat.beq (fldW rec 46 8) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hd
    have h' := hd1 hb
    obtain ⟨p1, h'⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    obtain ⟨p2, p3⟩ := (CFSG.KS.bAnd_iff _ _).1 h'
    exact ⟨Nat.blt_eq.mp p1, Nat.eq_of_beq_eq_true p2, Nat.eq_of_beq_eq_true p3⟩

theorem recPow_eq (g : Nat → Nat) : ∀ c, Nat.rec (motive := fun _ => Nat) 0
    (fun r acc => Nat.add acc (Nat.shiftLeft 1 (Nat.mul 21 (g r)))) c =
      ∑ r ∈ range c, 2 ^ (21 * g r)
  | 0 => rfl
  | c + 1 => by
    change Nat.add (Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => Nat.add acc (Nat.shiftLeft 1 (Nat.mul 21 (g r)))) c)
      (Nat.shiftLeft 1 (Nat.mul 21 (g c))) = _
    rw [recPow_eq g c, Finset.sum_range_succ]
    change _ + 1 <<< (21 * g c) = _
    rw [Nat.one_shiftLeft]
    try rfl

theorem cntLeaf_eq (U : Nat → Nat) (b : Nat) :
    cntLeaf U b = ∑ r ∈ range (hnxC b), 2 ^ (21 * fldW (U b) (Nat.add (Nat.mul 76 r) 42) 4) := by
  unfold cntLeaf
  rw [loopStrictN_eq]
  exact recPow_eq (fun r => fldW (U b) (Nat.add (Nat.mul 76 r) 42) 4) _

theorem cntSum_eq (U : Nat → Nat) (lo : Nat) : ∀ c,
    cntSum U lo c = ∑ j ∈ range c, cntLeaf U (lo + j)
  | 0 => rfl
  | c + 1 => by
    change CFSG.KC.Loop.strictN (cntSum U lo c) (fun a => Nat.add a (cntLeaf U (Nat.add lo c))) = _
    rw [loopStrictN_eq, cntSum_eq U lo c, Finset.sum_range_succ]
    try rfl

theorem digit21 (c : Nat → Nat) : ∀ m, (∀ j < m, c j < 2 ^ 21) →
    (∑ j ∈ range m, c j * 2 ^ (21 * j)) < 2 ^ (21 * m) ∧
      ∀ j < m, (∑ j ∈ range m, c j * 2 ^ (21 * j)) / 2 ^ (21 * j) % 2 ^ 21 = c j
  | 0, _ => ⟨by simp, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | m + 1, h => by
    obtain ⟨h1, h2⟩ := digit21 c m fun j hj => h j (by omega)
    have hx := h m (by omega)
    rw [Finset.sum_range_succ]
    refine ⟨?_, fun j hj => ?_⟩
    · calc (∑ j ∈ range m, c j * 2 ^ (21 * j)) + c m * 2 ^ (21 * m)
          < 2 ^ (21 * m) + c m * 2 ^ (21 * m) := by omega
        _ = 2 ^ (21 * m) * (c m + 1) := by ring
        _ ≤ 2 ^ (21 * m) * 2 ^ 21 := Nat.mul_le_mul_left _ hx
        _ = 2 ^ (21 * (m + 1)) := by rw [← Nat.pow_add]; ring_nf
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have e2 : 2 ^ (21 * m) = 2 ^ (21 * j) * (2 ^ 21 * 2 ^ (21 * (m - j - 1))) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          omega
        have e3 : c m * 2 ^ (21 * m) = 2 ^ (21 * j) * (2 ^ 21 * (c m * 2 ^ (21 * (m - j - 1)))) := by
          rw [e2]
          ring
        rw [e3, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, h2 j hj]
      · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h1, Nat.zero_add,
          Nat.mod_eq_of_lt hx]

end CFSG.KS.SporSch.HNXP

end

module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneSound
public import CFSG.Certificates.Kernel.BabyMonster.DyStabP
public import CFSG.Certificates.Kernel.BabyMonster.FixSound
public import CFSG.Certificates.Kernel.BabyMonster.Native.DyLaneQ

public section

namespace CFSG.KC.BM.Ln

set_option exponentiation.threshold 5000

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

@[expose] def LnData (Bs SS KK : List (List ℕ)) : Prop :=
  blocksOK Bs = true ∧ (∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) ∧
    (∀ s < 274, lnStripOK Bs SS s = true) ∧ SS.length = 274 ∧ KK = lnKK

theorem lanes_stOK {Bs SS KK : List (List ℕ)} (hD : LnData Bs SS KK) {F R : ℕ → ℕ}
    (h : ∀ k < 274, lnSt 256 KK SS F R 0 k = true) (i : ℕ) (hi : i < 4371) :
    dyElim 256 Bs 0 (F i) = R i := by
  obtain ⟨hB, hr, hSS, hlen, hKK⟩ := hD
  have hk : i / 16 < 274 := by omega
  have := (lnSt_sound (e := 8) hB hr hSS hlen hKK (by decide) le_rfl (by decide : 0 < 274)
    (h (i / 16) hk) (i % 16) (Nat.mod_lt _ (by decide))).1
  rw [Nat.div_add_mod, Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftLeft_zero] at this
  exact this

theorem stOK_of_lanes {Bs SS KK : List (List ℕ)} (hD : LnData Bs SS KK) {F R : ℕ → ℕ}
    (h : ∀ k < 274, lnSt 256 KK SS F R 0 k = true) : ∀ i < 4371, stOK Bs F R i = true := by
  intro i hi
  change Nat.beq (dyElim 256 Bs 0 (F i)) (R i) = true
  rw [lanes_stOK hD h i hi]
  exact Nat.beq_refl _

theorem stPOK_of_lanes {Bs SS KK : List (List ℕ)} (hD : LnData Bs SS KK) {F : ℕ → ℕ} {f : ℕ}
    {C Q : List (List ℕ)} (h : ∀ k < 274, lnSt 256 KK SS F (recOf C) 0 k = true)
    (hn : andB (Nat.beq (lenLL C) 69) (Nat.beq (lenLL Q) 69) = true)
    (hq : ∀ s < 69, lnQuot f C Q s = true) : ∀ s < 4370, stPOK Bs F f (recOf Q) s = true := by
  intro s hs
  have hQ := Fix.quotOK_sound hn hq s hs
  change Nat.beq (projRow 1197 f (dyElim 256 Bs 0 (F (skipP s)))) (recOf Q s) = true
  rw [lanes_stOK hD h _ (by unfold skipP; split <;> omega), hQ]
  unfold skipP
  exact Nat.beq_refl _

theorem run_thr (m M : ℕ) {k1 k2 : ℕ} :
    ∀ (L : List ℕ) v out j bad, k1 ≤ j → k2 ≤ j → dyRun m M k1 L v out j bad = dyRun m M k2 L v out j bad
  | [], _, _, _, _, _, _ => rfl
  | b :: L, v, out, j, bad, h1, h2 => by
    change Bool.rec (motive := fun _ => Nat) _ (dyStep m M b (dyRun m M k1 L) v out j bad) (Nat.ble k1 j) =
      Bool.rec (motive := fun _ => Nat) _ (dyStep m M b (dyRun m M k2 L) v out j bad) (Nat.ble k2 j)
    rw [Nat.ble_eq_true_of_le h1, Nat.ble_eq_true_of_le h2]
    exact dyStep_congr m M b (fun v out bad => run_thr m M L v out (j + 1) bad (by omega) (by omega)) v out bad

theorem dyElim_shift {Bs : List (List ℕ)} (hB : blocksOK Bs = true) (m : ℕ) {k' k : ℕ} (hk' : k' ≤ k)
    (hk : k ≤ 4371) (v : ℕ) : dyElim m Bs k' (v <<< (16 * (k - k'))) = dyElim m Bs k v := by
  rw [dyElim_run hB m (by omega), dyElim_run hB m hk]
  have key : ∀ n j, j + n = k → k' ≤ j →
      dyRun m (dyMask m) k' (rowsFrom Bs j) (v <<< (16 * n)) 0 j 0 =
        dyRun m (dyMask m) k (rowsFrom Bs k) v 0 k 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj hj'
      rw [Nat.add_zero] at hj
      subst hj
      rw [Nat.mul_zero, Nat.shiftLeft_zero]
      exact run_thr m _ _ v 0 j 0 hj' le_rfl
    | succ n ih =>
      intro j hj hj'
      rw [rowsFrom_cons hB (by omega)]
      change Bool.rec (motive := fun _ => Nat) _ (dyStep m (dyMask m) (recOf Bs j)
        (dyRun m (dyMask m) k' (rowsFrom Bs (j + 1))) (v <<< (16 * (n + 1))) 0 j 0) (Nat.ble k' j) = _
      rw [Nat.ble_eq_true_of_le hj']
      have h0 : Nat.beq (Nat.land (v <<< (16 * (n + 1))) (nat_lit 65535)) (nat_lit 0) = true := by
        rw [land65535, show 16 * (n + 1) = 16 * n + 16 by ring, Nat.shiftLeft_eq, Nat.pow_add,
          ← Nat.mul_assoc, fld_zero, Nat.mul_mod_left]
        rfl
      rw [dyStep_zero _ _ _ _ _ _ _ _ h0]
      have e : Nat.shiftRight (v <<< (16 * (n + 1))) 16 = v <<< (16 * n) := by
        change (v <<< (16 * (n + 1))) >>> 16 = _
        rw [show 16 * (n + 1) = 16 * n + 16 by ring, Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
      rw [e]
      exact ih (j + 1) (by omega) (by omega)
  have := key (k - k') k' (by omega) le_rfl
  rw [this]

theorem contOK_of_lanes {Bs SS KK : List (List ℕ)} (hD : LnData Bs SS KK) {R : ℕ → ℕ}
    (h : ∀ k < 274, lnCont KK Bs SS R k = true) : ∀ i < 4370, contOK Bs i = true := by
  obtain ⟨hB, hr, hSS, hlen, hKK⟩ := hD
  intro i hi
  have hk : i / 16 < 274 := by omega
  have h' : lnSt (2 ^ 7) KK SS (lnContF Bs) R (i / 16) (i / 16) = true := h (i / 16) hk
  obtain ⟨h1, h2⟩ := lnSt_sound (e := 7) hB hr hSS hlen hKK (by decide) (by decide) hk h' (i % 16)
    (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod] at h1 h2
  have hF : lnContF Bs i = contV Bs i <<< (16 * (i + 1 - 16 * (i / 16))) := by
    change Nat.shiftLeft (contV Bs i) (Nat.mul 16 (Nat.add (Nat.mod i 16) 1)) = _
    congr 1
    change 16 * (i % 16 + 1) = _
    omega
  rw [hF, dyElim_shift hB _ (by omega) (by omega)] at h1
  change Nat.blt (dyElim 128 Bs (Nat.succ i) (contV Bs i)) dyFail = true
  change dyElim (2 ^ 7) Bs (i + 1) (contV Bs i) = _ at h1
  rw [show (128 : ℕ) = 2 ^ 7 from rfl, Nat.succ_eq_add_one, h1]
  apply Nat.ble_eq_true_of_le
  have : (R i >>> (16 * (i / 16))) <<< (16 * (i / 16)) ≤ R i := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    exact Nat.div_mul_le_self _ _
  have h5 : (2 : ℕ) ^ 4371 < 2 ^ 5000 := Nat.pow_lt_pow_right (by decide) (by decide)
  change _ + 1 ≤ Nat.shiftLeft 1 5000
  rw [shl_one]
  omega

end CFSG.KC.BM.Ln

end

module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneStep
public import CFSG.Certificates.Kernel.BabyMonster.DyLaneRun
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

@[expose] def LnSim (Bs : List (List ℕ)) (e j0 : ℕ) (R : ℕ → ℕ) (j : ℕ) (K : ℕ → ℕ → ℕ → ℕ) : Prop :=
  LnMono K ∧ ∀ Y CE vs outs, LnRel (2 ^ e) j0 j R Y CE vs outs → K Y CE 0 = 0 →
    ∀ t < 16, dyRun (2 ^ e) (dyMask (2 ^ e)) j0 (rowsFrom Bs j) (vs t) (outs t) j 0 = (R t >>> j0) <<< j0

theorem dyFin_zero (out j : ℕ) : dyFin 0 out j 0 = out := rfl

theorem nthLL_eq : ∀ (L : List (List ℕ)) (i : ℕ), nthLL L i = L.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => nthLL_eq L i

theorem lnRows_eq (s : ℕ) : lnRows s = min 16 (4371 - 16 * s) := by
  change Bool.rec (motive := fun _ => Nat) 16 (4371 - 16 * s) (Nat.ble (4371 - 16 * s) 16) = _
  cases h : Nat.ble (4371 - 16 * s) 16
  · have : ¬ 4371 - 16 * s ≤ 16 := fun hh => by
      rw [Nat.ble_eq_true_of_le hh] at h
      exact absurd h (by decide)
    change 16 = _
    omega
  · have := Nat.le_of_ble_eq_true h
    change 4371 - 16 * s = _
    omega

theorem sim_end {Bs : List (List ℕ)} (hB : blocksOK Bs = true) {e j0 : ℕ} {R : ℕ → ℕ}
    (hR : ∀ t < 16, R t < 2 ^ 4371) (ONE MQ SM0 MASK LMr : ℕ) :
    LnSim Bs e j0 R 4371 (lnOut ONE MQ SM0 MASK LMr []) := by
  refine ⟨lnOut_mono _ _ _ _ _ [], fun Y CE vs outs hrel h t ht => ?_⟩
  obtain ⟨hY, -, -, -, hout⟩ := hrel
  rw [lnOut_nil] at h
  have hY0 : Y = 0 := (Nat.or_eq_zero_iff.1 (Nat.or_eq_zero_iff.1 h).1).2
  have hv : vs t = 0 := eq_zero_of_fld (fun k => by rw [← hY t ht k, hY0]; simp [fld])
  rw [rowsFrom_end hB, hv]
  change dyFin 0 (outs t) 4371 0 = _
  rw [dyFin_zero]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [hout t ht b, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hb : j0 ≤ b
  · rw [Nat.add_sub_cancel' hb]
    by_cases hb' : b < 4371
    · simp [hb, hb']
    · rw [testBit_x_ge (hR t ht) (by omega)]
      simp
  · simp [hb]

theorem sim_inner {Bs : List (List ℕ)} (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) {e : ℕ} (he1 : 1 ≤ e) (he : e ≤ 8)
    {j0 : ℕ} {R : ℕ → ℕ} {S : ℕ} {K : ℕ → ℕ → ℕ → ℕ} :
    ∀ (ps : List ℕ) (j sh : ℕ), lnRowsOK Bs S (lnKs 16 256) (lnD 16 256) ps j sh = true →
      j0 ≤ j → j + ps.length ≤ 4371 → LnSim Bs e j0 R (j + ps.length) K →
      LnSim Bs e j0 R j (lnIn lnOne (Nat.mul (2 ^ e) lnOne) lnSM0 (lnMask (2 ^ e)) lnLM S K ps sh)
  | [], j, sh, _, _, _, hK => hK
  | p :: ps, j, sh, hrows, hj0, hj, hK => by
    obtain ⟨hrow1, hrows'⟩ := andB_true hrows
    obtain ⟨hp, hS⟩ := andB_true hrow1
    have hp' : p = Nat.land (recOf Bs j) 65535 := Nat.eq_of_beq_eq_true hp
    have hS' := Nat.eq_of_beq_eq_true hS
    have hlen : (p :: ps).length = ps.length + 1 := rfl
    have hIH := sim_inner (j0 := j0) (R := R) (S := S) (K := K) hB hr he1 he ps (Nat.succ j)
      (Nat.add sh 272) hrows' (by omega) (by omega)
      (by rw [show Nat.succ j + ps.length = j + (p :: ps).length by rw [hlen]; omega]; exact hK)
    have hmono := lnIn_mono lnOne (Nat.mul (2 ^ e) lnOne) lnSM0 (lnMask (2 ^ e)) lnLM S hK.1 (p :: ps) sh
    refine ⟨hmono, fun Y CE vs outs hrel h t ht => ?_⟩
    rw [lnIn_cons] at h
    have hbad := lnIn_mono lnOne (Nat.mul (2 ^ e) lnOne) lnSM0 (lnMask (2 ^ e)) lnLM S hK.1 ps _ _ _ _ h
    obtain ⟨vs', outs', hrel', hstep⟩ := ln_step he1 he hj0 (by omega) (hr j (by omega)) hS' hp' hrel
      hbad
    have hj' : j < 4371 := by omega
    rw [rowsFrom_cons hB hj']
    change Bool.rec (motive := fun _ => Nat) _ (dyStep (2 ^ e) (dyMask (2 ^ e)) (recOf Bs j)
      (dyRun (2 ^ e) (dyMask (2 ^ e)) j0 (rowsFrom Bs (j + 1))) (vs t) (outs t) j 0) (Nat.ble j0 j) = _
    rw [Nat.ble_eq_true_of_le hj0, hstep t ht]
    rw [hbad] at h
    exact hIH.2 _ _ vs' outs' hrel' h t ht

theorem sim_outer {Bs SS : List (List ℕ)} (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK 4371 j (recOf Bs j) = true) (hSS : ∀ s < 274, lnStripOK Bs SS s = true)
    (hlen : SS.length = 274) {e : ℕ} (he1 : 1 ≤ e) (he : e ≤ 8) {s0 : ℕ} {R : ℕ → ℕ}
    (hR : ∀ t < 16, R t < 2 ^ 4371) :
    ∀ n s, s + n = 274 → s0 ≤ s → LnSim Bs e (16 * s0) R (min (16 * s) 4371)
      (lnOut lnOne (Nat.mul (2 ^ e) lnOne) lnSM0 (lnMask (2 ^ e)) lnLM (SS.drop s))
  | 0, s, hs, _ => by
    rw [show s = 274 by omega, List.drop_eq_nil_of_le (by omega), show min (16 * 274) 4371 = 4371 by rfl]
    exact sim_end hB hR _ _ _ _ _
  | n + 1, s, hs, hs0 => by
    have hs' : s < 274 := by omega
    have hdrop : SS.drop s = SS[s]'(by omega) :: SS.drop (s + 1) := List.drop_eq_getElem_cons (by omega)
    have hnth : nthLL SS s = SS[s]'(by omega) := by
      rw [nthLL_eq]
      exact getD_lt _ _ _
    have hstrip := hSS s hs'
    unfold lnStripOK at hstrip
    rw [hnth] at hstrip
    rw [hdrop]
    generalize hblk : SS[s]'(by omega) = blk at hstrip
    rcases blk with _ | ⟨S, ps⟩
    · exact absurd hstrip Bool.false_ne_true
    · obtain ⟨hl, hrows⟩ := andB_true hstrip
      have hl' : ps.length = lnRows s := by
        rw [← CFSG.KC.BM.Dy.dyLenL_eq]
        exact Nat.eq_of_beq_eq_true hl
      have hrows' : lnRowsOK Bs S (lnKs 16 256) (lnD 16 256) ps (16 * s) 0 = true := hrows
      have hrs : lnRows s = min 16 (4371 - 16 * s) := lnRows_eq s
      have hmin : min (16 * s) 4371 = 16 * s := by omega
      rw [hmin]
      have hK := sim_outer (s0 := s0) hB hr hSS hlen he1 he hR n (s + 1) (by omega) (by omega)
      refine sim_inner hB hr he1 he ps (16 * s) 0 hrows' (by omega) (by rw [hl', hrs]; omega) ?_
      rw [hl', hrs, show 16 * s + min 16 (4371 - 16 * s) = min (16 * (s + 1)) 4371 by omega]
      exact hK

end CFSG.KC.BM.Ln

end

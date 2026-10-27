module

public import CFSG.Certificates.Kernel.Spor.RawSch4OSound
import all CFSG.Certificates.Kernel.Spor.RawSch3GSound
import all CFSG.Certificates.Kernel.Spor.RawSch4OSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

theorem LJ_sub_LT {n w kS TJ : Nat} {S : Nat → Nat} : LJ n w S kS TJ ⊆ LT n w S kS TJ := by
  rintro g ⟨a, ha, -, rfl⟩
  have h : Nat.shiftRight (stCnt TJ) (nat_lit 1) ≤ stCnt TJ := by
    rw [shr_eq]
    exact Nat.div_le_self _ _
  exact ⟨a, by omega, rfl⟩

set_option maxHeartbeats 2000000 in
theorem schK_of_sch6WL {n w kS kO BP i TS TJ j0 NSi N1 N2 N3 N4 N5 CH : Nat}
    {S SI LR TR TRI : Nat → Nat} {W : List (List Int)} {WS : List (List Nat)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 6) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 6) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (h23 : lv12K w (mask w) S SI kS BP (i + 1) (stepsAt n w S kS BP (i + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1)) = true)
    (h34 : lv12K w (mask w) S SI kS BP (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1)) = true)
    (h45 : lv12K w (mask w) S SI kS BP (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1))
      (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1)) = true)
    (hTS : allN (stCnt TS) (fun a => Nat.blt (stAt TS a) kS) = true)
    (hJ : incK TJ TS = true)
    (hW : wdsK n w (mask w) (pidn n w) S SI kS TJ WS j0 = true)
    (hlo : allN (stCnt (stepsAt n w S kS BP i))
      (fun j => Nat.ble j0 (stAt (stepsAt n w S kS BP i) j)) = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6) i TS
      (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6)
      (i + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (hc3 : rcnt (LR (i + 1 + 1 + 1)) ≤ N3 * CH)
    (hs3 : ∀ s < N3, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6)
      (i + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1)) (s * CH) CH = true)
    (hc4 : rcnt (LR (i + 1 + 1 + 1 + 1)) ≤ N4 * CH)
    (hs4 : ∀ s < N4, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6)
      (i + 1 + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1)) (s * CH) CH = true)
    (hc5 : rcnt (LR (i + 1 + 1 + 1 + 1 + 1)) ≤ N5 * CH)
    (hs5 : ∀ s < N5, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6)
      (i + 1 + 1 + 1 + 1 + 1) (stepsAt n w S kS BP (i + 1 + 1 + 1 + 1 + 1)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 6) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hp, -, -⟩ := head_facts hh
  obtain ⟨hsz, -, hR0, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  have hP : ∀ l < i + 6, ∀ k < rcnt (LR l), permOK n w (mask w) (n * w)
      (TR (roff n (n * w) (LR l) + k)) (TRI (roff n (n * w) (LR l) + k)) = true :=
    fun l hl' => (levelK_facts (hl l hl')).2.2.2.2.2
  have hb : ∀ l < i + 6, pg w (mask w) BP l < n := fun l hl' => by
    obtain ⟨-, -, hR, -, -, -⟩ := levelK_facts (hl l hl')
    rw [← hR.root]
    exact (hR.pt 0 hR.c_pos).1
  have hq : ∀ l < i + 6, ∀ a < rcnt (LR l),
      rpos w (mask w) (n * w) (LR l) (rpt w (mask w) (LR l) a) = a := fun l hl' a ha => by
    obtain ⟨-, -, hR, -, -, -⟩ := levelK_facts (hl l hl')
    exact (hR.pt a ha).2
  unfold lv12K at h12 h23 h34 h45
  simp only [bAnd_iff, Nat.succ_eq_add_one] at h12 h23 h34 h45
  obtain ⟨hinv1, hinv2, hfx1, hfx2, hinc12⟩ := h12
  obtain ⟨-, hinv3, -, hfx3, hinc23⟩ := h23
  obtain ⟨-, hinv4, -, hfx4, hinc34⟩ := h34
  obtain ⟨-, hinv5, -, hfx5, hinc45⟩ := h45
  have hT0 := letter_lt hinv
  have hT1 := letter_lt hinv1
  have hT2 := letter_lt hinv2
  have hT3 := letter_lt hinv3
  have hT4 := letter_lt hinv4
  have hT5 := letter_lt hinv5
  have hTSb : ∀ a < stCnt TS, stAt TS a < kS + kS := fun a ha => by
    have := Nat.blt_eq.mp (allN_iff.1 hTS a ha)
    omega
  have F0 := tree_facts hp (hl i (by omega)) hT0
  have F1 := tree_facts hp (hl (i + 1) (by omega)) hT1
  have F2 := tree_facts hp (hl (i + 1 + 1) (by omega)) hT2
  have F3 := tree_facts hp (hl (i + 1 + 1 + 1) (by omega)) hT3
  have F4 := tree_facts hp (hl (i + 1 + 1 + 1 + 1) (by omega)) hT4
  have F5 := tree_facts hp (hl (i + 1 + 1 + 1 + 1 + 1) (by omega)) hT5
  have inc12 := inc_sub (n := n) (w := w) (kS := kS) (S := S) hinc12
  have inc23 := inc_sub (n := n) (w := w) (kS := kS) (S := S) hinc23
  have inc34 := inc_sub (n := n) (w := w) (kS := kS) (S := S) hinc34
  have inc45 := inc_sub (n := n) (w := w) (kS := kS) (S := S) hinc45
  have hA5 := step_of_schK (d := 0) hn24 hw hp hT5 hP (by omega) hc5 hs5
  have hA4 := step_of_schK (d := 1) hn24 hw hp hT4 hP (by omega) hc4 hs4
  have hA3 := step_of_schK (d := 2) hn24 hw hp hT3 hP (by omega) hc3 hs3
  have hA2 := step_of_schK (d := 3) hn24 hw hp hT2 hP (by omega) hc2 hs2
  have hA1 := step_of_schK (d := 4) hn24 hw hp hT1 hP (by omega) hc1 hs1
  have hD := step_of_schK (d := 5) hn24 hw hp hTSb hP (by omega) hc hs
  obtain ⟨C5a, C5b⟩ := mulW one_W one_Wm hA5 (fun a ha => (F5 a ha).1) (Set.empty_subset _)
  obtain ⟨C4a, C4b⟩ := mulW C5a C5b hA4 (fun a ha => (F4 a ha).1) inc45
  obtain ⟨C3a, C3b⟩ := mulW C4a C4b hA3 (fun a ha => (F3 a ha).1) inc34
  obtain ⟨C2a, C2b⟩ := mulW C3a C3b hA2 (fun a ha => (F2 a ha).1) inc23
  obtain ⟨C1a, C1b⟩ := mulW C2a C2b hA1 (fun a ha => (F1 a ha).1) inc12
  have hUU : ∀ u ∈ PS n w TR LR (i + 1) 5, ∀ v ∈ PS n w TR LR (i + 1) 5,
      u * v ∈ PS n w TR LR (i + 1) 5 := fun u hu v hv => C1a u (C1b hu) v hv
  have hR1c := (levelK_facts (hl (i + 1) (by omega))).2.2.1.c_pos
  have hR2c := (levelK_facts (hl (i + 1 + 1) (by omega))).2.2.1.c_pos
  have hR3c := (levelK_facts (hl (i + 1 + 1 + 1) (by omega))).2.2.1.c_pos
  have hR4c := (levelK_facts (hl (i + 1 + 1 + 1 + 1) (by omega))).2.2.1.c_pos
  have hR5c := (levelK_facts (hl (i + 1 + 1 + 1 + 1 + 1) (by omega))).2.2.1.c_pos
  have hone : (1 : Equiv.Perm (Fin n)) ∈ PS n w TR LR (i + 1) 5 :=
    mem_TW.2 ⟨0, hR1c, 1, mem_TW.2 ⟨0, hR2c, 1, mem_TW.2 ⟨0, hR3c, 1, mem_TW.2 ⟨0, hR4c, 1,
      mem_TW.2 ⟨0, hR5c, 1, Set.mem_singleton 1,
      by rw [tp_zero (hl (i + 1 + 1 + 1 + 1 + 1) (by omega)), one_mul]⟩,
      by rw [tp_zero (hl (i + 1 + 1 + 1 + 1) (by omega)), one_mul]⟩,
      by rw [tp_zero (hl (i + 1 + 1 + 1) (by omega)), one_mul]⟩,
      by rw [tp_zero (hl (i + 1 + 1) (by omega)), one_mul]⟩,
      by rw [tp_zero (hl (i + 1) (by omega)), one_mul]⟩
  have hWm := wds_facts hn24 hw hp WS j0 hW
  have hJS : LJ n w S kS TJ ⊆ LT n w S kS TS := fun g hg => inc_sub hJ (LJ_sub_LT hg)
  obtain ⟨q, hq', hqf⟩ := invTab_facts hinv
  have hlo' := allN_iff.1 hlo
  have hmem : ∀ j < stCnt (stepsAt n w S kS BP i),
      lp n w S kS (stAt (stepsAt n w S kS BP i) j) ∈ Submonoid.closure (LT n w S kS TS) := by
    intro j hj
    rcases Nat.lt_or_ge j q with h1 | h1
    · have hl1 := (hqf j h1).1
      have e : lp n w S kS (stAt (stepsAt n w S kS BP i) j) =
          pp n w (S (stAt (stepsAt n w S kS BP i) j)) := by
        unfold lp
        exact if_pos hl1
      rw [e]
      exact Submonoid.closure_mono hJS (hWm _ (Nat.le_of_ble_eq_true (hlo' j hj)) hl1)
    · obtain ⟨j', rfl⟩ : ∃ j', j = q + j' := ⟨j - q, by omega⟩
      obtain ⟨hl1, e1⟩ := hqf j' (by omega)
      have e : lp n w S kS (stAt (stepsAt n w S kS BP i) (q + j')) =
          (pp n w (S (stAt (stepsAt n w S kS BP i) j')))⁻¹ := by
        unfold lp
        rw [if_neg (by omega), e1, Nat.add_sub_cancel_left]
      rw [e]
      exact inv_mem_closure (Submonoid.closure_mono hJS
        (hWm _ (Nat.le_of_ble_eq_true (hlo' j' (by omega))) hl1))
  have hfix : ∀ l d, i + 1 ≤ l → l + (d + 1) = i + 6 → ∀ v ∈ PS n w TR LR (l + 1) d,
      ∀ x : Fin n, (x : Nat) = pg w (mask w) BP l → v x = x := by
    intro l d hlo hld v hv x hx
    obtain ⟨xv, hxv⟩ := x
    simp only at hx
    subst hx
    rcases (by omega : l = i + 1 ∨ l = i + 1 + 1 ∨ l = i + 1 + 1 + 1 ∨ l = i + 1 + 1 + 1 + 1 ∨
      l = i + 1 + 1 + 1 + 1 + 1) with rfl | rfl | rfl | rfl | rfl
    · obtain rfl : d = 4 := by omega
      exact fix_of_closure (fix_LT hp hT2 hfx2 hxv) (C2b hv)
    · obtain rfl : d = 3 := by omega
      exact fix_of_closure (fix_LT hp hT3 hfx3 hxv) (C3b hv)
    · obtain rfl : d = 2 := by omega
      exact fix_of_closure (fix_LT hp hT4 hfx4 hxv) (C4b hv)
    · obtain rfl : d = 1 := by omega
      exact fix_of_closure (fix_LT hp hT5 hfx5 hxv) (C5b hv)
    · obtain rfl : d = 0 := by omega
      rw [PS_zero, Set.mem_singleton_iff] at hv
      rw [hv]
      rfl
  have ht : ∀ l, i + 1 ≤ l → l < i + 6 → ∀ a < rcnt (LR l), ∀ hr : pg w (mask w) BP l < n,
      ((tp n w TR (LR l) a) ⟨_, hr⟩ : Nat) = rpt w (mask w) (LR l) a := by
    intro l hlo hl' a ha hr
    rcases (by omega : l = i + 1 ∨ l = i + 1 + 1 ∨ l = i + 1 + 1 + 1 ∨ l = i + 1 + 1 + 1 + 1 ∨
      l = i + 1 + 1 + 1 + 1 + 1) with rfl | rfl | rfl | rfl | rfl
    · exact (F1 a ha).2 hr
    · exact (F2 a ha).2 hr
    · exact (F3 a ha).2 hr
    · exact (F4 a ha).2 hr
    · exact (F5 a ha).2 hr
  have hb0 := hb i (by omega)
  have e2 : Nat.sub (i + 6) (Nat.succ i) = 0 + 1 + 1 + 1 + 1 + 1 := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  unfold schK
  rw [e2]
  simp only [strictB_eq, allN_iff, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one]
  intro dh _
  split
  case isFalse => rfl
  rename_i hc'
  rw [allN_iff]
  intro j hj
  have hσ := prep_lp hp (hT0 j hj)
  obtain ⟨k', hk', u, hu, e⟩ := mulCS hUU hD hone (hmem j hj) (h₀ + dh) hc'
  have fu : u ⟨_, hb0⟩ = ⟨_, hb0⟩ := fix_of_closure (fix_LT hp hT1 hfx1 hb0) (C1b hu)
  have ept : pg w (mask w) (letterK S SI kS (stAt (stepsAt n w S kS BP i) j))
      (rpt w (mask w) (LR i) (h₀ + dh)) = rpt w (mask w) (LR i) k' := by
    rw [← (F0 _ hc').2 hb0, hσ, ← Equiv.Perm.mul_apply, e, Equiv.Perm.mul_apply, fu,
      (F0 k' hk').2 hb0]
  have ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w)
      (letterK S SI kS (stAt (stepsAt n w S kS BP i) j)) (rpt w (mask w) (LR i) (h₀ + dh))) = k' := by
    rw [ept]
    exact (hR0.pt k' hk').2
  rw [ek, if_pos hk']
  have hPG : PRep n w _ ((tp n w TR (LR i) k')⁻¹ *
      (lp n w S kS (stAt (stepsAt n w S kS BP i) j) * tp n w TR (LR i) (h₀ + dh))) :=
    prep_pcomp hn (prep_pp (hp0 _ hk')).2 (prep_pcomp hn hσ (prep_pp (hp0 _ hc')).1)
  rw [e, inv_mul_cancel_left] at hPG
  exact sift_of_mem_PS hsz hP hb ht hq hfix 5 (i + 1) le_rfl (by omega) _ u hPG
    (PF.pcomp_shr _ _ hn (PF.w_pos hw)) hu

end CFSG.KS.Raw.Orb

end

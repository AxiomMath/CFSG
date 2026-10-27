module

public import CFSG.Certificates.Kernel.ONOutK3.NodeSound
public import Certificates.Data.Kernel.ONOutK3.F

public section

namespace CFSG.KS.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KS.Bfs3 CFSG.KS.BfsReplay
open CFSG.ComponentClassification.SolMax.ONOut

variable {G : Nat → Nat → Nat} {R : Nat → Nat} {UL UW : Nat → Nat} {FK : Nat}
  {TC : Nat → Nat}

theorem walk_succ (R : Nat → Nat) (d w j : Nat) :
    walk R (d + 1) w j = walk R d (w / 4) (posF (nrec R j) (w % 4)) := by
  change strictN (posF (nrec R j) (Nat.land w 3)) (fun j' => walk R d (Nat.shiftRight w 2) j') = _
  rw [sN, shr_eq, show Nat.land w 3 = w % 4 from land_mod w 2]

theorem gword_succ (G : Nat → Nat → Nat) (d w x : Nat) :
    gword G (d + 1) w x = gword G d (w / 4) (G (w % 4) x) := by
  change strictN (G (Nat.land w 3) x) (fun x' => gword G d (Nat.shiftRight w 2) x') = _
  rw [sN, shr_eq, show Nat.land w 3 = w % 4 from land_mod w 2]

@[expose] def LetsB : Nat → Nat → Bool
  | 0, _ => true
  | d + 1, w => decide (w % 4 < 3) && LetsB d (w / 4)

@[expose] def Lets (d w : Nat) : Prop := LetsB d w = true

theorem Lets.tail {d w : Nat} (h : Lets (d + 1) w) : Lets d (w / 4) ∧ w % 4 < 3 := by
  unfold Lets LetsB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.2, h.1⟩

theorem lets_zero (w : Nat) : Lets 0 w := rfl

theorem lets_append : ∀ (d w l : Nat), Lets d w → w < 4 ^ d → l < 3 → Lets (d + 1) (w + l * 4 ^ d)
  | 0, w, l, _, hw, hl => by
    have : w = 0 := by simpa using hw
    subst this
    unfold Lets LetsB LetsB
    simp
    omega
  | d + 1, w, l, h, hw, hl => by
    obtain ⟨h1, h2⟩ := h.tail
    have e1 : (w + l * 4 ^ (d + 1)) % 4 = w % 4 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    have e2 : (w + l * 4 ^ (d + 1)) / 4 = w / 4 + l * 4 ^ d := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (by decide)]
    have ih := lets_append d (w / 4) l h1 (by rw [Nat.pow_succ] at hw; omega) hl
    unfold Lets LetsB
    rw [e1, e2, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h2, ih⟩

theorem walk_map (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) :
    ∀ (d w : Nat), Lets d w → ∀ j < CNT,
      walk R d w j < CNT ∧ map3 (gword G d w) (Tn R j) = Tn R (walk R d w j)
  | 0, w, _, j, hj => ⟨hj, rfl⟩
  | d + 1, w, hw, j, hj => by
    obtain ⟨hw', hl⟩ := hw.tail
    obtain ⟨p1, p2, -⟩ := pos_spec hN hj hl
    obtain ⟨q1, q2⟩ := walk_map hN d (w / 4) hw' _ p1
    rw [walk_succ]
    refine ⟨q1, ?_⟩
    rw [← q2, ← p2]
    unfold map3 stepG
    simp only [gword_succ]
    rfl

theorem walk_append (R : Nat → Nat) :
    ∀ (d w l j : Nat), w < 4 ^ d → l < 4 →
      walk R (d + 1) (w + l * 4 ^ d) j = posF (nrec R (walk R d w j)) l
  | 0, w, l, j, hw, hl => by
    have : w = 0 := by simpa using hw
    subst this
    rw [walk_succ]
    simp [Nat.mod_eq_of_lt hl]
    rfl
  | d + 1, w, l, j, hw, hl => by
    have e1 : (w + l * 4 ^ (d + 1)) % 4 = w % 4 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_mod_self_right]
    have e2 : (w + l * 4 ^ (d + 1)) / 4 = w / 4 + l * 4 ^ d := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (by decide)]
    rw [walk_succ R (d + 1), e1, e2,
      walk_append R d (w / 4) l _ (by rw [Nat.pow_succ] at hw; omega) hl, walk_succ R d w j]

theorem wrd_lt (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) :
    ∀ k < CNT, wrdF (nrec R k) < 4 ^ depF (nrec R k) ∧ Lets (depF (nrec R k)) (wrdF (nrec R k)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      obtain ⟨-, -, -, -, a5, a6⟩ := (nodes_of hN hk).root rfl
      rw [a5, a6]
      exact ⟨by decide, lets_zero 0⟩
    · obtain ⟨t1, t2, -, t4, t5, -⟩ := (nodes_of hN hk).tree h0
      obtain ⟨i1, i2⟩ := ih _ t1 (by omega)
      have e : 2 ^ (2 * depF (nrec R (parF (nrec R k)))) = 4 ^ depF (nrec R (parF (nrec R k))) := by
        rw [Nat.pow_mul]
      rw [t4, t5, e]
      refine ⟨?_, lets_append _ _ _ i2 i1 t2⟩
      rw [Nat.pow_succ]
      have : labF (nrec R k) * 4 ^ depF (nrec R (parF (nrec R k))) ≤
          2 * 4 ^ depF (nrec R (parF (nrec R k))) := Nat.mul_le_mul_right _ (by omega)
      omega

theorem pathEval_map (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true) {A : Array (Array Nat)}
    {P L : Array Nat} (hA : ∀ l < 3, ∀ x < NP, A[l]![x]! = G l x)
    (hP : ∀ k < CNT, P[k]! = parF (nrec R k)) (hL : ∀ k < CNT, L[k]! = labF (nrec R k)) :
    ∀ k < CNT, ∀ j < CNT, map3 (pathEval A P L k) (Tn R j) = Tn R (walk R (depF (nrec R k))
      (wrdF (nrec R k)) j) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk j hj
    by_cases h0 : k = 0
    · subst h0
      obtain ⟨-, -, -, -, a5, -⟩ := (nodes_of hN hk).root rfl
      rw [a5]
      have pe0 : ∀ p, pathEval A P L 0 p = p := fun p => by
        rw [pathEval.eq_1, dif_neg (by omega)]
      unfold map3
      rw [pe0, pe0, pe0]
      rfl
    · obtain ⟨t1, t2, -, t4, t5, -⟩ := (nodes_of hN hk).tree h0
      have hq : parF (nrec R k) < CNT := Nat.lt_trans t1 hk
      have hpe : ∀ p, pathEval A P L k p = A[labF (nrec R k)]![pathEval A P L (parF (nrec R k)) p]! := by
        intro p
        rw [pathEval.eq_1, hP k hk, hL k hk, dif_pos ⟨Nat.pos_of_ne_zero h0, t1⟩]
      have ihq := ih _ t1 hq j hj
      obtain ⟨w1, w2⟩ := wrd_lt hN _ hq
      have hwq := walk_map hN _ _ w2 j hj
      obtain ⟨p1, p2, -⟩ := pos_spec hN hwq.1 t2
      have hlt := nodes_of hN hwq.1
      have c := ihq
      unfold map3 Tn at c
      simp only [Prod.mk.injEq] at c
      obtain ⟨c1, c2, c3⟩ := c
      have e : map3 (pathEval A P L k) (Tn R j) = stepG G (labF (nrec R k))
          (Tn R (walk R (depF (nrec R (parF (nrec R k)))) (wrdF (nrec R (parF (nrec R k)))) j)) := by
        unfold stepG map3 Tn
        rw [hpe, hpe, hpe, c1, c2, c3, hA _ t2 _ hlt.ltA, hA _ t2 _ hlt.ltB, hA _ t2 _ hlt.ltC]
      rw [e]
      rw [p2, t4, t5, show 2 ^ (2 * depF (nrec R (parF (nrec R k)))) =
        4 ^ depF (nrec R (parF (nrec R k))) by rw [Nat.pow_mul], walk_append R _ _ _ _ w1 (by omega)]

theorem sig_lt (hN : ∀ s < 315, sliceOK G R UL UW FK TC s = true)
    (hU : ∀ l < 3, Lets (UL l) (UW l)) : ∀ k < CNT, sigF (nrec R k) < CNT := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      rw [((nodes_of hN hk).root rfl).2.2.2.1]
      exact hk
    · obtain ⟨t1, t2, -, -, -, t6⟩ := (nodes_of hN hk).tree h0
      rw [t6]
      exact (walk_map hN _ _ (hU _ t2) _ (ih _ t1 (Nat.lt_trans t1 hk))).1

end CFSG.KS.ONK3

end

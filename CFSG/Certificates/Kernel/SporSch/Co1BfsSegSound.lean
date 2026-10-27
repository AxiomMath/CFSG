module

public import Certificates.Data.Kernel.SporSch.Co1BfsSeg
public import CFSG.Certificates.Kernel.SporSch.Co1MatLemmas

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

section Seg

variable {F : Nat → Nat → Nat} {P PAR LAB W : Nat → Nat} {ng cap : Nat}

theorem bfsRunK_succ_eq (fuel h c : Nat) :
    bfsRunK F P PAR LAB W ng cap (fuel + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsRunK F P PAR LAB W ng cap fuel (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else c := by
  show nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, bfsRunK F P PAR LAB W ng cap fuel (Nat.succ h) c'), c) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

theorem bfsSegK_succ_eq (k h c : Nat) :
    bfsSegK F P PAR LAB W ng cap (k + 1) h c =
      if h < c ∧ c < cap then
        (if bfsRowK F P PAR LAB W ng h ng 0 c = 0 then 0
         else bfsSegK F P PAR LAB W ng cap k (h + 1) (bfsRowK F P PAR LAB W ng h ng 0 c))
      else 0 := by
  show nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, bfsSegK F P PAR LAB W ng cap k (Nat.succ h) c'),
        nat_lit 0) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]

theorem bfsRowK_succ_eq (h k l c : Nat) :
    bfsRowK F P PAR LAB W ng h (k + 1) l c =
      if W (h * ng + l) < c then
        (if P (W (h * ng + l)) = F (P h) l then bfsRowK F P PAR LAB W ng h k (l + 1) c else 0)
      else if W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l then
        bfsRowK F P PAR LAB W ng h k (l + 1) (c + 1)
      else 0 := by
  show strictN (W (Nat.add (Nat.mul h ng) l)) (fun w => strictN (F (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, bfsRowK F P PAR LAB W ng h k (Nat.succ l) c, nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          bfsRowK F P PAR LAB W ng h k (Nat.succ l) (Nat.succ c), nat_lit 0))) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.beq_eq, Bool.and_eq_true]
  rfl

theorem bfsRowK_wit (h : Nat) : ∀ k l c, bfsRowK F P PAR LAB W ng h k l c ≠ 0 →
    c ≤ bfsRowK F P PAR LAB W ng h k l c ∧ ∀ l', l ≤ l' → l' < l + k →
      W (h * ng + l') < bfsRowK F P PAR LAB W ng h k l c ∧
        P (W (h * ng + l')) = F (P h) l' := by
  intro k
  induction k with
  | zero => intro l c _; exact ⟨Nat.le_refl c, fun l' h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro l c hne
    rw [bfsRowK_succ_eq] at hne ⊢
    by_cases hw : W (h * ng + l) < c
    · by_cases hp : P (W (h * ng + l)) = F (P h) l
      · rw [if_pos hw, if_pos hp] at hne ⊢
        obtain ⟨hle, hall⟩ := ih _ _ hne
        refine ⟨hle, fun l' h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact ⟨Nat.lt_of_lt_of_le hw hle, hp⟩
        · exact hall l' h1 (by omega)
      · rw [if_pos hw, if_neg hp] at hne
        exact absurd rfl hne
    · by_cases hq : W (h * ng + l) = c ∧ P c = F (P h) l ∧ PAR c = h ∧ LAB c = l
      · rw [if_neg hw, if_pos hq] at hne ⊢
        obtain ⟨hle, hall⟩ := ih _ _ hne
        refine ⟨Nat.le_of_succ_le hle, fun l' h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · rw [hq.1]
          exact ⟨hle, hq.2.1⟩
        · exact hall l' h1 (by omega)
      · rw [if_neg hw, if_neg hq] at hne
        exact absurd rfl hne

theorem bfsSegK_wit : ∀ k h c, bfsSegK F P PAR LAB W ng cap k h c ≠ 0 →
    c ≤ bfsSegK F P PAR LAB W ng cap k h c ∧ ∀ h', h ≤ h' → h' < h + k → ∀ l < ng,
      W (h' * ng + l) < bfsSegK F P PAR LAB W ng cap k h c ∧
        P (W (h' * ng + l)) = F (P h') l := by
  intro k
  induction k with
  | zero => intro h c _; exact ⟨Nat.le_refl c, fun h' h1 h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro h c hne
    rw [bfsSegK_succ_eq] at hne ⊢
    by_cases hc : h < c ∧ c < cap
    · by_cases hr : bfsRowK F P PAR LAB W ng h ng 0 c = 0
      · simp only [hc, hr, and_self, ↓reduceIte] at hne
        exact absurd rfl hne
      · simp only [hc, hr, and_self, ↓reduceIte] at hne ⊢
        obtain ⟨hle, hall⟩ := ih _ _ hne
        obtain ⟨hle0, hrow⟩ := bfsRowK_wit h ng 0 c hr
        refine ⟨Nat.le_trans hle0 hle, fun h' h1 h2 l hl => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · obtain ⟨a, b⟩ := hrow l (Nat.zero_le l) (by omega)
          exact ⟨Nat.lt_of_lt_of_le a hle, b⟩
        · exact hall h' h1 (by omega) l hl
    · simp only [hc, ↓reduceIte] at hne
      exact absurd rfl hne

theorem bfsRunK_of_seg (fuel : Nat) : ∀ k h c, bfsSegK F P PAR LAB W ng cap k h c ≠ 0 →
    bfsRunK F P PAR LAB W ng cap (k + fuel) h c =
      bfsRunK F P PAR LAB W ng cap fuel (h + k) (bfsSegK F P PAR LAB W ng cap k h c) := by
  intro k
  induction k with
  | zero => intro h c _; rw [Nat.zero_add, Nat.add_zero]; rfl
  | succ k ih =>
    intro h c hne
    rw [bfsSegK_succ_eq] at hne ⊢
    rw [show k + 1 + fuel = (k + fuel) + 1 by omega, bfsRunK_succ_eq]
    by_cases hc : h < c ∧ c < cap
    · by_cases hr : bfsRowK F P PAR LAB W ng h ng 0 c = 0
      · simp only [hc, hr, and_self, ↓reduceIte] at hne
        exact absurd rfl hne
      · simp only [hc, hr, and_self, ↓reduceIte] at hne ⊢
        rw [ih _ _ hne, show h + 1 + k = h + (k + 1) by omega]
    · simp only [hc, ↓reduceIte] at hne
      exact absurd rfl hne

end Seg

theorem cBsK_pos (PAR : Nat → Nat) (h : Nat) :
    ∀ fuel lo hi, 0 < lo → 0 < cBsK PAR h fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo _ hlo; exact hlo
  | succ fuel ih =>
    intro lo hi hlo
    show 0 < nIf(Nat.blt lo hi, strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) fun m =>
        nIf(Nat.blt (PAR m) h, cBsK PAR h fuel (Nat.succ m) hi, cBsK PAR h fuel lo m), lo)
    simp only [MatL.strictN_eq, MatL.nIf_eq]
    split
    · split
      · exact ih _ _ (Nat.succ_pos _)
      · exact ih _ _ hlo
    · exact hlo

theorem gtPinK_of_seg {GM : Nat → Nat} {ng cap N : Nat} {P PAR LAB W S : Nat → Nat} {K m : Nat}
    (hh : gtHeadK P PAR LAB N K m = true)
    (hs : ∀ i < m, gtSegK GM ng cap N P PAR LAB W S K i = true) :
    gtPinK GM ng cap N P PAR LAB W S = true := by
  unfold gtHeadK at hh
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hh
  obtain ⟨hN, hP0, hpar0, hlab0, hc0, hcN, hmK⟩ := hh
  change m * K = N at hmK
  have hseg : ∀ i < m,
      bfsSegK (gtStepK GM) P PAR LAB W ng cap K (i * K) (cAtK PAR N (i * K)) =
        cAtK PAR N (i * K + K) ∧
      ∀ l < K, distAtK P S N (i * K + l) = true := by
    intro i hi
    have h := hs i hi
    unfold gtSegK at h
    rw [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, MatL.allBlk_eq,
      List.all_eq_true] at h
    exact ⟨h.1, fun l hl => h.2 l (List.mem_range.2 hl)⟩
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0, Nat.mul_zero] at hmK; omega
    · exact h0
  have hpos : ∀ j, cAtK PAR N (j * K + K) ≠ 0 := fun j =>
    Nat.pos_iff_ne_zero.1 (cBsK_pos PAR _ _ _ _ Nat.one_pos)
  have hcle : ∀ d j, j + d = m → cAtK PAR N (j * K) ≤ N := by
    intro d
    induction d with
    | zero => intro j hj; rw [Nat.add_zero] at hj; rw [hj, hmK, hcN]
    | succ d ih =>
      intro j hj
      obtain ⟨e, -⟩ := hseg j (by omega)
      have hne : bfsSegK (gtStepK GM) P PAR LAB W ng cap K (j * K) (cAtK PAR N (j * K)) ≠ 0 := by
        rw [e]; exact hpos j
      have h1 := (bfsSegK_wit K (j * K) (cAtK PAR N (j * K)) hne).1
      rw [e] at h1
      exact Nat.le_trans h1 (by rw [← Nat.succ_mul]; exact ih (j + 1) (by omega))
  have hdiv : ∀ k < N, k / K < m ∧ k / K * K + k % K = k := fun k hk =>
    ⟨by rw [Nat.div_lt_iff_lt_mul hK, hmK]; exact hk, Nat.div_add_mod' k K⟩
  have hdist : ∀ k < N, distAtK P S N k = true := by
    intro k hk
    have := (hseg (k / K) (hdiv k hk).1).2 (k % K) (Nat.mod_lt _ hK)
    rwa [(hdiv k hk).2] at this
  have hclos : ∀ h < N, ∀ l < ng, W (h * ng + l) < N ∧
      P (W (h * ng + l)) = gtStepK GM (P h) l := by
    intro h hh l hl
    obtain ⟨hq, hk⟩ := hdiv h hh
    obtain ⟨e, -⟩ := hseg (h / K) hq
    have hne : bfsSegK (gtStepK GM) P PAR LAB W ng cap K (h / K * K)
        (cAtK PAR N (h / K * K)) ≠ 0 := by
      rw [e]; exact hpos (h / K)
    have hw := (bfsSegK_wit K _ _ hne).2 h (by omega)
      (by have := Nat.mod_lt h hK; omega) l hl
    rw [e] at hw
    refine ⟨Nat.lt_of_lt_of_le hw.1 ?_, hw.2⟩
    rw [← Nat.succ_mul]
    exact hcle (m - (h / K + 1)) _ (by omega)
  have hrun : ∀ j ≤ m, bfsRunK (gtStepK GM) P PAR LAB W ng cap (N + 1) 0 1 =
      bfsRunK (gtStepK GM) P PAR LAB W ng cap (N + 1 - j * K) (j * K) (cAtK PAR N (j * K)) := by
    intro j
    induction j with
    | zero => intro _; simp [hc0]
    | succ j ih =>
      intro hj
      rw [ih (by omega)]
      obtain ⟨e, -⟩ := hseg j (by omega)
      have hle : (j + 1) * K ≤ N := by rw [← hmK]; exact Nat.mul_le_mul_right K hj
      have hne : bfsSegK (gtStepK GM) P PAR LAB W ng cap K (j * K) (cAtK PAR N (j * K)) ≠ 0 := by
        rw [e]; exact hpos j
      have hf : N + 1 - j * K = K + (N + 1 - (j + 1) * K) := by
        rw [Nat.succ_mul] at hle ⊢; omega
      rw [hf, bfsRunK_of_seg _ _ _ _ hne, e, Nat.succ_mul]
  have htail : bfsRunK (gtStepK GM) P PAR LAB W ng cap (0 + 1) N N = N := by
    rw [bfsRunK_succ_eq, if_neg (fun h => Nat.lt_irrefl N h.1)]
  have hfin : bfsRunK (gtStepK GM) P PAR LAB W ng cap (N + 1) 0 1 = N := by
    rw [hrun m (Nat.le_refl m), hmK, hcN, show N + 1 - N = 0 + 1 by omega, htail]
  unfold gtPinK bfsK
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  refine ⟨⟨hN, hP0, hpar0, hlab0, ?_, hfin⟩, ?_⟩
  · change allN N (distAtK P S N) = true
    exact MatL.allN_iff.2 hdist
  · unfold gtClosK
    refine MatL.allN_iff.2 fun h hh => MatL.allN_iff.2 fun l hl => ?_
    obtain ⟨a, b⟩ := hclos h hh l hl
    simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
    exact ⟨a, b⟩

end CFSG.KS.SporSch.M24

end

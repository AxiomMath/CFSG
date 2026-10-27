module

public import CFSG.Certificates.Kernel.B433Alt.StLenKinds

public section

namespace CFSG.KC.B433Alt

open CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

theorem stL_sW (v : ℕ) (k : ℕ → WS) : sW v k = k v := by cases v <;> rfl

theorem stL_wsMk_eq {k f : ℕ} (J : ℕ) (hk : k < 256) (hf : f < 256) :
    wsMk k f J = k + 256 * f + 65536 * J := by
  show k ||| (f <<< 8) ||| (J <<< 16) = _
  rw [stL_lor_shiftLeft (by norm_num; omega : k < 2 ^ 8),
    stL_lor_shiftLeft (by norm_num; omega : k + 2 ^ 8 * f < 2 ^ 16)]
  norm_num

theorem stL_wsK_eq (s : ℕ) : wsK s = s % 256 := by
  show s &&& 255 = _
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem stL_wsFail_eq (s : ℕ) : wsFail s = s / 256 % 2 := by
  rw [show wsFail s = fld s 8 (2 ^ 1 - 1) from rfl, stL_fld_eq]
  norm_num

theorem stL_wsJ_eq (s : ℕ) : wsJ s = s / 65536 := by
  show s >>> 16 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem stL_wsFail_lt (s : ℕ) : wsFail s < 2 := by
  rw [stL_wsFail_eq]; exact Nat.mod_lt _ (by norm_num)

theorem stL_wsK_wsMk {k f : ℕ} (J : ℕ) (hk : k < 256) (hf : f < 256) : wsK (wsMk k f J) = k := by
  rw [stL_wsK_eq, stL_wsMk_eq J hk hf]; omega

theorem stL_wsFail_wsMk {k f : ℕ} (J : ℕ) (hk : k < 256) (hf : f < 2) :
    wsFail (wsMk k f J) = f := by
  rw [stL_wsFail_eq, stL_wsMk_eq J hk (by omega)]; omega

theorem stL_wsJ_wsMk {k f : ℕ} (J : ℕ) (hk : k < 256) (hf : f < 2) : wsJ (wsMk k f J) = J := by
  rw [stL_wsJ_eq, stL_wsMk_eq J hk (by omega)]; omega

theorem stL_wsK_lt (s : ℕ) : wsK s < 256 := by
  rw [stL_wsK_eq]; exact Nat.mod_lt _ (by norm_num)

theorem stL_dN2_lt (d : ℕ) : dN2 d < 256 := by
  rw [show dN2 d = fld d 12 (2 ^ 8 - 1) from rfl, stL_fld_eq]; exact Nat.mod_lt _ (by norm_num)

section
variable {G : Type*} [Group G]

@[expose] noncomputable def stL_E (x : ℕ → G) (u : G) (pos : ℕ) : G :=
  if pos % 2 = 0 then x 7 else u

theorem stL_E_mul_self {x : ℕ → G} {u : G} (hx : ∀ c, x c * x c = 1) (hu : u * u = 1) (pos : ℕ) :
    stL_E x u pos * stL_E x u pos = 1 := by
  unfold stL_E; split_ifs
  · exact hx 7
  · exact hu

theorem stL_rel8 {x : ℕ → G} {u : G} (h47 : (x 7 * u) ^ 4 = 1) :
    evalWord (stL_E x u) (List.range 8) = 1 := by
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, stL_E]
  norm_num
  rw [← h47]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem stL_rel_gap {x : ℕ → G} {u : G} (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (h47 : (x 7 * u) ^ 4 = 1) {f : ℕ} (hf : f ≤ 7) :
    evalWord (stL_E x u) (List.range f) * stL_E x u f =
      evalWord (stL_E x u) (List.range' (f + 1) (7 - f)).reverse := by
  have e : List.range 8 = List.range f ++ [f] ++ List.range' (f + 1) (7 - f) := by
    interval_cases f <;> decide
  have h8 := stL_rel8 h47
  rw [e, stL_evalWord_append, stL_evalWord_append] at h8
  rw [stL_evalWord_reverse (stL_E_mul_self hx hu)]
  have h1 : evalWord (stL_E x u) [f] = stL_E x u f := by simp [evalWord]
  rw [h1] at h8
  exact eq_inv_of_mul_eq_one_left h8

end

section
variable {LP RD RW PW : ℕ → ℕ} {r : ℕ}

theorem stL_walkStep_fail {s : ℕ} (w pos : ℕ) (hs : wsFail s = 1) :
    walkStep LP RD RW PW r pos (s, w) = (s, w) := by
  show Bool.rec (motive := fun _ => WS) _ _ (Nat.beq (wsFail s) 1) = _
  rw [hs]
  rfl

theorem stL_walkStep_even {s pos : ℕ} (w : ℕ) (hs : wsFail s = 0) (hp : pos % 2 = 0) :
    walkStep LP RD RW PW r pos (s, w) = (s, wCat w (wOne 7)) := by
  show Bool.rec (motive := fun _ => WS) (Bool.rec (motive := fun _ => WS) _ _
    (Nat.beq (Nat.land pos 1) 0)) _ (Nat.beq (wsFail s) 1) = _
  rw [hs, show Nat.land pos 1 = pos % 2 from Nat.and_one_is_mod pos, hp]
  rfl

theorem stL_walkStep_odd {s pos : ℕ} (w : ℕ) (hs : wsFail s = 0) (hp : pos % 2 = 1) :
    walkStep LP RD RW PW r pos (s, w) =
      Bool.rec (motive := fun _ => WS) (wsMk (wsK s) 1 0, w)
        (wsMk (dN2 (RD (hNat (wsJ s) 20))) 0 (hAfterWord (hDrop (wsJ s) 20)),
          wCat (RW (hNat (wsJ s) 20)) (wTh (hWord (hDrop (wsJ s) 20))))
        (andB (Nat.blt (hNat (wsJ s) 20) r) (andB (isFact (dKind (RD (hNat (wsJ s) 20))))
          (andB (Nat.beq (dN1 (RD (hNat (wsJ s) 20))) (wsK s))
            (ptOK LP PW (dPt (RD (hNat (wsJ s) 20))) w (hWord (hDrop (wsJ s) 20)))))) := by
  show Bool.rec (motive := fun _ => WS) (Bool.rec (motive := fun _ => WS) _ _
    (Nat.beq (Nat.land pos 1) 0)) _ (Nat.beq (wsFail s) 1) = _
  rw [hs, show Nat.land pos 1 = pos % 2 from Nat.and_one_is_mod pos, hp]
  show sW _ _ = _
  rw [stL_sW, stL_sW, stL_sW, stL_sW]

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G}
  {u : G} {X : ℕ → G}

theorem stL_walkStep_spec (hy : stL_Hyp LP RD RW PW N H x u) {r : ℕ} (hr : r < N)
    (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) {s w pos : ℕ} (hs : wsFail s = 0)
    (hw : wInH w = true) (hwl : wLen w < 2 ^ 27)
    (hf : wsFail (walkStep LP RD RW PW r pos (s, w)).1 = 0) :
    wInH (walkStep LP RD RW PW r pos (s, w)).2 = true ∧
    wLen (walkStep LP RD RW PW r pos (s, w)).2 ≤ wLen w + 2 ^ 17 ∧
    stL_rc H (X (wsK s) * evalWord x (wList w) * stL_E x u pos)
      (X (wsK (walkStep LP RD RW PW r pos (s, w)).1) *
        evalWord x (wList (walkStep LP RD RW PW r pos (s, w)).2)) := by
  rcases Nat.mod_two_eq_zero_or_one pos with hp | hp
  · rw [stL_walkStep_even w hs hp] at hf ⊢
    have hl : wLen w + wLen (wOne 7) < 2 ^ 32 := by rw [stL_wLen_wOne]; omega
    refine ⟨stL_wInH_wCat hl hw (stL_wInH_wOne (by norm_num)), by
      rw [stL_wLen_wCat hl, stL_wLen_wOne]; omega, ?_⟩
    rw [stL_val_wCat x hl (stL_wOK_of_wInH hw), stL_val_wOne x (by norm_num), stL_E, if_pos hp]
    exact stL_rc_congr (stL_rc_refl _) (by group) rfl
  · rw [stL_walkStep_odd w hs hp] at hf ⊢
    generalize hF : hNat (wsJ s) 20 = f at hf ⊢
    generalize hTW : hWord (hDrop (wsJ s) 20) = tw at hf ⊢
    cases hc : andB (Nat.blt f r) (andB (isFact (dKind (RD f))) (andB (Nat.beq (dN1 (RD f)) (wsK s))
        (ptOK LP PW (dPt (RD f)) w tw))) with
    | false =>
      rw [hc] at hf
      rw [show wsFail (wsMk (wsK s) 1 0) = 1 from stL_wsFail_wsMk 0 (stL_wsK_lt s) (by norm_num)]
        at hf
      exact absurd hf (by norm_num)
    | true =>
      simp only [stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨hfr, hfa, h1, hpt⟩ := hc
      have hfN : f < N := lt_trans hfr hr
      have htl : wLen tw < 2 ^ 16 := hTW ▸ stL_wLen_hWord _
      obtain ⟨hT, e1⟩ := stL_ptOK hy hw (by omega) htl hpt
      have hl : wLen (RW f) + wLen (wTh tw) < 2 ^ 32 := by
        rw [stL_wLen_wTh]; have := hy.rwLen f hfN; omega
      refine ⟨stL_wInH_wCat hl (hy.rwH f hfN) (stL_wInH_wTh hT), by
        rw [stL_wLen_wCat hl, stL_wLen_wTh]; have := hy.rwLen f hfN; omega, ?_⟩
      show stL_rc H (X (wsK s) * evalWord x (wList w) * stL_E x u pos)
        (X (wsK (wsMk (dN2 (RD f)) 0 (hAfterWord (hDrop (wsJ s) 20)))) *
          evalWord x (wList (wCat (RW f) (wTh tw))))
      rw [stL_wsK_wsMk _ (stL_dN2_lt _) (by norm_num), stL_val_wCat x hl (stL_wOK_of_wInH
        (hy.rwH f hfN)), stL_val_wTh hy.uu hy.θ hT, stL_E, if_neg (by omega), e1]
      have hff := (ih f hfr).1 hfa
      rw [h1] at hff
      exact stL_rc_congr (stL_rc_ustep hy.uu (evalWord x (wList tw)) hff) (by group) (by group)

private noncomputable def runLoop (LP RD RW PW : ℕ → ℕ) (r a n : ℕ) (down : Bool) (m : ℕ) :
    WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (walkStep LP RD RW PW r
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) down)
          (Prod.mk s' x'))))) st)
    m

@[expose] def stL_posF (a n : ℕ) (down : Bool) (j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => Nat) (a + (n - 1 - j)) (a - (n - 1 - j)) down

private theorem runLoop_succ' (r a n : ℕ) (down : Bool) (m s w : ℕ) :
    runLoop LP RD RW PW r a n down (m + 1) (s, w) =
      sW s (fun s' => sW w (fun x' => runLoop LP RD RW PW r a n down m
        (walkStep LP RD RW PW r (stL_posF a n down m) (s', x')))) := rfl

private theorem runLoop_succ (r a n : ℕ) (down : Bool) (m s w : ℕ) :
    runLoop LP RD RW PW r a n down (m + 1) (s, w) =
      runLoop LP RD RW PW r a n down m (walkStep LP RD RW PW r (stL_posF a n down m) (s, w)) := by
  rw [runLoop_succ', stL_sW, stL_sW]

private theorem runLoop_zero (r a n : ℕ) (down : Bool) (st : WS) :
    runLoop LP RD RW PW r a n down 0 st = st := rfl

private theorem runLoop_fail (r a n : ℕ) (down : Bool) :
    ∀ m s w, wsFail s = 1 → runLoop LP RD RW PW r a n down m (s, w) = (s, w)
  | 0, _, _, _ => rfl
  | m + 1, s, w, hs => by
    rw [runLoop_succ, stL_walkStep_fail w _ hs, runLoop_fail r a n down m s w hs]

private theorem runLoop_spec (hy : stL_Hyp LP RD RW PW N H x u) {r : ℕ} (hr : r < N)
    (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) (a n : ℕ) (down : Bool) :
    ∀ m s w, wsFail (runLoop LP RD RW PW r a n down m (s, w)).1 = 0 → wInH w = true →
      wLen w + 2 ^ 17 * m < 2 ^ 27 →
      wsFail s = 0 ∧ wInH (runLoop LP RD RW PW r a n down m (s, w)).2 = true ∧
      wLen (runLoop LP RD RW PW r a n down m (s, w)).2 ≤ wLen w + 2 ^ 17 * m ∧
      stL_rc H (X (wsK s) * evalWord x (wList w) *
          evalWord (stL_E x u) ((List.range m).reverse.map (stL_posF a n down)))
        (X (wsK (runLoop LP RD RW PW r a n down m (s, w)).1) *
          evalWord x (wList (runLoop LP RD RW PW r a n down m (s, w)).2)) := by
  intro m
  induction m with
  | zero =>
    intro s w hf hw _
    rw [runLoop_zero] at hf ⊢
    refine ⟨hf, hw, le_refl _, ?_⟩
    simp only [List.range_zero, List.reverse_nil, List.map_nil, evalWord_nil, mul_one]
    exact stL_rc_refl _
  | succ m ihm =>
    intro s w hf hw hl
    have hs : wsFail s = 0 := by
      rcases (by have := stL_wsFail_lt s; omega : wsFail s = 0 ∨ wsFail s = 1) with h | h
      · exact h
      · rw [runLoop_fail r a n down _ s w h] at hf; rw [hf] at h; exact absurd h (by norm_num)
    rw [runLoop_succ] at hf ⊢
    generalize hst : walkStep LP RD RW PW r (stL_posF a n down m) (s, w) = st at hf ⊢
    obtain ⟨s1, w1⟩ := st
    have hf1 : wsFail s1 = 0 := by
      rcases (by have := stL_wsFail_lt s1; omega : wsFail s1 = 0 ∨ wsFail s1 = 1) with h | h
      · exact h
      · rw [runLoop_fail r a n down _ s1 w1 h] at hf; rw [hf] at h; exact absurd h (by norm_num)
    obtain ⟨hw1, hl1, hrc1⟩ := stL_walkStep_spec hy hr ih hs hw (by omega)
      (by rw [hst]; exact hf1)
    rw [hst] at hw1 hl1 hrc1
    obtain ⟨-, hw2, hl2, hrc2⟩ := ihm s1 w1 hf hw1 (by simp only at hl1; omega)
    refine ⟨hs, hw2, by simp only at hl1; omega, ?_⟩
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, evalWord_cons, ← mul_assoc]
    exact stL_rc_trans (stL_rc_mul hrc1 _) hrc2

theorem stL_walkRun_spec (hy : stL_Hyp LP RD RW PW N H x u) {r : ℕ} (hr : r < N)
    (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) {a n : ℕ} {down : Bool} {s w : ℕ}
    (hf : wsFail (walkRun LP RD RW PW r a n down (s, w)).1 = 0) (hw : wInH w = true)
    (hl : wLen w + 2 ^ 17 * n < 2 ^ 27) :
    wsFail s = 0 ∧ wInH (walkRun LP RD RW PW r a n down (s, w)).2 = true ∧
      wLen (walkRun LP RD RW PW r a n down (s, w)).2 ≤ wLen w + 2 ^ 17 * n ∧
      stL_rc H (X (wsK s) * evalWord x (wList w) *
          evalWord (stL_E x u) ((List.range n).reverse.map (stL_posF a n down)))
        (X (wsK (walkRun LP RD RW PW r a n down (s, w)).1) *
          evalWord x (wList (walkRun LP RD RW PW r a n down (s, w)).2)) :=
  runLoop_spec hy hr ih a n down n s w hf hw hl

end

theorem stL_posF_fwd {f : ℕ} (hf : f ≤ 8) :
    (List.range f).reverse.map (stL_posF 0 f false) = List.range f := by
  interval_cases f <;> decide

theorem stL_posF_bwd {f : ℕ} (hf : f ≤ 7) :
    (List.range (7 - f)).reverse.map (stL_posF 7 (7 - f) true) =
      (List.range' (f + 1) (7 - f)).reverse := by
  interval_cases f <;> decide

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G}
  {u : G} {X : ℕ → G}

theorem stL_walk_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) (h : walkOK LP RD RW PW r (RD r) J = true) :
    stL_Sem H x u X RD RW PW r := by
  unfold walkOK at h
  rw [stL_sB, stL_sB, stL_sB, stL_sB] at h
  have hx0l : wLen (hWord J) < 2 ^ 16 := stL_wLen_hWord J
  generalize hx0 : hWord J = x0 at h hx0l
  generalize hJ1 : hAfterWord J = J1 at h
  have hi : Nat.land J1 255 < 256 := by
    rw [show Nat.land J1 255 = J1 % 2 ^ 8 from Nat.and_two_pow_sub_one_eq_mod J1 8]
    exact Nat.mod_lt _ (by norm_num)
  generalize hI : Nat.land J1 255 = i at h hi
  generalize hFa : dAux (RD r) = f at h
  generalize hW : walkRun LP RD RW PW r 0 f false (wsMk i 0 (J1 >>> 8), x0) = W at h
  obtain ⟨sf, xf⟩ := W
  simp only [stL_andB_eq_true, Nat.ble_eq, Nat.beq_eq] at h
  obtain ⟨hx0H, hf8, hsf, hbr⟩ := h
  have hfw := stL_walkRun_spec hy (X := X) hr ih (a := 0) (n := f) (down := false)
    (s := wsMk i 0 (J1 >>> 8)) (w := x0) (by rw [hW]; exact hsf) hx0H (by omega)
  rw [hW, stL_wsK_wsMk _ hi (by norm_num), stL_posF_fwd hf8] at hfw
  obtain ⟨-, hxfH, hxfl, hfwd⟩ := hfw
  simp only at hxfH hxfl hfwd
  by_cases h8 : f = 8
  ·
    subst h8
    rw [show notB (Nat.beq 8 8) = false from rfl] at hbr
    simp only [stL_andB_eq_true, Nat.beq_eq] at hbr
    obtain ⟨-, hbr⟩ := hbr
    rw [stL_rel8 hy.rel, mul_one] at hfwd
    cases hk : Nat.beq (wsK sf) i <;> rw [hk] at hbr <;>
      simp only [stL_andB_eq_true, Nat.beq_eq] at hbr
    · obtain ⟨hk12, -, hbr⟩ := hbr
      refine stL_Sem_coinc (by rw [hk12]; rfl) ?_
      cases hl : Nat.blt i (wsK sf) <;> rw [hl] at hbr <;>
        simp only [stL_andB_eq_true, Nat.beq_eq] at hbr
      · obtain ⟨h1, h2, hone⟩ := hbr
        rw [h1, h2, stL_isOne_rev3 hy hr hxfH (stL_wInH_rev hx0H) (by omega)
          (by rw [stL_wLen_wRev]; omega) hone, stL_val_wRev hy.xx]
        exact stL_rc_congr (stL_rc_mul hfwd (evalWord x (wList x0))⁻¹) (by group) (by group)
      · obtain ⟨h1, h2, hone⟩ := hbr
        rw [h1, h2, stL_isOne_rev3 hy hr hx0H (stL_wInH_rev hxfH) (by omega)
          (by rw [stL_wLen_wRev]; omega) hone, stL_val_wRev hy.xx]
        exact stL_rc_congr (stL_rc_mul (stL_rc_symm hfwd) (evalWord x (wList xf))⁻¹) (by group)
          (by group)
    · obtain ⟨hk11, h2, hone⟩ := hbr
      have hki : wsK sf = i := Nat.eq_of_beq_eq_true hk
      refine stL_Sem_stab (by rw [hk11]; rfl) ?_
      rw [h2, stL_isOne_rev3 hy hr hxfH (stL_wInH_rev hx0H) (by omega)
        (by rw [stL_wLen_wRev]; omega) hone, stL_val_wRev hy.xx]
      rw [hki] at hfwd
      exact stL_rc_congr (stL_rc_mul (stL_rc_symm hfwd) (evalWord x (wList x0))⁻¹) (by group)
        (by group)
  ·
    have hf7 : f ≤ 7 := by omega
    rw [show notB (Nat.beq f 8) = true by
      rw [stL_notB]; cases hb : Nat.beq f 8
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h8] at hbr
    generalize hWb : walkRun LP RD RW PW r 7 (7 - f) true (wsMk i 0 (wsJ sf), x0) = Wb at hbr
    obtain ⟨sb, xb⟩ := Wb
    simp only [stL_sB, stL_andB_eq_true, Nat.beq_eq] at hbr
    obtain ⟨hk5, hsb, hodd, -, h1, h2, hpt, hnew⟩ := hbr
    have hbw := stL_walkRun_spec hy (X := X) hr ih (a := 7) (n := 7 - f) (down := true)
      (s := wsMk i 0 (wsJ sf)) (w := x0) (by rw [hWb]; exact hsb) hx0H (by omega)
    rw [hWb, stL_wsK_wsMk _ hi (by norm_num), stL_posF_bwd hf7] at hbw
    obtain ⟨-, hxbH, hxbl, hbwd⟩ := hbw
    simp only at hxbH hxbl hbwd
    have hodd' : f % 2 = 1 := by
      have : Nat.land (f + 1) 1 = (f + 1) % 2 := Nat.and_one_is_mod (f + 1)
      rw [this] at hodd; omega
    have hgap := stL_rel_gap hy.xx hy.uu hy.rel hf7
    rw [stL_E, if_neg (by omega)] at hgap
    have htl : wLen (hWord (wsJ sb)) < 2 ^ 16 := stL_wLen_hWord _
    obtain ⟨hT, e1⟩ := stL_ptOK hy hxfH (by omega) htl hpt
    have e2 := stL_newOK hy hr hxbH (by omega) hT htl hnew
    refine stL_Sem_fact (by rw [hk5]; norm_num) ?_
    rw [h1, h2, e2]
    have hA : stL_rc H (X (wsK sf) * evalWord x (wList (PW (dPt (RD r)))) *
        evalWord x (wList (hWord (wsJ sb))) * u) (X (wsK sb) * evalWord x (wList xb)) := by
      refine stL_rc_trans (stL_rc_congr (stL_rc_mul (stL_rc_symm hfwd) u) (by rw [e1]; group) ?_)
        hbwd
      rw [← hgap]; group
    exact stL_rc_congr (stL_rc_uback hy.uu _ hA) rfl (by group)

end

end CFSG.KC.B433Alt

end

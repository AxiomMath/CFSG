module

public import CFSG.Certificates.Kernel.B433Alt.Sound
public import CFSG.Certificates.Kernel.B433Alt.StLenWalk

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

@[expose] noncomputable def trGen {G : Type*} [Group G] (x : ℕ → G) (u : G) (c : ℕ) : G :=
  if c < 10 then x c else u * x 7 * u

section
variable {G : Type*} [Group G]

structure TrHyp (LP RD RW PW : ℕ → ℕ) (N : ℕ) (H : Subgroup G) (x : ℕ → G) (u : G) (X : ℕ → G) :
    Prop where
  xx : ∀ c, x c * x c = 1
  uu : u * u = 1
  θ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15)
  one : ∀ w, wInH w = true → isOne LP w = true → evalWord x (wList w) = 1
  fact : ∀ r < N, isFact (dKind (RD r)) = true →
    stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r)) * evalWord x (wList (RW r)))
  stab : ∀ r < N, isStab (dKind (RD r)) = true →
    stL_rc H (X (dN2 (RD r)) * evalWord x (wList (RW r))) (X (dN2 (RD r)))
  rwH : ∀ r < N, wInH (RW r) = true
  pwH : ∀ p, wInH (PW p) = true

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

theorem tr_isOne3 (hy : TrHyp LP RD RW PW N H x u X) {a b c : ℕ} (ha : wInH a = true)
    (hb : wInH b = true) (hc : wInH c = true) (hla : wLen a < 2 ^ 28) (hlb : wLen b < 2 ^ 28)
    (hlc : wLen c < 2 ^ 28) (h : isOne LP (cat3 a b c) = true) :
    evalWord x (wList a) * evalWord x (wList b) * evalWord x (wList c) = 1 := by
  have hbc : wLen b + wLen c < 2 ^ 32 := by omega
  have habc : wLen a + wLen (wCat b c) < 2 ^ 32 := by rw [stL_wLen_wCat hbc]; omega
  have := hy.one _ (stL_wInH_wCat habc ha (stL_wInH_wCat hbc hb hc)) h
  rw [stL_val_wCat x habc (stL_wOK_of_wInH ha), stL_val_wCat x hbc (stL_wOK_of_wInH hb)] at this
  rw [mul_assoc]
  exact this

theorem tr_ptOK (hy : TrHyp LP RD RW PW N H x u X) {p w tw : ℕ} (hw : wInH w = true)
    (hwl : wLen w < 2 ^ 28) (htl : wLen tw < 2 ^ 16) (hpl : wLen (PW p) < 2 ^ 16)
    (h : ptOK LP PW p w tw = true) :
    wInT tw = true ∧
      evalWord x (wList w) = evalWord x (wList (PW p)) * evalWord x (wList tw) := by
  unfold ptOK at h
  obtain ⟨hT, h1⟩ := stL_andB_eq_true.1 h
  refine ⟨hT, ?_⟩
  have := tr_isOne3 hy (stL_wInH_rev (stL_wInH_of_wInT hT)) (stL_wInH_rev (hy.pwH p)) hw
    (by rw [stL_wLen_wRev]; omega) (by rw [stL_wLen_wRev]; omega) hwl h1
  rw [stL_val_wRev hy.xx, stL_val_wRev hy.xx] at this
  calc evalWord x (wList w) = evalWord x (wList (PW p)) * evalWord x (wList tw) *
        ((evalWord x (wList tw))⁻¹ * (evalWord x (wList (PW p)))⁻¹ * evalWord x (wList w)) := by
        group
    _ = _ := by rw [this, mul_one]

end

@[expose] noncomputable def tpLoop (RD RW : ℕ → ℕ) (i r m : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg => sN (RW g) (fun wg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (wCat (Nat.sub acc (nat_lit 1)) wg) (fun a =>
            ih (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (B4A.andB (Nat.blt g r) (B4A.andB (isStab (dKind dg))
            (B4A.andB (Nat.beq (dN2 dg) i) (Nat.blt (wLen wg) (nat_lit 65536)))))))))
    m

theorem tr_tpLoop_succ' (RD RW : ℕ → ℕ) (i r m L acc : ℕ) :
    tpLoop RD RW i r (m + 1) L acc =
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg => sN (RW g) (fun wg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (wCat (Nat.sub acc (nat_lit 1)) wg) (fun a =>
            tpLoop RD RW i r m (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (B4A.andB (Nat.blt g r) (B4A.andB (isStab (dKind dg))
            (B4A.andB (Nat.beq (dN2 dg) i) (Nat.blt (wLen wg) (nat_lit 65536)))))))) := rfl

theorem tr_tpLoop_succ (RD RW : ℕ → ℕ) (i r m L acc : ℕ) :
    tpLoop RD RW i r (m + 1) L acc =
      Bool.rec (motive := fun _ => Nat) 0
        (tpLoop RD RW i r m (L >>> 20) (wCat (acc - 1) (RW (L &&& ones 20)) + 1))
        (B4A.andB (Nat.blt (L &&& ones 20) r) (B4A.andB (isStab (dKind (RD (L &&& ones 20))))
          (B4A.andB (Nat.beq (dN2 (RD (L &&& ones 20))) i)
            (Nat.blt (wLen (RW (L &&& ones 20))) 65536)))) := by
  rw [tr_tpLoop_succ', stL_sN, stL_sN, stL_sN, stL_sN]
  rfl

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

theorem tr_tpLoop_spec (hy : TrHyp LP RD RW PW N H x u X) {i r : ℕ} (hr : r ≤ N) :
    ∀ m L acc, 0 < tpLoop RD RW i r m L acc → wInH (acc - 1) = true →
      wLen (acc - 1) + 2 ^ 16 * m < 2 ^ 28 →
      stL_rc H (X i * evalWord x (wList (acc - 1))) (X i) →
      wInH (tpLoop RD RW i r m L acc - 1) = true ∧
      wLen (tpLoop RD RW i r m L acc - 1) ≤ wLen (acc - 1) + 2 ^ 16 * m ∧
      stL_rc H (X i * evalWord x (wList (tpLoop RD RW i r m L acc - 1))) (X i) := by
  intro m
  induction m with
  | zero =>
    intro L acc _ hw _ hs
    refine ⟨hw, ?_, hs⟩
    change wLen (acc - 1) ≤ wLen (acc - 1) + 2 ^ 16 * 0
    omega
  | succ m ihm =>
    intro L acc hpos hw hl hs
    have e := tr_tpLoop_succ RD RW i r m L acc
    generalize L &&& ones 20 = g at e
    cases hc : B4A.andB (Nat.blt g r) (B4A.andB (isStab (dKind (RD g)))
        (B4A.andB (Nat.beq (dN2 (RD g)) i) (Nat.blt (wLen (RW g)) 65536))) with
    | false => rw [e, hc] at hpos; exact absurd hpos (lt_irrefl 0)
    | true =>
      rw [hc] at e
      simp only [stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨hg, hgs, hgi, hgl⟩ := hc
      have hgN : g < N := lt_of_lt_of_le hg hr
      have hgw := hy.rwH g hgN
      have hsg := hy.stab g hgN hgs
      rw [hgi] at hsg
      have hcat : wLen (acc - 1) + wLen (RW g) < 2 ^ 32 := by omega
      have e' : tpLoop RD RW i r (m + 1) L acc =
          tpLoop RD RW i r m (L >>> 20) (wCat (acc - 1) (RW g) + 1) := e
      rw [e'] at hpos ⊢
      have hrc : stL_rc H (X i * evalWord x (wList (wCat (acc - 1) (RW g)))) (X i) := by
        rw [stL_val_wCat x hcat (stL_wOK_of_wInH hw), ← mul_assoc]
        exact stL_rc_trans (stL_rc_mul hs _) hsg
      obtain ⟨h1, h2, h3⟩ := ihm (L >>> 20) (wCat (acc - 1) (RW g) + 1) hpos
        (by simpa using stL_wInH_wCat hcat hw hgw)
        (by simp only [Nat.add_sub_cancel]; rw [stL_wLen_wCat hcat]; omega)
        (by simpa using hrc)
      refine ⟨h1, ?_, h3⟩
      simp only [Nat.add_sub_cancel] at h2
      rw [stL_wLen_wCat hcat] at h2
      omega

theorem tr_trPath_spec (hy : TrHyp LP RD RW PW N H x u X) {i m L : ℕ} (hm : m < 256)
    (hpos : 0 < trPath RD RW i m L N) :
    wInH (trPath RD RW i m L N - 1) = true ∧ wLen (trPath RD RW i m L N - 1) < 2 ^ 24 ∧
      stL_rc H (X i * evalWord x (wList (trPath RD RW i m L N - 1))) (X i) := by
  have e : trPath RD RW i m L N = tpLoop RD RW i N m L 1 := rfl
  rw [e] at hpos ⊢
  have h0 : wInH (1 - 1) = true := by
    rw [stL_wInH_iff, Nat.sub_self, stL_wOK_iff, stL_wLen_zero, stL_wStr_eq]
    exact ⟨by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  obtain ⟨h1, h2, h3⟩ := tr_tpLoop_spec hy (le_refl N) m L 1 hpos h0
    (by rw [Nat.sub_self, stL_wLen_zero]; omega)
    (by rw [Nat.sub_self, stL_val_zero, mul_one]; exact stL_rc_refl _)
  refine ⟨h1, ?_, h3⟩
  rw [Nat.sub_self, stL_wLen_zero] at h2
  omega

end

section
variable {LP RD RW PW : ℕ → ℕ} {N : ℕ}

theorem tr_blt_true {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem tr_blt_false {a b : ℕ} (h : ¬a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at hb
    exact absurd hb h

theorem tr_brec_true (A B : WS) : Bool.rec (motive := fun _ => WS) A B true = B := rfl

theorem tr_fld255_lt (a o : ℕ) : fld a o 255 < 256 := by
  rw [show fld a o 255 = fld a o (2 ^ 8 - 1) from rfl, stL_fld_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem tr_trU_fail {s : ℕ} (v : ℕ) (hs : wsFail s = 1) : trU LP RD RW PW N (s, v) = (s, v) := by
  show Bool.rec (motive := fun _ => WS) _ _ (Nat.beq (wsFail s) 1) = _
  rw [hs]
  rfl

theorem tr_trU_eq {s v f m L J1 tw sw : ℕ} (hs : wsFail s = 0)
    (hf : hNat (wsJ s) (nat_lit 20) = f) (hm : fld (wsJ s) (nat_lit 20) (nat_lit 255) = m)
    (hL : fld (wsJ s) (nat_lit 28) (ones (Nat.mul (nat_lit 20) m)) = L)
    (hJ : hDrop (wsJ s) (Nat.add (nat_lit 28) (Nat.mul (nat_lit 20) m)) = J1)
    (ht : hWord J1 = tw) (hsw : trPath RD RW (wsK s) m L N = sw) :
    trU LP RD RW PW N (s, v) =
      Bool.rec (motive := fun _ => WS) (Prod.mk (wsMk (wsK s) (nat_lit 1) (nat_lit 0)) v)
        (Prod.mk (wsMk (dN2 (RD f)) (nat_lit 0) (hAfterWord J1)) (wCat (RW f) (wTh tw)))
        (B4A.andB (Nat.blt f N) (B4A.andB (isFact (dKind (RD f))) (B4A.andB (Nat.beq (dN1 (RD f)) (wsK s))
          (B4A.andB (Nat.blt (nat_lit 0) sw) (B4A.andB (Nat.blt (wLen (RW f)) (nat_lit 65536))
            (B4A.andB (Nat.blt (wLen (PW (dPt (RD f)))) (nat_lit 65536))
              (ptOK LP PW (dPt (RD f)) (wCat (Nat.sub sw (nat_lit 1)) v) tw))))))) := by
  subst hf hm hL hJ ht hsw
  show Bool.rec (motive := fun _ => WS) _ _ (Nat.beq (wsFail s) (nat_lit 1)) = _
  rw [hs]
  show sW _ _ = _
  rw [stL_sW, stL_sW, stL_sW, stL_sW, stL_sW, stL_sW, stL_sW, stL_sW]

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

theorem tr_trU_spec (hy : TrHyp LP RD RW PW N H x u X) {s v : ℕ} (hs : wsFail s = 0)
    (hv : wInH v = true) (hvl : wLen v < 2 ^ 25)
    (hf : wsFail (trU LP RD RW PW N (s, v)).1 = 0) :
    wInH (trU LP RD RW PW N (s, v)).2 = true ∧ wLen (trU LP RD RW PW N (s, v)).2 < 2 ^ 17 ∧
      stL_rc H (X (wsK s) * evalWord x (wList v) * u)
        (X (wsK (trU LP RD RW PW N (s, v)).1) * evalWord x (wList (trU LP RD RW PW N (s, v)).2)) := by
  obtain ⟨f, hF⟩ : ∃ f, hNat (wsJ s) (nat_lit 20) = f := ⟨_, rfl⟩
  obtain ⟨m, hM⟩ : ∃ m, fld (wsJ s) (nat_lit 20) (nat_lit 255) = m := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, fld (wsJ s) (nat_lit 28) (ones (Nat.mul (nat_lit 20) m)) = L := ⟨_, rfl⟩
  obtain ⟨J1, hJ⟩ : ∃ J1, hDrop (wsJ s) (Nat.add (nat_lit 28) (Nat.mul (nat_lit 20) m)) = J1 :=
    ⟨_, rfl⟩
  obtain ⟨tw, hT⟩ : ∃ tw, hWord J1 = tw := ⟨_, rfl⟩
  obtain ⟨sw, hSW⟩ : ∃ sw, trPath RD RW (wsK s) m L N = sw := ⟨_, rfl⟩
  have hm : m < 256 := by rw [← hM]; exact tr_fld255_lt _ _
  have htl : wLen tw < 2 ^ 16 := by rw [← hT]; exact stL_wLen_hWord _
  rw [tr_trU_eq (PW := PW) (LP := LP) (v := v) hs hF hM hL hJ hT hSW] at hf ⊢
  cases hc : B4A.andB (Nat.blt f N) (B4A.andB (isFact (dKind (RD f))) (B4A.andB (Nat.beq (dN1 (RD f)) (wsK s))
      (B4A.andB (Nat.blt (nat_lit 0) sw) (B4A.andB (Nat.blt (wLen (RW f)) (nat_lit 65536))
        (B4A.andB (Nat.blt (wLen (PW (dPt (RD f)))) (nat_lit 65536))
          (ptOK LP PW (dPt (RD f)) (wCat (Nat.sub sw (nat_lit 1)) v) tw)))))) with
  | false =>
    rw [hc] at hf
    rw [show wsFail (wsMk (wsK s) 1 0) = 1 from stL_wsFail_wsMk 0 (stL_wsK_lt s) (by norm_num)]
      at hf
    exact absurd hf (by norm_num)
  | true =>
    change wInH (wCat (RW f) (wTh tw)) = true ∧ wLen (wCat (RW f) (wTh tw)) < 2 ^ 17 ∧
      stL_rc H (X (wsK s) * evalWord x (wList v) * u)
        (X (wsK (wsMk (dN2 (RD f)) 0 (hAfterWord J1))) * evalWord x (wList (wCat (RW f) (wTh tw))))
    simp only [stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨hfN, hfa, h1, hsw0, hrl, hpl, hpt⟩ := hc
    have hrl' : wLen (RW f) < 2 ^ 16 := hrl
    have hpl' : wLen (PW (dPt (RD f))) < 2 ^ 16 := hpl
    have hpt' : ptOK LP PW (dPt (RD f)) (wCat (sw - 1) v) tw = true := hpt
    have hrH := hy.rwH f hfN
    obtain ⟨hp1, hp2, hp3⟩ := tr_trPath_spec hy (i := wsK s) (L := L) hm
      (by rw [hSW]; exact hsw0)
    rw [hSW] at hp1 hp2 hp3
    have hl1 : wLen (sw - 1) + wLen v < 2 ^ 32 := by omega
    obtain ⟨hTw, e1⟩ := tr_ptOK hy (stL_wInH_wCat hl1 hp1 hv) (by rw [stL_wLen_wCat hl1]; omega)
      htl hpl' hpt'
    rw [stL_val_wCat x hl1 (stL_wOK_of_wInH hp1)] at e1
    have hl2 : wLen (RW f) + wLen (wTh tw) < 2 ^ 32 := by rw [stL_wLen_wTh]; omega
    refine ⟨stL_wInH_wCat hl2 hrH (stL_wInH_wTh hTw), by
      rw [stL_wLen_wCat hl2, stL_wLen_wTh]; omega, ?_⟩
    rw [stL_wsK_wsMk _ (stL_dN2_lt _) (by norm_num), stL_val_wCat x hl2 (stL_wOK_of_wInH hrH),
      stL_val_wTh hy.uu hy.θ hTw]
    have hff := hy.fact f hfN hfa
    rw [h1] at hff
    have hA : stL_rc H (X (wsK s) * evalWord x (wList v) * u)
        (X (wsK s) * evalWord x (wList (PW (dPt (RD f)))) * evalWord x (wList tw) * u) := by
      refine stL_rc_congr (stL_rc_mul (stL_rc_symm hp3) (evalWord x (wList v) * u))
        (by group) ?_
      rw [show X (wsK s) * evalWord x (wList (sw - 1)) * (evalWord x (wList v) * u) =
        X (wsK s) * (evalWord x (wList (sw - 1)) * evalWord x (wList v)) * u by group, e1]
      group
    exact stL_rc_trans hA (stL_rc_congr (stL_rc_ustep hy.uu (evalWord x (wList tw)) hff) rfl
      (by group))

end

section
variable {LP RD RW PW : ℕ → ℕ} {N : ℕ}

theorem tr_trL_long {c s v : ℕ} (h : ¬wLen v < 2 ^ 24) :
    trL LP RD RW PW N c (s, v) = (wsMk (wsK s) 1 0, v) := by
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt (wLen v) 16777216) = _
  rw [tr_blt_false (a := wLen v) (b := 16777216) (by omega)]

theorem tr_trL_lt {c s v : ℕ} (h : wLen v < 2 ^ 24) (hc : c < 10) :
    trL LP RD RW PW N c (s, v) = (s, wCat v (wOne c)) := by
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt (wLen v) 16777216) = _
  rw [tr_blt_true (a := wLen v) (b := 16777216) (by omega)]
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt c 10) = _
  rw [tr_blt_true hc]

theorem tr_trL_big {c s v : ℕ} (h : wLen v < 2 ^ 24) (hc : 10 < c) :
    trL LP RD RW PW N c (s, v) = (wsMk (wsK s) 1 0, v) := by
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt (wLen v) 16777216) = _
  rw [tr_blt_true (a := wLen v) (b := 16777216) (by omega)]
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt c 10) = _
  rw [tr_blt_false (a := c) (b := 10) (by omega)]
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.beq c 10) = _
  have hb : Nat.beq c 10 = false := by
    cases hb : Nat.beq c 10
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  rw [hb]

theorem tr_trL_ten {s v s1 v1 : ℕ} (h : wLen v < 2 ^ 24)
    (h1 : trU LP RD RW PW N (s, v) = (s1, v1)) :
    trL LP RD RW PW N 10 (s, v) = trU LP RD RW PW N (s1, wCat v1 (wOne 7)) := by
  change Bool.rec (motive := fun _ => WS) _ _ (Nat.blt (wLen v) 16777216) = _
  rw [tr_blt_true (a := wLen v) (b := 16777216) (by omega)]
  change Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW (wCat x (wOne 7))
    (fun x' => trU LP RD RW PW N (s', x')))) (trU LP RD RW PW N (s, v)) = _
  rw [h1]
  change sW s1 (fun s' => sW (wCat v1 (wOne 7)) (fun x' => trU LP RD RW PW N (s', x'))) = _
  rw [stL_sW, stL_sW]

theorem tr_trL_fail {c s v : ℕ} (hs : wsFail s = 1) :
    wsFail (trL LP RD RW PW N c (s, v)).1 = 1 := by
  have hf1 : wsFail (wsMk (wsK s) 1 0) = 1 := stL_wsFail_wsMk 0 (stL_wsK_lt s) (by norm_num)
  by_cases hl : wLen v < 2 ^ 24
  · rcases lt_trichotomy c 10 with hc | rfl | hc
    · rw [tr_trL_lt hl hc]
      exact hs
    · rw [tr_trL_ten hl (tr_trU_fail v hs), tr_trU_fail _ hs]
      exact hs
    · rw [tr_trL_big hl hc]
      exact hf1
  · rw [tr_trL_long hl]
    exact hf1

theorem tr_trRun_cons (c : ℕ) (w : List ℕ) (s v : ℕ) :
    trRun LP RD RW PW N (c :: w) (s, v) = trRun LP RD RW PW N w (trL LP RD RW PW N c (s, v)) := by
  show sW s (fun s' => sW v (fun v' => trRun LP RD RW PW N w (trL LP RD RW PW N c (s', v')))) = _
  rw [stL_sW, stL_sW]

theorem tr_trRun_fail : ∀ (w : List ℕ) (s v : ℕ), wsFail s = 1 →
    wsFail (trRun LP RD RW PW N w (s, v)).1 = 1
  | [], _, _, hs => hs
  | c :: w, s, v, hs => by
    rw [tr_trRun_cons]
    obtain ⟨s1, v1, h1⟩ : ∃ s1 v1, trL LP RD RW PW N c (s, v) = (s1, v1) := ⟨_, _, rfl⟩
    have hs1 := tr_trL_fail (LP := LP) (RD := RD) (RW := RW) (PW := PW) (N := N) (c := c) (v := v) hs
    rw [h1] at hs1 ⊢
    exact tr_trRun_fail w s1 v1 hs1

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

theorem tr_fail01 (s : ℕ) : wsFail s = 0 ∨ wsFail s = 1 := by
  have := stL_wsFail_lt s
  omega

theorem tr_trL_spec (hy : TrHyp LP RD RW PW N H x u X) {c s v : ℕ} (hs : wsFail s = 0)
    (hv : wInH v = true) (hf : wsFail (trL LP RD RW PW N c (s, v)).1 = 0) :
    wInH (trL LP RD RW PW N c (s, v)).2 = true ∧ wLen (trL LP RD RW PW N c (s, v)).2 < 2 ^ 25 ∧
      stL_rc H (X (wsK s) * evalWord x (wList v) * trGen x u c)
        (X (wsK (trL LP RD RW PW N c (s, v)).1) *
          evalWord x (wList (trL LP RD RW PW N c (s, v)).2)) := by
  have hf1 : wsFail (wsMk (wsK s) 1 0) = 1 := stL_wsFail_wsMk 0 (stL_wsK_lt s) (by norm_num)
  by_cases hl : wLen v < 2 ^ 24
  · rcases lt_trichotomy c 10 with hc | rfl | hc
    · rw [tr_trL_lt hl hc]
      have hl' : wLen v + wLen (wOne c) < 2 ^ 32 := by rw [stL_wLen_wOne]; omega
      refine ⟨stL_wInH_wCat hl' hv (stL_wInH_wOne hc), by
        rw [stL_wLen_wCat hl', stL_wLen_wOne]; omega, ?_⟩
      rw [stL_val_wCat x hl' (stL_wOK_of_wInH hv), stL_val_wOne x (by omega), trGen, if_pos hc]
      exact stL_rc_congr (stL_rc_refl _) rfl (by group)
    · obtain ⟨s1, v1, h1⟩ : ∃ s1 v1, trU LP RD RW PW N (s, v) = (s1, v1) := ⟨_, _, rfl⟩
      rw [tr_trL_ten hl h1] at hf ⊢
      have hs1 : wsFail s1 = 0 := by
        rcases tr_fail01 s1 with h | h
        · exact h
        · rw [tr_trU_fail _ h] at hf
          rw [hf] at h
          exact absurd h (by norm_num)
      have hf0 : wsFail (trU LP RD RW PW N (s, v)).1 = 0 := by rw [h1]; exact hs1
      obtain ⟨hv1, hl1, hrc1⟩ := tr_trU_spec hy hs hv (by omega) hf0
      rw [h1] at hv1 hl1 hrc1
      dsimp only at hv1 hl1 hrc1
      have hl7 : wLen v1 + wLen (wOne 7) < 2 ^ 32 := by rw [stL_wLen_wOne]; omega
      obtain ⟨hv2, hl2, hrc2⟩ := tr_trU_spec hy hs1 (stL_wInH_wCat hl7 hv1 (stL_wInH_wOne (by norm_num)))
        (by rw [stL_wLen_wCat hl7, stL_wLen_wOne]; omega) hf
      refine ⟨hv2, by omega, ?_⟩
      rw [stL_val_wCat x hl7 (stL_wOK_of_wInH hv1), stL_val_wOne x (by norm_num)] at hrc2
      rw [trGen, if_neg (by norm_num)]
      exact stL_rc_trans (stL_rc_congr (stL_rc_mul hrc1 (x 7 * u)) (by group) (by group)) hrc2
    · rw [tr_trL_big hl hc] at hf
      rw [hf1] at hf
      exact absurd hf (by norm_num)
  · rw [tr_trL_long hl] at hf
    rw [hf1] at hf
    exact absurd hf (by norm_num)

theorem tr_trRun_spec (hy : TrHyp LP RD RW PW N H x u X) : ∀ (w : List ℕ) (s v : ℕ),
    wsFail s = 0 → wInH v = true → wLen v < 2 ^ 25 →
    wsFail (trRun LP RD RW PW N w (s, v)).1 = 0 →
    wInH (trRun LP RD RW PW N w (s, v)).2 = true ∧
      wLen (trRun LP RD RW PW N w (s, v)).2 < 2 ^ 25 ∧
      stL_rc H (X (wsK s) * evalWord x (wList v) * evalWord (trGen x u) w)
        (X (wsK (trRun LP RD RW PW N w (s, v)).1) *
          evalWord x (wList (trRun LP RD RW PW N w (s, v)).2))
  | [], _, _, _, hv, hl, _ => ⟨hv, hl, by rw [evalWord_nil, mul_one]; exact stL_rc_refl _⟩
  | c :: w, s, v, hs, hv, _, hf => by
    rw [tr_trRun_cons] at hf ⊢
    obtain ⟨s1, v1, h1⟩ : ∃ s1 v1, trL LP RD RW PW N c (s, v) = (s1, v1) := ⟨_, _, rfl⟩
    rw [h1] at hf ⊢
    have hs1 : wsFail s1 = 0 := by
      rcases tr_fail01 s1 with h | h
      · exact h
      · have := tr_trRun_fail (LP := LP) (RD := RD) (RW := RW) (PW := PW) (N := N) w s1 v1 h
        rw [hf] at this
        exact absurd this (by norm_num)
    have hf0 : wsFail (trL LP RD RW PW N c (s, v)).1 = 0 := by rw [h1]; exact hs1
    obtain ⟨hv1, hl1, hrc1⟩ := tr_trL_spec hy hs hv hf0
    rw [h1] at hv1 hl1 hrc1
    dsimp only at hv1 hl1 hrc1
    obtain ⟨hv2, hl2, hrc2⟩ := tr_trRun_spec hy w s1 v1 hs1 hv1 hl1 hf
    refine ⟨hv2, hl2, ?_⟩
    rw [evalWord_cons, ← mul_assoc]
    exact stL_rc_trans (stL_rc_mul hrc1 _) hrc2

end

theorem tr_sound {LP RD RW PW : ℕ → ℕ} {N : ℕ} {G : Type*} [Group G] (H : Subgroup G)
    (x : ℕ → G) (u : G) (X : ℕ → G)
    (hxH : ∀ c < 10, x c ∈ H) (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15))
    (hone : ∀ w, wInH w = true → isOne LP w = true → wVal x w = 1)
    (hfact : ∀ r < N, isFact (dKind (RD r)) = true →
      X (dN1 (RD r)) * wVal x (PW (dPt (RD r))) * u * (X (dN2 (RD r)) * wVal x (RW r))⁻¹ ∈ H)
    (hstab : ∀ r < N, isStab (dKind (RD r)) = true →
      X (dN2 (RD r)) * wVal x (RW r) * (X (dN2 (RD r)))⁻¹ ∈ H)
    (hrw : ∀ r < N, wInH (RW r) = true) (hpw : ∀ p, wInH (PW p) = true)
    {k₀ a₀ k₁ a₁ J : ℕ} {w : List ℕ} (h : trOK LP RD RW PW N k₀ a₀ w J k₁ a₁ = true) :
    X k₀ * wVal x a₀ * evalWord (trGen x u) w * (X k₁ * wVal x a₁)⁻¹ ∈ H := by
  have hy : TrHyp LP RD RW PW N H x u X := ⟨hx, hu, hθ, hone, hfact, hstab, hrw, hpw⟩
  unfold trOK at h
  simp only [stL_andB_eq_true, Nat.blt_eq] at h
  obtain ⟨hk0, ha0l, ha0, ha1l, ha1, h⟩ := h
  have hs0 : wsFail (wsMk k₀ 0 J) = 0 := stL_wsFail_wsMk J (by omega) (by norm_num)
  have hk : wsK (wsMk k₀ 0 J) = k₀ := stL_wsK_wsMk J (by omega) (by norm_num)
  obtain ⟨sf, vf, hR⟩ : ∃ sf vf, trRun LP RD RW PW N w (wsMk k₀ 0 J, a₀) = (sf, vf) := ⟨_, _, rfl⟩
  have hR' : trRun LP RD RW PW N w (wsMk k₀ (nat_lit 0) J, a₀) = (sf, vf) := hR
  rw [hR'] at h
  simp only [stL_sB, stL_andB_eq_true, Nat.beq_eq] at h
  obtain ⟨hf, hk1, -, hone1⟩ := h
  obtain ⟨hvf, hlf, hrc⟩ := tr_trRun_spec hy w _ _ hs0 ha0 (by omega) (by rw [hR]; exact hf)
  rw [hR] at hvf hlf hrc
  rw [hk] at hrc
  dsimp only at hvf hlf hrc
  rw [hk1] at hrc
  have hl : wLen (wRev a₁) + wLen vf < 2 ^ 32 := by rw [stL_wLen_wRev]; omega
  have e := hy.one _ (stL_wInH_wCat hl (stL_wInH_rev ha1) hvf) hone1
  rw [stL_val_wCat x hl (stL_wOK_wRev _), stL_val_wRev hx] at e
  rw [← (inv_mul_eq_one.1 e)] at hrc
  exact hrc

end CFSG.KC.B433Alt

end

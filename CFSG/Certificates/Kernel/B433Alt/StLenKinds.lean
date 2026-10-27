module

public import CFSG.Certificates.Kernel.B433Alt.StLenWords

public section

namespace CFSG.KC.B433Alt

open CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

section
variable {G : Type*} [Group G] (H : Subgroup G)

@[expose] def stL_rc (a b : G) : Prop := a * b⁻¹ ∈ H

variable {H}

theorem stL_rc_refl (a : G) : stL_rc H a a := by
  show a * a⁻¹ ∈ H
  rw [mul_inv_cancel]
  exact H.one_mem

theorem stL_rc_symm {a b : G} (h : stL_rc H a b) : stL_rc H b a := by
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem stL_rc_trans {a b c : G} (h1 : stL_rc H a b) (h2 : stL_rc H b c) : stL_rc H a c := by
  have := H.mul_mem h1 h2
  rwa [show a * b⁻¹ * (b * c⁻¹) = a * c⁻¹ by group] at this

theorem stL_rc_mul {a b : G} (h : stL_rc H a b) (c : G) : stL_rc H (a * c) (b * c) := by
  show a * c * (b * c)⁻¹ ∈ H
  rwa [show a * c * (b * c)⁻¹ = a * b⁻¹ by group]

theorem stL_rc_congr {a b a' b' : G} (h : stL_rc H a b) (ha : a = a') (hb : b = b') :
    stL_rc H a' b' := ha ▸ hb ▸ h

theorem stL_thinv {u : G} (hu : u * u = 1) (τ : G) : (u * τ * u)⁻¹ = u * τ⁻¹ * u := by
  rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hu, mul_assoc]

theorem stL_rc_ustep {u : G} (hu : u * u = 1) {A B : G} (τ : G) (h : stL_rc H (A * u) B) :
    stL_rc H (A * τ * u) (B * (u * τ * u)) :=
  stL_rc_congr (stL_rc_mul h (u * τ * u))
    (by rw [show A * u * (u * τ * u) = A * (u * u) * τ * u by group, hu, mul_one]) rfl

theorem stL_rc_uback {u : G} (hu : u * u = 1) {A B : G} (τ : G) (h : stL_rc H (A * τ * u) B) :
    stL_rc H (A * u) (B * (u * τ * u)⁻¹) :=
  stL_rc_congr (stL_rc_mul h (u * τ * u)⁻¹)
    (by rw [stL_thinv hu, show A * τ * u * (u * τ⁻¹ * u) = A * τ * (u * u) * τ⁻¹ * u by group, hu,
      mul_one, mul_inv_cancel_right]) rfl

theorem stL_solve3 {a b c : G} (h : a⁻¹ * b * c = 1) : a = b * c := by
  calc a = a * (a⁻¹ * b * c) := by rw [h, mul_one]
    _ = b * c := by group

end

section
variable {G : Type*} [Group G]

structure stL_Hyp (LP RD RW PW : ℕ → ℕ) (N : ℕ) (H : Subgroup G) (x : ℕ → G) (u : G) : Prop where
  rwLen : ∀ r < N, wLen (RW r) < 2 ^ 16
  rwH : ∀ r < N, wInH (RW r) = true
  tree0 : ∀ r < N, dKind (RD r) = 0 → RW r = 0
  pwLen : ∀ p, wLen (PW p) < 2 ^ 16
  pwH : ∀ p, wInH (PW p) = true
  xH : ∀ c < 10, x c ∈ H
  xx : ∀ c, x c * x c = 1
  uu : u * u = 1
  θ : ∀ c < 10, c ≠ 7 → u * x c * u = x (fld THM (4 * c) 15)
  rel : (x 7 * u) ^ 4 = 1
  one : ∀ w, wInH w = true → isOne LP w = true → evalWord x (wList w) = 1

variable (H : Subgroup G) (x : ℕ → G) (u : G) (X : ℕ → G) (RD RW PW : ℕ → ℕ)

@[expose] def stL_Sem (q : ℕ) : Prop :=
  (isFact (dKind (RD q)) = true →
    stL_rc H (X (dN1 (RD q)) * evalWord x (wList (PW (dPt (RD q)))) * u)
      (X (dN2 (RD q)) * evalWord x (wList (RW q)))) ∧
  (isStab (dKind (RD q)) = true →
    stL_rc H (X (dN2 (RD q)) * evalWord x (wList (RW q))) (X (dN2 (RD q)))) ∧
  (isCoinc (dKind (RD q)) = true →
    stL_rc H (X (dN2 (RD q))) (X (dN1 (RD q)) * evalWord x (wList (RW q))))

theorem stL_isFact_iff (k : ℕ) : isFact k = true ↔ k < 6 := by
  unfold isFact; simp

theorem stL_isStab_iff (k : ℕ) : isStab k = true ↔ k = 7 ∨ (8 ≤ k ∧ k ≤ 11) := by
  unfold isStab; rw [stL_orB, stL_andB]; simp

theorem stL_isCoinc_iff (k : ℕ) : isCoinc k = true ↔ k = 6 ∨ k = 12 := by
  unfold isCoinc; rw [stL_orB]; simp

variable {H x u X RD RW PW}

theorem stL_Sem_fact {q : ℕ} (hk : dKind (RD q) < 6)
    (h : stL_rc H (X (dN1 (RD q)) * evalWord x (wList (PW (dPt (RD q)))) * u)
      (X (dN2 (RD q)) * evalWord x (wList (RW q)))) : stL_Sem H x u X RD RW PW q := by
  refine ⟨fun _ => h, fun hs => ?_, fun hc => ?_⟩
  · rcases (stL_isStab_iff _).1 hs with h' | h' <;> omega
  · rcases (stL_isCoinc_iff _).1 hc with h' | h' <;> omega

theorem stL_Sem_stab {q : ℕ} (hk : isStab (dKind (RD q)) = true)
    (h : stL_rc H (X (dN2 (RD q)) * evalWord x (wList (RW q))) (X (dN2 (RD q)))) :
    stL_Sem H x u X RD RW PW q := by
  have hk' := (stL_isStab_iff _).1 hk
  refine ⟨fun hf => ?_, fun _ => h, fun hc => ?_⟩
  · have := (stL_isFact_iff _).1 hf; omega
  · rcases (stL_isCoinc_iff _).1 hc with h' | h' <;> omega

theorem stL_Sem_coinc {q : ℕ} (hk : isCoinc (dKind (RD q)) = true)
    (h : stL_rc H (X (dN2 (RD q))) (X (dN1 (RD q)) * evalWord x (wList (RW q)))) :
    stL_Sem H x u X RD RW PW q := by
  have hk' := (stL_isCoinc_iff _).1 hk
  refine ⟨fun hf => ?_, fun hs => ?_, fun _ => h⟩
  · have := (stL_isFact_iff _).1 hf; omega
  · rcases (stL_isStab_iff _).1 hs with h' | h' <;> omega

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}

theorem stL_isOne3 (hy : stL_Hyp LP RD RW PW N H x u) {a b c : ℕ} (ha : wInH a = true)
    (hb : wInH b = true) (hc : wInH c = true) (hla : wLen a < 2 ^ 28) (hlb : wLen b < 2 ^ 28)
    (hlc : wLen c < 2 ^ 28) (h : isOne LP (cat3 a b c) = true) :
    evalWord x (wList a) * evalWord x (wList b) * evalWord x (wList c) = 1 := by
  have hbc : wLen b + wLen c < 2 ^ 32 := by omega
  have habc : wLen a + wLen (wCat b c) < 2 ^ 32 := by rw [stL_wLen_wCat hbc]; omega
  have := hy.one _ (stL_wInH_wCat habc ha (stL_wInH_wCat hbc hb hc)) h
  rw [stL_val_wCat x habc (stL_wOK_of_wInH ha), stL_val_wCat x hbc (stL_wOK_of_wInH hb)] at this
  rw [mul_assoc]
  exact this

theorem stL_isOne4 (hy : stL_Hyp LP RD RW PW N H x u) {a b c e : ℕ} (ha : wInH a = true)
    (hb : wInH b = true) (hc : wInH c = true) (he : wInH e = true) (hla : wLen a < 2 ^ 28)
    (hlb : wLen b < 2 ^ 28) (hlc : wLen c < 2 ^ 28) (hle : wLen e < 2 ^ 28)
    (h : isOne LP (cat4 a b c e) = true) :
    evalWord x (wList a) * evalWord x (wList b) * evalWord x (wList c) * evalWord x (wList e) =
      1 := by
  have hce : wLen c + wLen e < 2 ^ 32 := by omega
  have hbce : wLen b + wLen (wCat c e) < 2 ^ 32 := by rw [stL_wLen_wCat hce]; omega
  have habce : wLen a + wLen (wCat b (wCat c e)) < 2 ^ 32 := by
    rw [stL_wLen_wCat hbce, stL_wLen_wCat hce]; omega
  have := hy.one _ (stL_wInH_wCat habce ha (stL_wInH_wCat hbce hb (stL_wInH_wCat hce hc he))) h
  rw [stL_val_wCat x habce (stL_wOK_of_wInH ha), stL_val_wCat x hbce (stL_wOK_of_wInH hb),
    stL_val_wCat x hce (stL_wOK_of_wInH hc)] at this
  rw [mul_assoc, mul_assoc]
  exact this

theorem stL_isOne2 (hy : stL_Hyp LP RD RW PW N H x u) {a b : ℕ} (ha : wInH a = true)
    (hb : wInH b = true) (hla : wLen a < 2 ^ 28) (hlb : wLen b < 2 ^ 28)
    (h : isOne LP (wCat a b) = true) : evalWord x (wList a) * evalWord x (wList b) = 1 := by
  have hab : wLen a + wLen b < 2 ^ 32 := by omega
  have := hy.one _ (stL_wInH_wCat hab ha hb) h
  rwa [stL_val_wCat x hab (stL_wOK_of_wInH ha)] at this

theorem stL_wInH_rev {w : ℕ} (h : wInH w = true) : wInH (wRev w) = true :=
  stL_wInH_wRev (stL_wAt_lt_of_wInH h)

theorem stL_isOne_rev3 (hy : stL_Hyp LP RD RW PW N H x u) {r b c : ℕ} (hr : r < N)
    (hb : wInH b = true) (hc : wInH c = true) (hlb : wLen b < 2 ^ 28) (hlc : wLen c < 2 ^ 28)
    (h : isOne LP (cat3 (wRev (RW r)) b c) = true) :
    evalWord x (wList (RW r)) = evalWord x (wList b) * evalWord x (wList c) := by
  have := stL_isOne3 hy (stL_wInH_rev (hy.rwH r hr)) hb hc
    (by rw [stL_wLen_wRev]; have := hy.rwLen r hr; omega) hlb hlc h
  rw [stL_val_wRev hy.xx] at this
  exact stL_solve3 this

theorem stL_ptOK (hy : stL_Hyp LP RD RW PW N H x u) {p w tw : ℕ} (hw : wInH w = true)
    (hwl : wLen w < 2 ^ 28) (htl : wLen tw < 2 ^ 16) (h : ptOK LP PW p w tw = true) :
    wInT tw = true ∧
      evalWord x (wList w) = evalWord x (wList (PW p)) * evalWord x (wList tw) := by
  unfold ptOK at h
  obtain ⟨hT, h1⟩ := stL_andB_eq_true.1 h
  refine ⟨hT, ?_⟩
  have := stL_isOne3 hy (stL_wInH_rev (stL_wInH_of_wInT hT)) (stL_wInH_rev (hy.pwH p)) hw
    (by rw [stL_wLen_wRev]; omega) (by rw [stL_wLen_wRev]; have := hy.pwLen p; omega) hwl h1
  rw [stL_val_wRev hy.xx, stL_val_wRev hy.xx] at this
  calc evalWord x (wList w) = evalWord x (wList (PW p)) * evalWord x (wList tw) *
        ((evalWord x (wList tw))⁻¹ * (evalWord x (wList (PW p)))⁻¹ * evalWord x (wList w)) := by
        group
    _ = _ := by rw [this, mul_one]

theorem stL_newOK (hy : stL_Hyp LP RD RW PW N H x u) {r w tw : ℕ} (hr : r < N)
    (hw : wInH w = true) (hwl : wLen w < 2 ^ 28) (hT : wInT tw = true) (htl : wLen tw < 2 ^ 16)
    (h : newOK LP RW r w tw = true) :
    evalWord x (wList (RW r)) = evalWord x (wList w) * (u * evalWord x (wList tw) * u)⁻¹ := by
  unfold newOK at h
  rw [stL_isOne_rev3 hy hr hw (stL_wInH_rev (stL_wInH_wTh hT)) hwl
    (by rw [stL_wLen_wRev, stL_wLen_wTh]; omega) h, stL_val_wRev hy.xx,
    stL_val_wTh hy.uu hy.θ hT]

end

private noncomputable def pathLoop (RD RW : ℕ → ℕ) (i : ℕ) (inv : Bool) (r : ℕ) (m : ℕ) :
    ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (wRev (RW g)) (Nat.sub acc (nat_lit 1))) inv) (fun a =>
            ih (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) i)))))))
    m

private theorem pathLoop_succ (RD RW : ℕ → ℕ) (i : ℕ) (inv : Bool) (r m L acc : ℕ) :
    pathLoop RD RW i inv r (m + 1) L acc =
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (wRev (RW g)) (Nat.sub acc (nat_lit 1))) inv) (fun a =>
            pathLoop RD RW i inv r m (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) i)))))) := rfl

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

private theorem pathLoop_spec (hy : stL_Hyp LP RD RW PW N H x u) {i r : ℕ} (hr : r ≤ N)
    (inv : Bool)
    (ih : ∀ g < r, isStab (dKind (RD g)) = true →
      stL_rc H (X (dN2 (RD g)) * evalWord x (wList (RW g))) (X (dN2 (RD g)))) :
    ∀ m L acc, 0 < pathLoop RD RW i inv r m L acc → 0 < acc → wInH (acc - 1) = true →
      wLen (acc - 1) + 2 ^ 16 * m < 2 ^ 28 →
      stL_rc H (X i * evalWord x (wList (acc - 1))) (X i) →
      wInH (pathLoop RD RW i inv r m L acc - 1) = true ∧
      wLen (pathLoop RD RW i inv r m L acc - 1) ≤ wLen (acc - 1) + 2 ^ 16 * m ∧
      stL_rc H (X i * evalWord x (wList (pathLoop RD RW i inv r m L acc - 1))) (X i) := by
  intro m
  induction m with
  | zero => intro L acc _ _ hw _ hs; exact ⟨hw, by simp [pathLoop], hs⟩
  | succ m ihm =>
    intro L acc hpos hacc hw hl hs
    have e : pathLoop RD RW i inv r (m + 1) L acc =
        Bool.rec (motive := fun _ => Nat) 0
          (pathLoop RD RW i inv r m (L >>> 20)
            (Bool.rec (motive := fun _ => Nat) (wCat (acc - 1) (RW (L &&& ones 20)))
              (wCat (wRev (RW (L &&& ones 20))) (acc - 1)) inv + 1))
          (andB (Nat.blt 0 acc) (andB (Nat.blt (L &&& ones 20) r)
            (andB (isStab (dKind (RD (L &&& ones 20))))
              (Nat.beq (dN2 (RD (L &&& ones 20))) i)))) := by
      rw [pathLoop_succ, stL_sN, stL_sN, stL_sN]
      rfl
    generalize L &&& ones 20 = g at e
    cases hc : andB (Nat.blt 0 acc) (andB (Nat.blt g r)
        (andB (isStab (dKind (RD g))) (Nat.beq (dN2 (RD g)) i))) with
    | false => rw [e, hc] at hpos; exact absurd hpos (lt_irrefl 0)
    | true =>
      rw [hc] at e
      simp only [stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at hc
      obtain ⟨-, hg, hgs, hgi⟩ := hc
      have hgN : g < N := lt_of_lt_of_le hg hr
      have hgw := hy.rwH g hgN
      have hgl := hy.rwLen g hgN
      have hsg := ih g hg hgs
      rw [hgi] at hsg
      have hcat : wLen (acc - 1) + wLen (RW g) < 2 ^ 32 := by omega
      have hcat' : wLen (wRev (RW g)) + wLen (acc - 1) < 2 ^ 32 := by
        rw [stL_wLen_wRev]; omega
      set a := Bool.rec (motive := fun _ => Nat) (wCat (acc - 1) (RW g))
        (wCat (wRev (RW g)) (acc - 1)) inv with ha
      have haw : wInH a = true ∧ wLen a = wLen (acc - 1) + wLen (RW g) ∧
          stL_rc H (X i * evalWord x (wList a)) (X i) := by
        cases inv with
        | false =>
          refine ⟨stL_wInH_wCat hcat hw hgw, stL_wLen_wCat hcat, ?_⟩
          show stL_rc H (X i * evalWord x (wList (wCat (acc - 1) (RW g)))) (X i)
          rw [stL_val_wCat x hcat (stL_wOK_of_wInH hw), ← mul_assoc]
          exact stL_rc_trans (stL_rc_mul hs _) hsg
        | true =>
          have hl2 : wLen (wCat (wRev (RW g)) (acc - 1)) = wLen (acc - 1) + wLen (RW g) := by
            rw [stL_wLen_wCat hcat', stL_wLen_wRev]; omega
          refine ⟨stL_wInH_wCat hcat' (stL_wInH_rev hgw) hw, hl2, ?_⟩
          show stL_rc H (X i * evalWord x (wList (wCat (wRev (RW g)) (acc - 1)))) (X i)
          rw [stL_val_wCat x hcat' (stL_wOK_wRev _), stL_val_wRev hy.xx, ← mul_assoc]
          have h1 : stL_rc H (X i * (evalWord x (wList (RW g)))⁻¹) (X i) :=
            stL_rc_symm (stL_rc_congr (stL_rc_mul hsg (evalWord x (wList (RW g)))⁻¹)
              (by group) rfl)
          exact stL_rc_trans (stL_rc_congr (stL_rc_mul h1 (evalWord x (wList (acc - 1))))
            rfl rfl) hs
      have e' : pathLoop RD RW i inv r (m + 1) L acc =
          pathLoop RD RW i inv r m (L >>> 20) (a + 1) := e
      rw [e'] at hpos ⊢
      obtain ⟨h1, h2, h3⟩ := ihm (L >>> 20) (a + 1) hpos (Nat.succ_pos _)
        (by simpa using haw.1) (by simp only [Nat.add_sub_cancel]; rw [haw.2.1]; omega)
        (by simpa using haw.2.2)
      refine ⟨h1, ?_, h3⟩
      simp only [Nat.add_sub_cancel] at h2
      rw [haw.2.1] at h2
      omega

theorem stL_pathW (hy : stL_Hyp LP RD RW PW N H x u) {i m L r : ℕ} {inv : Bool} (hr : r ≤ N)
    (hm : m ≤ 255)
    (ih : ∀ g < r, isStab (dKind (RD g)) = true →
      stL_rc H (X (dN2 (RD g)) * evalWord x (wList (RW g))) (X (dN2 (RD g))))
    (hpos : 0 < pathW RD RW i m L inv r) :
    wInH (pathW RD RW i m L inv r - 1) = true ∧ wLen (pathW RD RW i m L inv r - 1) < 2 ^ 24 ∧
      stL_rc H (X i * evalWord x (wList (pathW RD RW i m L inv r - 1))) (X i) := by
  have e : pathW RD RW i m L inv r = pathLoop RD RW i inv r m L 1 := rfl
  rw [e] at hpos ⊢
  have h0 : wInH (1 - 1) = true := by
    rw [stL_wInH_iff, Nat.sub_self, stL_wOK_iff, stL_wLen_zero, stL_wStr_eq]
    exact ⟨by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  obtain ⟨h1, h2, h3⟩ := pathLoop_spec hy hr inv ih m L 1 hpos one_pos h0
    (by rw [Nat.sub_self, stL_wLen_zero]; omega)
    (by rw [Nat.sub_self, stL_val_zero, mul_one]; exact stL_rc_refl _)
  refine ⟨h1, ?_, h3⟩
  rw [Nat.sub_self, stL_wLen_zero] at h2
  omega

end

section
variable {G : Type*} [Group G] {LP RD RW PW : ℕ → ℕ} {N : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}
  {X : ℕ → G}

theorem stL_rc_stab_mul {A a b : G} (ha : stL_rc H (A * a) A) (hb : stL_rc H (A * b) A) :
    stL_rc H (A * (a * b)) A :=
  stL_rc_trans (stL_rc_congr (stL_rc_mul ha b) (by group) rfl) hb

theorem stL_isOne_rev4 (hy : stL_Hyp LP RD RW PW N H x u) {r b c e : ℕ} (hr : r < N)
    (hb : wInH b = true) (hc : wInH c = true) (he : wInH e = true) (hlb : wLen b < 2 ^ 28)
    (hlc : wLen c < 2 ^ 28) (hle : wLen e < 2 ^ 28)
    (h : isOne LP (cat4 (wRev (RW r)) b c e) = true) :
    evalWord x (wList (RW r)) =
      evalWord x (wList b) * evalWord x (wList c) * evalWord x (wList e) := by
  have := stL_isOne4 hy (stL_wInH_rev (hy.rwH r hr)) hb hc he
    (by rw [stL_wLen_wRev]; have := hy.rwLen r hr; omega) hlb hlc hle h
  rw [stL_val_wRev hy.xx] at this
  calc evalWord x (wList (RW r)) = evalWord x (wList (RW r)) * ((evalWord x (wList (RW r)))⁻¹ *
        evalWord x (wList b) * evalWord x (wList c) * evalWord x (wList e)) := by rw [this, mul_one]
    _ = _ := by group

theorem stL_inv_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : invOK LP RD RW PW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r)) * evalWord x (wList (RW r))) := by
  unfold invOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hfa, h1, h2, hpt, hnew⟩ := h
  have hfN : hNat J 20 < N := lt_trans hf hr
  have htl := stL_wLen_hWord (hDrop J 20)
  obtain ⟨hT, e1⟩ := stL_ptOK hy (hy.rwH _ hfN) (by have := hy.rwLen _ hfN; omega) htl hpt
  have e2 := stL_newOK hy hr (hy.pwH _) (by have := hy.pwLen (dPt (RD (hNat J 20))); omega) hT
    htl hnew
  have hff := (ih _ hf).1 hfa
  rw [e1] at hff
  rw [h1, h2, e2]
  exact stL_rc_congr (stL_rc_mul (stL_rc_symm hff)
    ((evalWord x (wList (hWord (hDrop J 20))))⁻¹ * u)) (by group)
    (by rw [stL_thinv hy.uu]; group)

theorem stL_trans_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : transOK LP RD RW PW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r)) * evalWord x (wList (RW r))) := by
  unfold transOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hfa, hs, h1, h2, -, hbr, hnew⟩ := h
  generalize hS : pathW RD RW (dN1 (RD r)) (fld J 40 255) (fld J 48 (ones (20 * fld J 40 255)))
    (Nat.beq (dAux (RD r)) 1) r = S at hs hbr
  generalize hTW : hWord (hDrop J (48 + 20 * fld J 40 255)) = tw at hbr hnew
  generalize hF : hNat J 20 = f at hf hfa h1 h2 hbr hnew
  have hpt : ptOK LP PW (dPt (RD r)) (wCat (S - 1) (PW (dPt (RD f)))) tw = true := by
    cases hd : Nat.beq (dAux (RD r)) 0 <;> rw [hd] at hbr <;>
      simp only [stL_andB_eq_true, Nat.beq_eq] at hbr
    · obtain ⟨e, hp⟩ := hbr; rw [e]; exact hp
    · obtain ⟨e, hp⟩ := hbr; rw [e]; exact hp
  have hfN : f < N := lt_trans hf hr
  have htl : wLen tw < 2 ^ 16 := hTW ▸ stL_wLen_hWord _
  obtain ⟨hSw, hSl, hSs⟩ := stL_pathW hy (X := X) hr.le (Nat.le_of_lt_succ (by
      have : fld J 40 255 < 256 := by
        rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, stL_fld_eq]; exact Nat.mod_lt _ (by norm_num)
      omega)) (fun g hg hgs => (ih g hg).2.1 hgs) (hS ▸ hs)
  rw [hS] at hSw hSl hSs
  have hcl : wLen (S - 1) + wLen (PW (dPt (RD f))) < 2 ^ 32 := by
    have := hy.pwLen (dPt (RD f)); omega
  obtain ⟨hT, e1⟩ := stL_ptOK hy (stL_wInH_wCat hcl hSw (hy.pwH _))
    (by rw [stL_wLen_wCat hcl]; have := hy.pwLen (dPt (RD f)); omega) htl hpt
  rw [stL_val_wCat x hcl (stL_wOK_of_wInH hSw)] at e1
  have e2 := stL_newOK hy hr (hy.rwH f hfN) (by have := hy.rwLen f hfN; omega) hT htl hnew
  have hff := (ih f hf).1 hfa
  rw [h1] at hff
  rw [← h2] at hff
  rw [e2]
  have hA : stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) *
      evalWord x (wList tw) * u) (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD f)))) * u) :=
    stL_rc_congr (stL_rc_mul hSs (evalWord x (wList (PW (dPt (RD f)))) * u))
      (by rw [show X (dN1 (RD r)) * evalWord x (wList (S - 1)) *
          (evalWord x (wList (PW (dPt (RD f)))) * u) = X (dN1 (RD r)) *
          (evalWord x (wList (S - 1)) * evalWord x (wList (PW (dPt (RD f))))) * u by group, e1]
          group) (by group)
  exact stL_rc_congr (stL_rc_uback hy.uu _ (stL_rc_trans hA hff)) rfl (by group)

theorem stL_dead_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : deadOK LP RD RW PW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r)) * evalWord x (wList (RW r))) := by
  unfold deadOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hc, hfa, hca, h1, h2, h3, hpt, hnew⟩ := h
  generalize hTW : hWord (hDrop J 40) = tw at hpt hnew
  generalize hF : hNat J 20 = f at hf hfa h1 h3 hpt hnew
  generalize hC : fld J 20 (ones 20) = c at hc hca h1 h2 hpt
  have hfN : f < N := lt_trans hf hr
  have hcN : c < N := lt_trans hc hr
  have htl : wLen tw < 2 ^ 16 := hTW ▸ stL_wLen_hWord _
  have hcl : wLen (RW c) + wLen (PW (dPt (RD f))) < 2 ^ 32 := by
    have := hy.pwLen (dPt (RD f)); have := hy.rwLen c hcN; omega
  obtain ⟨hT, e1⟩ := stL_ptOK hy (stL_wInH_wCat hcl (hy.rwH c hcN) (hy.pwH _))
    (by rw [stL_wLen_wCat hcl]; have := hy.pwLen (dPt (RD f)); have := hy.rwLen c hcN; omega)
    htl hpt
  rw [stL_val_wCat x hcl (stL_wOK_of_wInH (hy.rwH c hcN))] at e1
  have e2 := stL_newOK hy hr (hy.rwH f hfN) (by have := hy.rwLen f hfN; omega) hT htl hnew
  have hff := (ih f hf).1 hfa
  have hcc := (ih c hc).2.2 hca
  rw [h1] at hff
  rw [h2, h3, e2]
  have hA : stL_rc H (X (dN1 (RD c)) * evalWord x (wList (PW (dPt (RD r)))) *
      evalWord x (wList tw) * u) (X (dN2 (RD c)) * evalWord x (wList (PW (dPt (RD f)))) * u) :=
    stL_rc_congr (stL_rc_symm (stL_rc_mul hcc (evalWord x (wList (PW (dPt (RD f)))) * u)))
      (by rw [show X (dN1 (RD c)) * evalWord x (wList (RW c)) *
          (evalWord x (wList (PW (dPt (RD f)))) * u) = X (dN1 (RD c)) *
          (evalWord x (wList (RW c)) * evalWord x (wList (PW (dPt (RD f))))) * u by group, e1]
          group) (by group)
  exact stL_rc_congr (stL_rc_uback hy.uu _ (stL_rc_trans hA hff)) rfl (by group)

theorem stL_link_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : linkOK LP RD RW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN1 (RD r)) * evalWord x (wList (PW (dPt (RD r)))) * u)
      (X (dN2 (RD r)) * evalWord x (wList (RW r))) := by
  unfold linkOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hf, hc, hfa, hca, h1, h2, h3, h4, hone⟩ := h
  generalize hF : hNat J 20 = f at hf hfa h1 h2 h3 hone
  generalize hC : fld J 20 (ones 20) = c at hc hca h1 h4 hone
  have hfN : f < N := lt_trans hf hr
  have hcN : c < N := lt_trans hc hr
  have e := stL_isOne_rev3 hy hr (hy.rwH c hcN) (hy.rwH f hfN)
    (by have := hy.rwLen c hcN; omega) (by have := hy.rwLen f hfN; omega) hone
  have hff := (ih f hf).1 hfa
  have hcc := (ih c hc).2.2 hca
  rw [h1] at hff
  rw [h2, h3, h4, e, ← mul_assoc]
  exact stL_rc_trans hff (stL_rc_mul hcc _)

theorem stL_coinc_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : coincOK LP RD RW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN2 (RD r))) (X (dN1 (RD r)) * evalWord x (wList (RW r))) := by
  unfold coincOK twoAt at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨he, hf, hea, hfa, h1, h2, -, hbr⟩ := h
  generalize hE : hNat J 20 = e at he hea h1 h2 hbr
  generalize hF : fld J 20 (ones 20) = f at hf hfa h1 h2 hbr
  have heN : e < N := lt_trans he hr
  have hfN : f < N := lt_trans hf hr
  have hee := (ih e he).1 hea
  have hff := (ih f hf).1 hfa
  rw [h1, h2] at hee
  have hef := stL_rc_trans (stL_rc_symm hee) hff
  cases hd : Nat.blt (dN2 (RD e)) (dN2 (RD f)) <;> rw [hd] at hbr <;>
    simp only [stL_andB_eq_true, Nat.beq_eq] at hbr
  · obtain ⟨h3, h4, hone⟩ := hbr
    rw [h3, h4, stL_isOne_rev3 hy hr (hy.rwH f hfN) (stL_wInH_rev (hy.rwH e heN))
      (by have := hy.rwLen f hfN; omega)
      (by rw [stL_wLen_wRev]; have := hy.rwLen e heN; omega) hone, stL_val_wRev hy.xx]
    exact stL_rc_congr (stL_rc_mul hef (evalWord x (wList (RW e)))⁻¹) (by group) (by group)
  · obtain ⟨h3, h4, hone⟩ := hbr
    rw [h3, h4, stL_isOne_rev3 hy hr (hy.rwH e heN) (stL_wInH_rev (hy.rwH f hfN))
      (by have := hy.rwLen e heN; omega)
      (by rw [stL_wLen_wRev]; have := hy.rwLen f hfN; omega) hone, stL_val_wRev hy.xx]
    exact stL_rc_congr (stL_rc_mul (stL_rc_symm hef) (evalWord x (wList (RW f)))⁻¹) (by group)
      (by group)

theorem stL_let_sem (hy : stL_Hyp LP RD RW PW N H x u) (hX0 : X 0 = 1) {r : ℕ}
    (h : letOK RW r (RD r) = true) :
    stL_rc H (X (dN2 (RD r)) * evalWord x (wList (RW r))) (X (dN2 (RD r))) := by
  unfold letOK at h
  simp only [stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h3, hX0, stL_val_wOne x (by omega), one_mul]
  show x (dAux (RD r)) * 1⁻¹ ∈ H
  rw [inv_one, mul_one]
  exact hy.xH _ h2

theorem stL_seed_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : seedOK LP RD RW PW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN2 (RD r)) * evalWord x (wList (RW r))) (X (dN2 (RD r))) := by
  unfold seedOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨ht, hg, htk, hgs, hgi, hux, huy, h1, hpt, hone⟩ := h
  generalize hT : hNat J 20 = t at ht htk hgi hux huy h1 hpt
  generalize hG : fld J 20 (ones 20) = g at hg hgs hgi hpt
  generalize hTW : hWord (hDrop J (56 + 20 * (fld J 40 255 + fld J 48 255))) = tw at hpt hone
  generalize hUX : pathW RD RW (dN1 (RD t)) (fld J 40 255) (fld J 56 (ones (20 * fld J 40 255)))
    false r = UX at hux hpt
  generalize hUY : pathW RD RW (dN1 (RD t)) (fld J 48 255)
    (fld J (56 + 20 * fld J 40 255) (ones (20 * fld J 48 255))) true r = UY at huy hpt
  have htN : t < N := lt_trans ht hr
  have hgN : g < N := lt_trans hg hr
  have htl : wLen tw < 2 ^ 16 := hTW ▸ stL_wLen_hWord _
  have h255 : ∀ o, fld J o 255 ≤ 255 := fun o => by
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, stL_fld_eq]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hstab : ∀ g < r, isStab (dKind (RD g)) = true →
      stL_rc H (X (dN2 (RD g)) * evalWord x (wList (RW g))) (X (dN2 (RD g))) :=
    fun g hg hgs => (ih g hg).2.1 hgs
  obtain ⟨hXw, hXl, hXs⟩ := stL_pathW hy (X := X) hr.le (h255 _) hstab (hUX ▸ hux)
  obtain ⟨hYw, hYl, hYs⟩ := stL_pathW hy (X := X) hr.le (h255 _) hstab (hUY ▸ huy)
  rw [hUX] at hXw hXl hXs
  rw [hUY] at hYw hYl hYs
  have hgl := hy.rwLen g hgN
  have hpl := hy.pwLen (dPt (RD t))
  have hc1 : wLen (UX - 1) + wLen (PW (dPt (RD t))) < 2 ^ 32 := by omega
  have hc2 : wLen (RW g) + wLen (wCat (UX - 1) (PW (dPt (RD t)))) < 2 ^ 32 := by
    rw [stL_wLen_wCat hc1]; omega
  have hc3 : wLen (UY - 1) + wLen (wCat (RW g) (wCat (UX - 1) (PW (dPt (RD t))))) < 2 ^ 32 := by
    rw [stL_wLen_wCat hc2, stL_wLen_wCat hc1]; omega
  obtain ⟨hTT, e1⟩ := stL_ptOK hy
    (stL_wInH_wCat hc3 hYw (stL_wInH_wCat hc2 (hy.rwH g hgN) (stL_wInH_wCat hc1 hXw (hy.pwH _))))
    (by rw [stL_wLen_wCat hc3, stL_wLen_wCat hc2, stL_wLen_wCat hc1]; omega) htl hpt
  rw [stL_val_wCat x hc3 (stL_wOK_of_wInH hYw), stL_val_wCat x hc2 (stL_wOK_of_wInH (hy.rwH g hgN)),
    stL_val_wCat x hc1 (stL_wOK_of_wInH hXw)] at e1
  have e2 := stL_isOne2 hy (stL_wInH_rev (hy.rwH r hr)) (stL_wInH_wTh hTT)
    (by rw [stL_wLen_wRev]; have := hy.rwLen r hr; omega) (by rw [stL_wLen_wTh]; omega) hone
  rw [stL_val_wRev hy.xx, stL_val_wTh hy.uu hy.θ hTT] at e2
  have e3 : evalWord x (wList (RW r)) = u * evalWord x (wList tw) * u := by
    calc evalWord x (wList (RW r)) = evalWord x (wList (RW r)) * ((evalWord x (wList (RW r)))⁻¹ *
          (u * evalWord x (wList tw) * u)) := by rw [e2, mul_one]
      _ = _ := by group
  have hsg := hstab g hg hgs
  rw [hgi] at hsg
  have htt := (ih t ht).1 (by rw [stL_isFact_iff, htk]; norm_num)
  rw [hy.tree0 t htN htk, stL_val_zero, mul_one] at htt
  have hy3 := stL_rc_stab_mul (stL_rc_stab_mul hYs hsg) hXs
  have hB : stL_rc H (X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) *
      evalWord x (wList tw) * u) (X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) * u) :=
    stL_rc_congr (stL_rc_mul hy3 (evalWord x (wList (PW (dPt (RD t)))) * u))
      (by rw [show X (dN1 (RD t)) * (evalWord x (wList (UY - 1)) * evalWord x (wList (RW g)) *
          evalWord x (wList (UX - 1))) * (evalWord x (wList (PW (dPt (RD t)))) * u) =
          X (dN1 (RD t)) * (evalWord x (wList (UY - 1)) * (evalWord x (wList (RW g)) *
          (evalWord x (wList (UX - 1)) * evalWord x (wList (PW (dPt (RD t))))))) * u by group, e1]
          group) (by group)
  rw [h1, e3]
  have hC : stL_rc H (X (dN2 (RD t)) * (u * evalWord x (wList tw) * u))
      (X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) * evalWord x (wList tw) * u) :=
    stL_rc_congr (stL_rc_mul (stL_rc_symm htt) (u * evalWord x (wList tw) * u)) rfl
      (by rw [show X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) * u *
          (u * evalWord x (wList tw) * u) = X (dN1 (RD t)) * evalWord x (wList (PW (dPt (RD t)))) *
          (u * u) * evalWord x (wList tw) * u by group, hy.uu, mul_one])
  exact stL_rc_trans hC (stL_rc_trans hB htt)

theorem stL_diff_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : diffOK LP RD RW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN2 (RD r)) * evalWord x (wList (RW r))) (X (dN2 (RD r))) := by
  unfold diffOK twoAt at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨he, hf, hea, hfa, h1, h2, h3, h4, hone⟩ := h
  generalize hE : hNat J 20 = e at he hea h1 h2 h3 h4 hone
  generalize hF : fld J 20 (ones 20) = f at hf hfa h1 h2 h3 hone
  have heN : e < N := lt_trans he hr
  have hfN : f < N := lt_trans hf hr
  have hee := (ih e he).1 hea
  have hff := (ih f hf).1 hfa
  rw [h1, h2] at hee
  rw [← h3] at hff
  have hef := stL_rc_trans (stL_rc_symm hee) hff
  rw [h4, stL_isOne_rev3 hy hr (hy.rwH e heN) (stL_wInH_rev (hy.rwH f hfN))
    (by have := hy.rwLen e heN; omega)
    (by rw [stL_wLen_wRev]; have := hy.rwLen f hfN; omega) hone, stL_val_wRev hy.xx]
  exact stL_rc_congr (stL_rc_mul hef (evalWord x (wList (RW f)))⁻¹) (by group) (by group)

theorem stL_conj_sem (hy : stL_Hyp LP RD RW PW N H x u) {r J : ℕ} (hr : r < N)
    (h : conjOK LP RD RW r (RD r) J = true) (ih : ∀ q < r, stL_Sem H x u X RD RW PW q) :
    stL_rc H (X (dN2 (RD r)) * evalWord x (wList (RW r))) (X (dN2 (RD r))) := by
  unfold conjOK at h
  simp only [stL_sB, stL_andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hc, hw, hca, hws, h1, h2, hone⟩ := h
  generalize hC : hNat J 20 = c at hc hca h1 h2 hone
  generalize hW : fld J 20 (ones 20) = w at hw hws h1 hone
  have hcN : c < N := lt_trans hc hr
  have hwN : w < N := lt_trans hw hr
  have hcc := (ih c hc).2.2 hca
  have hww := (ih w hw).2.1 hws
  rw [h1] at hww
  rw [h2, stL_isOne_rev4 hy hr (hy.rwH c hcN) (hy.rwH w hwN) (stL_wInH_rev (hy.rwH c hcN))
    (by have := hy.rwLen c hcN; omega) (by have := hy.rwLen w hwN; omega)
    (by rw [stL_wLen_wRev]; have := hy.rwLen c hcN; omega) hone, stL_val_wRev hy.xx]
  set d := evalWord x (wList (RW c))
  set s := evalWord x (wList (RW w))
  have h3 : stL_rc H (X (dN1 (RD c)) * (d * s * d⁻¹)) (X (dN2 (RD c)) * (s * d⁻¹)) :=
    stL_rc_congr (stL_rc_mul (stL_rc_symm hcc) (s * d⁻¹)) (by group) rfl
  have h4 : stL_rc H (X (dN2 (RD c)) * (s * d⁻¹)) (X (dN2 (RD c)) * d⁻¹) :=
    stL_rc_congr (stL_rc_mul hww d⁻¹) (by group) rfl
  have h5 : stL_rc H (X (dN2 (RD c)) * d⁻¹) (X (dN1 (RD c))) :=
    stL_rc_congr (stL_rc_mul hcc d⁻¹) rfl (by group)
  exact stL_rc_trans h3 (stL_rc_trans h4 h5)

end

end CFSG.KC.B433Alt

end

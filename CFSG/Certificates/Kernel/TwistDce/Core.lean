module

public import CFSG.Certificates.Kernel.TwistDce.Words
public import CFSG.Certificates.CosetEnumeration
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Certificates.TwDce.Core

open CFSG.KC.TwDce CFSG.KC.YModel CFSG.Certificates.CosetEnumeration CFSG.Certificates.TwDce.Words

variable {G : Type*} [Group G]

@[expose] def CE (H : Subgroup G) (g g' : G) : Prop := g * g'⁻¹ ∈ H

theorem CE.refl (H : Subgroup G) (g : G) : CE H g g := by
  simp [CE]

theorem CE.symm {H : Subgroup G} {g g' : G} (h : CE H g g') : CE H g' g := by
  have := H.inv_mem h
  rwa [mul_inv_rev, inv_inv] at this

theorem CE.trans {H : Subgroup G} {g g' g'' : G} (h : CE H g g') (h' : CE H g' g'') : CE H g g'' := by
  have := H.mul_mem h h'
  rwa [mul_assoc, inv_mul_cancel_left] at this

theorem CE.mul_right {H : Subgroup G} {g g' : G} (h : CE H g g') (z : G) : CE H (g * z) (g' * z) := by
  unfold CE
  rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]

theorem CE.of_left {H : Subgroup G} {h : G} (hh : h ∈ H) (g : G) : CE H (h * g) g := by
  unfold CE
  rwa [mul_inv_cancel_right]

theorem CE.of_eq {H : Subgroup G} {g g' : G} (h : g = g') : CE H g g' := h ▸ CE.refl H g

@[expose] noncomputable def val (x : ℕ → G) (w : ℕ) : G := evalWord x (lst w)

structure GW (B w : ℕ) : Prop where
  ok : wOK w = true
  lt : ∀ c ∈ lst w, c < 10
  len : wLen w < B

theorem GW.mono {B B' w : ℕ} (h : GW B w) (hB : B ≤ B') : GW B' w :=
  ⟨h.ok, h.lt, lt_of_lt_of_le h.len hB⟩

theorem evalWord_append (x : ℕ → G) (l l' : List ℕ) :
    evalWord x (l ++ l') = evalWord x l * evalWord x l' := by
  simp [evalWord]

theorem evalWord_reverse {x : ℕ → G} (hx : ∀ c, x c * x c = 1) (l : List ℕ) :
    evalWord x l.reverse = (evalWord x l)⁻¹ := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.reverse_cons, evalWord_append, ih, evalWord_cons, evalWord_cons, evalWord_nil, mul_one,
      mul_inv_rev, inv_eq_of_mul_eq_one_left (hx c)]

theorem evalWord_mem {H : Subgroup G} {x : ℕ → G} (hxH : ∀ c < 10, x c ∈ H) {l : List ℕ}
    (hl : ∀ c ∈ l, c < 10) : evalWord x l ∈ H := by
  induction l with
  | nil => exact H.one_mem
  | cons c l ih =>
    rw [evalWord_cons]
    exact H.mul_mem (hxH c (hl c List.mem_cons_self))
      (ih fun d hd => hl d (List.mem_cons_of_mem _ hd))

theorem evalWord_th {x : ℕ → G} {u : G} {THM : ℕ} (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c)) {l : List ℕ}
    (hl : ∀ c ∈ l, c < 10 ∧ thL THM c < 10) :
    evalWord x l * u = u * evalWord x (l.map (thL THM)) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc := hl c List.mem_cons_self
    rw [List.map_cons, evalWord_cons, evalWord_cons, mul_assoc,
      ih fun d hd => hl d (List.mem_cons_of_mem _ hd), ← mul_assoc, ← mul_assoc, ← hθ c hc.1 hc.2]
    have : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
    rw [show x c * u = u * (u * x c * u) by
      rw [← mul_assoc, ← mul_assoc, hu, one_mul]]

theorem val_one {x : ℕ → G} {F : ℕ → ℕ} {BS NB : ℕ}
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {w : ℕ} (hw : ∀ c ∈ lst w, c < 10) (h : isOne F BS NB w = true) : val x w = 1 :=
  hone _ hw (isOne_spec h).1 (isOne_spec h).2

theorem GW.cat {A B a b : ℕ} (ha : GW A a) (hb : GW B b) (h : A + B ≤ 2 ^ 32) :
    GW (A + B) (wCat a b) ∧ lst (wCat a b) = lst a ++ lst b := by
  have hl : wLen a + wLen b < 2 ^ 32 := by have := ha.len; have := hb.len; omega
  obtain ⟨h1, h2, h3⟩ := wCat_spec ha.ok hb.ok hl
  refine ⟨⟨h2, fun c hc => ?_, by rw [h1]; have := ha.len; have := hb.len; omega⟩, h3⟩
  rw [h3, List.mem_append] at hc
  exact hc.elim (ha.lt c) (hb.lt c)

theorem GW.rev {B w : ℕ} (h : GW B w) : GW B (wRev w) ∧ lst (wRev w) = (lst w).reverse := by
  obtain ⟨h1, h2, h3⟩ := wRev_spec w
  refine ⟨⟨h2, fun c hc => ?_, by rw [h1]; exact h.len⟩, h3⟩
  rw [h3, List.mem_reverse] at hc
  exact h.lt c hc

theorem val_cat {x : ℕ → G} {a b : ℕ} (h : lst (wCat a b) = lst a ++ lst b) :
    val x (wCat a b) = val x a * val x b := by
  rw [val, h, evalWord_append]; rfl

theorem val_rev {x : ℕ → G} (hx : ∀ c, x c * x c = 1) (w : ℕ) : val x (wRev w) = (val x w)⁻¹ := by
  rw [val, (wRev_spec w).2.2, evalWord_reverse hx]; rfl

theorem brec_eq {α : Sort*} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by cases c <;> rfl

section Rec

variable (RD RW RA : ℕ → ℕ) (H : Subgroup G) (x : ℕ → G) (u : G)

structure RecHolds (X : ℕ → G) (f : ℕ) : Prop where
  rw : GW (2 ^ 20) (RW f)
  ra : GW (2 ^ 20) (RA f)
  fact : dKind (RD f) < 3 →
    CE H (X (dN1 (RD f)) * val x (RW f) * u) (X (dN2 (RD f)) * val x (RA f))
  stab : 3 ≤ dKind (RD f) → dKind (RD f) < 5 →
    X (dN2 (RD f)) * val x (RW f) * (X (dN2 (RD f)))⁻¹ ∈ H

@[expose] def Hist (X : ℕ → G) (r : ℕ) : Prop := ∀ f < r, RecHolds RD RW RA H x u X f

@[expose] noncomputable def pR (k r : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wRev (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) k)))))))

theorem pathW_eq (k m L r : ℕ) : pathW RD RW k m L r = pR RD RW k r m L 1 := rfl

variable {RD RW RA H x u}

theorem conj_mul_mem {X : ℕ → G} {k : ℕ} {a b : G} (ha : X k * a * (X k)⁻¹ ∈ H)
    (hb : X k * b * (X k)⁻¹ ∈ H) : X k * (a * b) * (X k)⁻¹ ∈ H := by
  have := H.mul_mem ha hb
  rwa [show X k * a * (X k)⁻¹ * (X k * b * (X k)⁻¹) = X k * (a * b) * (X k)⁻¹ by group] at this

theorem conj_inv_mem {X : ℕ → G} {k : ℕ} {b : G} (hb : X k * b * (X k)⁻¹ ∈ H) :
    X k * b⁻¹ * (X k)⁻¹ ∈ H := by
  have := H.inv_mem hb
  rwa [show (X k * b * (X k)⁻¹)⁻¹ = X k * b⁻¹ * (X k)⁻¹ by group] at this

theorem pR_succ (k r m L acc : ℕ) : pR RD RW k r (m + 1) L acc =
    sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wRev (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            pR RD RW k r m (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) k)))))) := rfl

theorem path_spec (hx : ∀ c, x c * x c = 1) {X : ℕ → G} {k r : ℕ} (hH : Hist RD RW RA H x u X r) :
    ∀ m L acc B, 0 < acc → GW B (acc - 1) → B + m * 2 ^ 20 ≤ 2 ^ 32 →
      X k * val x (acc - 1) * (X k)⁻¹ ∈ H → 0 < pR RD RW k r m L acc →
      GW (B + m * 2 ^ 20) (pR RD RW k r m L acc - 1) ∧
        X k * val x (pR RD RW k r m L acc - 1) * (X k)⁻¹ ∈ H := by
  intro m
  induction m with
  | zero =>
    intro L acc B _ hg _ hc _
    show GW (B + 0 * 2 ^ 20) (acc - 1) ∧ _
    exact ⟨hg.mono (by simp), hc⟩
  | succ m ih =>
    intro L acc B hacc hg hB hc hS
    rw [pR_succ, sN_eq, sN_eq, brec_eq, sN_eq, brec_eq] at hS ⊢
    have hB' : B + 2 ^ 20 + m * 2 ^ 20 ≤ 2 ^ 32 := by rw [Nat.add_one_mul] at hB; omega
    have key : ∀ v, GW (2 ^ 20) v → X k * val x v * (X k)⁻¹ ∈ H →
        0 < pR RD RW k r m (Nat.shiftRight L 21) (Nat.succ (wCat (acc - 1) v)) →
        GW (B + (m + 1) * 2 ^ 20) (pR RD RW k r m (Nat.shiftRight L 21)
          (Nat.succ (wCat (acc - 1) v)) - 1) ∧
        X k * val x (pR RD RW k r m (Nat.shiftRight L 21)
          (Nat.succ (wCat (acc - 1) v)) - 1) * (X k)⁻¹ ∈ H := by
      intro v hv hcv hpos
      obtain ⟨h1, h2⟩ := hg.cat hv (by omega)
      rw [show B + (m + 1) * 2 ^ 20 = B + 2 ^ 20 + m * 2 ^ 20 by ring]
      exact ih (Nat.shiftRight L 21) (Nat.succ (wCat (acc - 1) v)) (B + 2 ^ 20)
        (Nat.succ_pos _) (by rw [Nat.succ_sub_one]; exact h1) hB'
        (by rw [Nat.succ_sub_one, val_cat h2]; exact conj_mul_mem hc hcv) hpos
    split_ifs at hS ⊢ with hcond hdir
    all_goals first
      | exact absurd hS (lt_irrefl 0)
      | (simp only [andB_iff] at hcond
         obtain ⟨-, hg1, hst, hk⟩ := hcond
         have hgr := Nat.blt_eq.mp hg1
         have hR := hH _ hgr
         have hk' := Nat.eq_of_beq_eq_true hk
         unfold isStab at hst
         rw [andB_iff] at hst
         have hstab := hR.stab (Nat.le_of_ble_eq_true hst.1) (Nat.blt_eq.mp hst.2)
         rw [hk'] at hstab
         first
           | exact key _ hR.rw.rev.1 (by rw [val_rev hx]; exact conj_inv_mem hstab) hS
           | exact key _ hR.rw hstab hS)

end Rec

section Step

variable {F RD RW RA : ℕ → ℕ} {THM BS NB : ℕ} {H : Subgroup G} {x : ℕ → G} {u : G}

theorem GW.zero : GW 1 0 := ⟨wOK_zero, by simp [lst_zero], by
  have := length_lst 0; rw [lst_zero] at this; simp at this; omega⟩

theorem GW.th {THM w : ℕ} (hT : wInT THM w = true) (hl : wLen w < 2 ^ 16) :
    GW (2 ^ 16) w ∧ GW (2 ^ 16) (wTh THM w) ∧ lst (wTh THM w) = (lst w).map (thL THM) := by
  obtain ⟨h1, h2⟩ := wInT_spec hT
  obtain ⟨e1, e2, e3⟩ := wTh_spec THM w
  refine ⟨⟨h1, fun c hc => (h2 c hc).1, hl⟩, ⟨e2, fun c hc => ?_, by rw [e1]; exact hl⟩, e3⟩
  rw [e3, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  exact (h2 d hd).2

theorem wsBad_fail (a : ℕ) : wsFail (wsBad a).1 = 1 :=
  (wsMk_spec (by norm_num) (by norm_num) 0).2.1

variable (F THM BS NB H x u) in
theorem step_core (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {n n' w w' tw Sw a : ℕ}
    (hfact : CE H (X n * val x w * u) (X n' * val x w'))
    (hw : GW (2 ^ 20) w) (hw' : GW (2 ^ 20) w') (hT : wInT THM tw = true) (htl : wLen tw < 2 ^ 16)
    (hS : GW (2 ^ 28) Sw) (hSc : X n * val x Sw * (X n)⁻¹ ∈ H) (ha : GW (2 ^ 22) a)
    (h1 : isOne F BS NB (cat4 (wRev tw) (wRev w) (wRev Sw) a) = true) :
    CE H (X n * val x a * u) (X n' * val x (wCat w' (wTh THM tw))) ∧
      GW (2 ^ 21) (wCat w' (wTh THM tw)) := by
  obtain ⟨gt, gth, eth⟩ := GW.th hT htl
  obtain ⟨c1, e1⟩ := hS.rev.1.cat ha (by norm_num)
  obtain ⟨c2, e2⟩ := hw.rev.1.cat c1 (by norm_num)
  obtain ⟨c3, e3⟩ := gt.rev.1.cat c2 (by norm_num)
  obtain ⟨c4, e4⟩ := hw'.cat gth (by norm_num)
  refine ⟨?_, c4.mono (by norm_num)⟩
  have hv := val_one hone c3.lt h1
  unfold cat4 at hv
  rw [val_cat e3, val_cat e2, val_cat e1, val_rev hx, val_rev hx, val_rev hx] at hv
  have ea : val x a = val x Sw * val x w * val x tw := by
    have := congrArg (fun z => val x Sw * (val x w * (val x tw * z))) hv
    simp only [mul_one] at this
    rw [mul_assoc, ← this]
    group
  have hth : val x tw * u = u * val x (wTh THM tw) := by
    rw [val, val, eth]
    exact evalWord_th hu hθ fun c hc => (wInT_spec hT).2 c hc
  rw [val_cat e4, ea]
  have e5 : X n * (val x Sw * val x w * val x tw) * u =
      (X n * val x Sw * (X n)⁻¹) * (X n * val x w * u * val x (wTh THM tw)) := by
    rw [show X n * val x w * u * val x (wTh THM tw) = X n * val x w * (u * val x (wTh THM tw)) by
      group, ← hth]
    group
  rw [e5, ← mul_assoc (X n')]
  exact (CE.of_left hSc _).trans (hfact.mul_right _)

theorem val_zero (x : ℕ → G) : val x 0 = 1 := by
  rw [val, lst_zero, evalWord_nil]

theorem CE.flip_u {H : Subgroup G} {u : G} (hu : u * u = 1) {a b : G} (h : CE H (a * u) b) :
    CE H (b * u) a := by
  have := h.symm.mul_right u
  rwa [mul_assoc, hu, mul_one] at this

variable (F THM BS NB RD RW RA H x u) in
theorem step_spec (hx : ∀ c, x c * x c = 1) (hu : u * u = 1)
    (hθ : ∀ c < 10, thL THM c < 10 → u * x c * u = x (thL THM c))
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 10) → Even w.length →
      (∀ i < NB, w.foldl (fun p c => fieldAt 32 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r k a J : ℕ} (hH : Hist RD RW RA H x u X r) (ha : GW (2 ^ 22) a)
    (hf : wsFail (stepCore F THM BS NB RD RW RA r k a J).1 = 0) :
    CE H (X k * val x a * u) (X (wsK (stepCore F THM BS NB RD RW RA r k a J).1) *
      val x (stepCore F THM BS NB RD RW RA r k a J).2) ∧
    GW (2 ^ 21) (stepCore F THM BS NB RD RW RA r k a J).2 := by
  have hm : fld J 21 255 < 256 := fld_lt_succ _ _ _
  have hpath : ∀ m L, m < 256 → 0 < pathW RD RW k m L r →
      GW (2 ^ 28) (pathW RD RW k m L r - 1) ∧
        X k * val x (pathW RD RW k m L r - 1) * (X k)⁻¹ ∈ H := by
    intro m L hm hS
    rw [pathW_eq] at hS ⊢
    have hb : 1 + m * 2 ^ 20 ≤ 2 ^ 28 := by
      have : m * 2 ^ 20 ≤ 255 * 2 ^ 20 := Nat.mul_le_mul_right _ (by omega)
      norm_num at this ⊢; omega
    obtain ⟨h1, h2⟩ := path_spec hx hH m L 1 1 Nat.one_pos GW.zero (by omega)
      (by show X k * val x 0 * (X k)⁻¹ ∈ H; rw [val_zero, mul_one, mul_inv_cancel]; exact H.one_mem)
      hS
    exact ⟨h1.mono hb, h2⟩
  obtain hd | hd : Nat.beq (fld J 20 1) 0 = true ∨ Nat.beq (fld J 20 1) 0 = false := by
    cases Nat.beq (fld J 20 1) 0 <;> simp
  all_goals
    unfold stepCore at hf ⊢
    simp only [sW_eq, brec_eq, hd, ↓reduceIte, Bool.false_eq_true] at hf ⊢
    split_ifs at hf ⊢ with hc
    swap
    · exact absurd hf (by rw [wsBad_fail]; norm_num)
    simp only [andB_iff] at hc
    obtain ⟨hfr, hfa, -, hk, hS, hT, h1⟩ := hc
    have hR := hH _ (Nat.blt_eq.mp hfr)
    have hfa' : dKind (RD (hNat J 20)) < 3 := Nat.blt_eq.mp hfa
    have hk' := Nat.eq_of_beq_eq_true hk
    obtain ⟨hSg, hSc⟩ := hpath _ _ hm (Nat.blt_eq.mp hS)
    rw [(wsMk_spec (by first | exact dN1_lt _ | exact dN2_lt _) (by norm_num) _).1]
  · subst hk'
    exact step_core F THM BS NB H x u hx hu hθ hone (hR.fact hfa') hR.rw hR.ra hT
      (hWord_spec _).1 hSg hSc ha h1
  · subst hk'
    exact step_core F THM BS NB H x u hx hu hθ hone (CE.flip_u hu (hR.fact hfa')) hR.ra hR.rw hT
      (hWord_spec _).1 hSg hSc ha h1

end Step

end CFSG.Certificates.TwDce.Core

end

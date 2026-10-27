module

public import CFSG.Certificates.Kernel.TwistDce2.Words
public import CFSG.Certificates.Kernel.TwistDce.Core

public section

namespace CFSG.Certificates.TwDce2.Walk

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 CFSG.KC.YModel CFSG.Certificates.CosetEnumeration
open CFSG.Certificates.TwDce.Words hiding evP_eq isOne_spec wsMk_spec wsFail_lt dN1_lt dN2_lt
open CFSG.Certificates.TwDce.Core hiding wsBad_fail
open CFSG.Certificates.TwDce2.Words

variable {G : Type*} [Group G]

structure GD (B w : ℕ) : Prop where
  ok : wOK w = true
  lt : ∀ c ∈ lst w, c < 12
  len : wLen w < B

theorem GD.mono {B B' w : ℕ} (h : GD B w) (hB : B ≤ B') : GD B' w :=
  ⟨h.ok, h.lt, lt_of_lt_of_le h.len hB⟩

theorem GD.cat {A B a b : ℕ} (ha : GD A a) (hb : GD B b) (h : A + B ≤ 2 ^ 32) :
    GD (A + B) (wCat a b) ∧ lst (wCat a b) = lst a ++ lst b := by
  have hl : wLen a + wLen b < 2 ^ 32 := by have := ha.len; have := hb.len; omega
  obtain ⟨h1, h2, h3⟩ := wCat_spec ha.ok hb.ok hl
  refine ⟨⟨h2, fun c hc => ?_, by rw [h1]; have := ha.len; have := hb.len; omega⟩, h3⟩
  rw [h3, List.mem_append] at hc
  exact hc.elim (ha.lt c) (hb.lt c)

theorem GD.zero : GD 1 0 := ⟨wOK_zero, by simp [lst_zero], by
  have := length_lst 0; rw [lst_zero] at this; simp at this; omega⟩

theorem evalWord_mem12 {H : Subgroup G} {x : ℕ → G} (hxH : ∀ c < 12, x c ∈ H) {l : List ℕ}
    (hl : ∀ c ∈ l, c < 12) : evalWord x l ∈ H := by
  induction l with
  | nil => exact H.one_mem
  | cons c l ih =>
    rw [evalWord_cons]
    exact H.mul_mem (hxH c (hl c List.mem_cons_self))
      (ih fun d hd => hl d (List.mem_cons_of_mem _ hd))

theorem evalWord_comm {x : ℕ → G} {s : G} (hs : ∀ c < 4, x c * s = s * x c) :
    ∀ l : List ℕ, (∀ c ∈ l, c < 4) → evalWord x l * s = s * evalWord x l
  | [], _ => by simp
  | c :: l, hl => by
    rw [evalWord_cons, mul_assoc, evalWord_comm hs l fun d hd => hl d (List.mem_cons_of_mem _ hd),
      ← mul_assoc, hs c (hl c List.mem_cons_self), mul_assoc]

section Inv

variable {INVM : ℕ} {x : ℕ → G}

theorem evalWord_invL (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹) :
    ∀ l : List ℕ, (∀ c ∈ l, c < 12) → evalWord x (l.reverse.map (ivL INVM)) = (evalWord x l)⁻¹
  | [], _ => by simp
  | c :: l, hl => by
    rw [List.reverse_cons, List.map_append, evalWord_append,
      evalWord_invL hinv l (fun d hd => hl d (List.mem_cons_of_mem _ hd)), List.map_singleton,
      evalWord_cons, evalWord_nil, mul_one, (hinv c (hl c List.mem_cons_self)).2, evalWord_cons,
      mul_inv_rev]

theorem GD.inv (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹) {B w : ℕ}
    (h : GD B w) : GD B (wInv INVM w) ∧ val x (wInv INVM w) = (val x w)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := wInv_spec INVM w
  refine ⟨⟨h2, fun c hc => ?_, by rw [h1]; exact h.len⟩, ?_⟩
  · rw [h3, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact (hinv d (h.lt d (List.mem_reverse.1 hd))).1
  · show evalWord x (lst (wInv INVM w)) = (evalWord x (lst w))⁻¹
    rw [h3]
    exact evalWord_invL hinv _ h.lt

end Inv

theorem ce_flip_t {H : Subgroup G} {t a b : G} (h : CE H (a * t) b) : CE H (b * t⁻¹) a := by
  have := h.symm
  unfold CE at this ⊢
  convert this using 1
  group

theorem ce_flip_inv {H : Subgroup G} {t a b : G} (h : CE H (a * t⁻¹) b) : CE H (b * t) a := by
  have := h.symm
  unfold CE at this ⊢
  convert this using 1
  group

section Rec

variable (RD RW RA : ℕ → ℕ) (H : Subgroup G) (x : ℕ → G) (t : G)

structure RH (X : ℕ → G) (f : ℕ) : Prop where
  rw : GD (2 ^ 16) (RW f)
  ra : GD (2 ^ 16) (RA f)
  fact : dKind (RD f) < 3 →
    CE H (X (dN1 (RD f)) * val x (RW f) * t) (X (dN2 (RD f)) * val x (RA f))
  eq : 3 ≤ dKind (RD f) → dKind (RD f) < 5 →
    CE H (X (dN1 (RD f))) (X (dN2 (RD f)) * val x (RW f))

@[expose] def Hist2 (X : ℕ → G) (r : ℕ) : Prop := ∀ f < r, RH RD RW RA H x t X f

@[expose] noncomputable def pR2 (INVM k r : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wInv INVM (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isEq (dKind dg)) (andB (Nat.beq (dN1 dg) k) (Nat.beq (dN2 dg) k))))))))

theorem pathW_eq2 (INVM k m L r : ℕ) : pathW INVM RD RW k m L r = pR2 RD RW INVM k r m L 1 := rfl

variable {RD RW RA H x t}

theorem pR2_succ (INVM k r m L acc : ℕ) : pR2 RD RW INVM k r (m + 1) L acc =
    sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wInv INVM (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            pR2 RD RW INVM k r m (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isEq (dKind dg)) (andB (Nat.beq (dN1 dg) k) (Nat.beq (dN2 dg) k))))))) := rfl

theorem path_spec2 {INVM : ℕ} (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    {X : ℕ → G} {k r : ℕ} (hH : Hist2 RD RW RA H x t X r) :
    ∀ m L acc B, 0 < acc → GD B (acc - 1) → B + m * 2 ^ 16 ≤ 2 ^ 32 →
      X k * val x (acc - 1) * (X k)⁻¹ ∈ H → 0 < pR2 RD RW INVM k r m L acc →
      GD (B + m * 2 ^ 16) (pR2 RD RW INVM k r m L acc - 1) ∧
        X k * val x (pR2 RD RW INVM k r m L acc - 1) * (X k)⁻¹ ∈ H := by
  intro m
  induction m with
  | zero =>
    intro L acc B _ hg _ hc _
    show GD (B + 0 * 2 ^ 16) (acc - 1) ∧ _
    exact ⟨hg.mono (by simp), hc⟩
  | succ m ih =>
    intro L acc B hacc hg hB hc hS
    rw [pR2_succ, sN_eq, sN_eq, brec_eq, sN_eq, brec_eq] at hS ⊢
    have hB' : B + 2 ^ 16 + m * 2 ^ 16 ≤ 2 ^ 32 := by rw [Nat.add_one_mul] at hB; omega
    have key : ∀ v, GD (2 ^ 16) v → X k * val x v * (X k)⁻¹ ∈ H →
        0 < pR2 RD RW INVM k r m (Nat.shiftRight L 21) (Nat.succ (wCat (acc - 1) v)) →
        GD (B + (m + 1) * 2 ^ 16) (pR2 RD RW INVM k r m (Nat.shiftRight L 21)
          (Nat.succ (wCat (acc - 1) v)) - 1) ∧
        X k * val x (pR2 RD RW INVM k r m (Nat.shiftRight L 21)
          (Nat.succ (wCat (acc - 1) v)) - 1) * (X k)⁻¹ ∈ H := by
      intro v hv hcv hpos
      obtain ⟨h1, h2⟩ := hg.cat hv (by omega)
      rw [show B + (m + 1) * 2 ^ 16 = B + 2 ^ 16 + m * 2 ^ 16 by ring]
      exact ih (Nat.shiftRight L 21) (Nat.succ (wCat (acc - 1) v)) (B + 2 ^ 16)
        (Nat.succ_pos _) (by rw [Nat.succ_sub_one]; exact h1) hB'
        (by rw [Nat.succ_sub_one, val_cat h2]; exact conj_mul_mem hc hcv) hpos
    split_ifs at hS ⊢ with hcond hdir
    all_goals first
      | exact absurd hS (lt_irrefl 0)
      | (simp only [kandB_iff] at hcond
         obtain ⟨-, hg1, hst, hk1, hk2⟩ := hcond
         have hR := hH _ (Nat.blt_eq.mp hg1)
         unfold isEq at hst
         rw [kandB_iff] at hst
         have he := hR.eq (Nat.le_of_ble_eq_true hst.1) (Nat.blt_eq.mp hst.2)
         rw [Nat.eq_of_beq_eq_true hk1, Nat.eq_of_beq_eq_true hk2] at he
         have hci : X k * (val x (RW (Nat.land L (ones 20))))⁻¹ * (X k)⁻¹ ∈ H := by
           unfold CE at he
           convert he using 1
           group
         first
           | exact key _ (hR.rw.inv hinv).1 (by rw [(hR.rw.inv hinv).2]; exact hci) hS
           | exact key _ hR.rw (by simpa using conj_inv_mem hci) hS)

end Rec

section Step

variable {F RD RW RA : ℕ → ℕ} {INVM BS NB : ℕ} {H : Subgroup G} {x : ℕ → G} {t : G}

theorem val_one2
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {w : ℕ} (hw : ∀ c ∈ lst w, c < 12) (h : isOne F BS NB w = true) : val x w = 1 :=
  hone _ hw (isOne_spec h)

theorem val_eq_of_isOne2 (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {A B v w : ℕ} (hv : GD A v) (hw : GD B w) (hAB : A + B ≤ 2 ^ 32)
    (h : isOne F BS NB (wCat (wInv INVM v) w) = true) : val x v = val x w := by
  obtain ⟨g, e⟩ := GD.cat (hv.inv hinv).1 hw hAB
  have := val_one2 hone g.lt h
  rw [val_cat e, (hv.inv hinv).2] at this
  exact inv_mul_eq_one.mp this

theorem inv_comm_of {a s : G} (h : a * s = s * a) : a * s⁻¹ = s⁻¹ * a := by
  calc a * s⁻¹ = s⁻¹ * (s * a) * s⁻¹ := by group
    _ = s⁻¹ * (a * s) * s⁻¹ := by rw [h]
    _ = s⁻¹ * a := by group

variable (F INVM BS NB H x) in
theorem step_core2 (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {s : G} {n n' w w' tw Sw a : ℕ}
    (hfact : CE H (X n * val x w * s) (X n' * val x w'))
    (hs : ∀ c < 4, x c * s = s * x c)
    (hw : GD (2 ^ 16) w) (hw' : GD (2 ^ 16) w') (hT : wBelow 4 tw = true) (htl : wLen tw < 2 ^ 16)
    (hS : GD (2 ^ 24) Sw) (hSc : X n * val x Sw * (X n)⁻¹ ∈ H) (ha : GD (2 ^ 30) a)
    (h1 : isOne F BS NB (wCat (wInv INVM tw) (wCat (wInv INVM w) (wCat (wInv INVM Sw) a))) =
      true) :
    CE H (X n * val x a * s) (X n' * val x (wCat w' tw)) ∧ GD (2 ^ 17) (wCat w' tw) := by
  obtain ⟨hTok, hTlt⟩ := wBelow_spec hT
  have gt : GD (2 ^ 16) tw := ⟨hTok, fun c hc => by have := hTlt c hc; omega, htl⟩
  obtain ⟨c1, e1⟩ := (hS.inv hinv).1.cat ha (by norm_num)
  obtain ⟨c2, e2⟩ := (hw.inv hinv).1.cat c1 (by norm_num)
  obtain ⟨c3, e3⟩ := (gt.inv hinv).1.cat c2 (by norm_num)
  obtain ⟨c4, e4⟩ := hw'.cat gt (by norm_num)
  refine ⟨?_, c4.mono (by norm_num)⟩
  have hv := val_one2 hone c3.lt h1
  rw [val_cat e3, val_cat e2, val_cat e1, (gt.inv hinv).2, (hw.inv hinv).2, (hS.inv hinv).2] at hv
  have ea : val x a = val x Sw * val x w * val x tw := by
    have := congrArg (fun z => val x Sw * (val x w * (val x tw * z))) hv
    simp only [mul_one] at this
    rw [mul_assoc, ← this]
    group
  have hth : val x tw * s = s * val x tw := evalWord_comm hs _ hTlt
  rw [val_cat e4, ea]
  have e5 : X n * (val x Sw * val x w * val x tw) * s =
      (X n * val x Sw * (X n)⁻¹) * (X n * val x w * s * val x tw) := by
    rw [show X n * val x w * s * val x tw = X n * val x w * (s * val x tw) by group, ← hth]
    group
  rw [e5, ← mul_assoc (X n')]
  exact (CE.of_left hSc _).trans (hfact.mul_right _)

variable (F INVM BS NB RD RW RA H x t) in
theorem tStep_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hT : ∀ c < 4, x c * t = t * x c)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r k a J : ℕ} (fwd : Bool) (hH : Hist2 RD RW RA H x t X r) (ha : GD (2 ^ 30) a)
    (hf : wsFail (tStep F INVM BS NB RD RW RA r k a J fwd).1 = 0) :
    CE H (X k * val x a * (if fwd = true then t else t⁻¹))
      (X (wsK (tStep F INVM BS NB RD RW RA r k a J fwd).1) *
        val x (tStep F INVM BS NB RD RW RA r k a J fwd).2) ∧
    GD (2 ^ 17) (tStep F INVM BS NB RD RW RA r k a J fwd).2 := by
  have hm : fld J 20 255 < 256 := fld_lt_succ _ _ _
  have hpath : ∀ m L, m < 256 → 0 < pathW INVM RD RW k m L r →
      GD (2 ^ 24) (pathW INVM RD RW k m L r - 1) ∧
        X k * val x (pathW INVM RD RW k m L r - 1) * (X k)⁻¹ ∈ H := by
    intro m L hm hS
    rw [pathW_eq2] at hS ⊢
    have hb : 1 + m * 2 ^ 16 ≤ 2 ^ 24 := by
      have : m * 2 ^ 16 ≤ 255 * 2 ^ 16 := Nat.mul_le_mul_right _ (by omega)
      norm_num at this ⊢; omega
    obtain ⟨h1, h2⟩ := path_spec2 hinv hH m L 1 1 Nat.one_pos GD.zero (by omega)
      (by show X k * val x 0 * (X k)⁻¹ ∈ H; rw [val_zero, mul_one, mul_inv_cancel]; exact H.one_mem)
      hS
    exact ⟨h1.mono hb, h2⟩
  have hTi : ∀ c < 4, x c * t⁻¹ = t⁻¹ * x c := fun c hc => inv_comm_of (hT c hc)
  cases fwd
  all_goals
    unfold tStep at hf ⊢
    simp only [sW_eq, brec_eq, ↓reduceIte, Bool.false_eq_true] at hf ⊢
    split_ifs at hf ⊢ with hc
    swap
    · exact absurd hf (by rw [wsBad_fail]; norm_num)
    simp only [kandB_iff] at hc
    obtain ⟨hfr, hfa, hk, hS, hT', h1⟩ := hc
    have hR := hH _ (Nat.blt_eq.mp hfr)
    have hfa' : dKind (RD (hNat J 20)) < 3 := Nat.blt_eq.mp hfa
    have hk' := Nat.eq_of_beq_eq_true hk
    obtain ⟨hSg, hSc⟩ := hpath _ _ hm (Nat.blt_eq.mp hS)
    rw [(wsMk_spec (by first | exact dN1_lt _ | exact dN2_lt _) (by norm_num) _).1]
    subst hk'
  · exact step_core2 F INVM BS NB H x hinv hone (ce_flip_t (hR.fact hfa')) hTi hR.ra hR.rw hT'
      (hWord_spec _).1 hSg hSc ha h1
  · exact step_core2 F INVM BS NB H x hinv hone (hR.fact hfa') hT hR.rw hR.ra hT'
      (hWord_spec _).1 hSg hSc ha h1

variable (INVM RD RW RA H x t) in
theorem eStep_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    {X : ℕ → G} {r k a J B : ℕ} (back : Bool) (hH : Hist2 RD RW RA H x t X r)
    (ha : GD B a) (hB : 2 ^ 16 + B ≤ 2 ^ 32)
    (hf : wsFail (eStep INVM RD RW r k a J back).1 = 0) :
    CE H (X k * val x a) (X (wsK (eStep INVM RD RW r k a J back).1) *
      val x (eStep INVM RD RW r k a J back).2) ∧
    GD (2 ^ 16 + B) (eStep INVM RD RW r k a J back).2 := by
  unfold eStep at hf ⊢
  simp only [sW_eq] at hf ⊢
  generalize (Bool.rec (motive := fun _ => ℕ) (fld J (nat_lit 20) (nat_lit 1))
    (Nat.sub (nat_lit 1) (fld J (nat_lit 20) (nat_lit 1))) back) = dir at hf ⊢
  obtain hd | hd : Nat.beq dir 0 = true ∨ Nat.beq dir 0 = false := by
    cases Nat.beq dir 0 <;> simp
  all_goals
    simp only [brec_eq, hd, ↓reduceIte, Bool.false_eq_true] at hf ⊢
    split_ifs at hf ⊢ with hc
    swap
    · exact absurd hf (by rw [wsBad_fail]; norm_num)
    simp only [kandB_iff] at hc
    obtain ⟨he, hq, hk⟩ := hc
    have hR := hH _ (Nat.blt_eq.mp he)
    unfold isEq at hq
    rw [kandB_iff] at hq
    have heq := hR.eq (Nat.le_of_ble_eq_true hq.1) (Nat.blt_eq.mp hq.2)
    rw [(wsMk_spec (by first | exact dN1_lt _ | exact dN2_lt _) (by norm_num) _).1]
    have hk' := Nat.eq_of_beq_eq_true hk
    subst hk'
  · obtain ⟨g, e⟩ := hR.rw.cat ha hB
    refine ⟨?_, g⟩
    rw [val_cat e]
    unfold CE at heq ⊢
    convert heq using 1
    group
  · obtain ⟨gi, ei⟩ := hR.rw.inv hinv
    obtain ⟨g, e⟩ := gi.cat ha hB
    refine ⟨?_, g⟩
    rw [val_cat e, ei]
    have := H.inv_mem heq
    unfold CE
    convert this using 1
    group

end Step

section Walk

variable {F RD RW RA WD : ℕ → ℕ} {INVM BS NB : ℕ} {H : Subgroup G} {x : ℕ → G} {t : G}

theorem prod_rec_eq {β : Sort*} (f : ℕ → ℕ → β) (p : WS) :
    Prod.rec (motive := fun _ => β) f p = f p.1 p.2 := rfl

theorem posStep_mk (r w pos : ℕ) (back : Bool) (s a : ℕ) :
    posStep F INVM BS NB RD RW RA r w pos back (s, a) =
      if Nat.beq (wsFail s) 1 = true then wsBad a
      else if Nat.blt (wAt w pos) 12 = true then
        (s, wCat a (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)))
      else if Nat.beq (wAt w pos) 14 = true then eStep INVM RD RW r (wsK s) a (wsJ s) back
      else tStep F INVM BS NB RD RW RA r (wsK s) a (wsJ s)
        (if back = true then Nat.beq (wAt w pos) 13 else Nat.beq (wAt w pos) 12) := by
  simp only [posStep, sW_eq, brec_eq]

theorem posStep_fail (r w pos : ℕ) (back : Bool) {st : WS} (h : wsFail st.1 = 1) :
    wsFail (posStep F INVM BS NB RD RW RA r w pos back st).1 = 1 := by
  obtain ⟨s, a⟩ := st
  rw [posStep_mk, if_pos (by simpa using h)]
  exact wsBad_fail a

theorem foldl_fail (r w : ℕ) (back : Bool) (ps : List ℕ) : ∀ {st : WS}, wsFail st.1 = 1 →
    wsFail (ps.foldl (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st).1 = 1 := by
  induction ps with
  | nil => exact fun h => h
  | cons p ps ih => exact fun h => ih (posStep_fail r w p back h)

@[expose] noncomputable def pval (v : ℕ → G) (w : ℕ) (back : Bool) (p : ℕ) : G :=
  if back = true then (v (wAt w p))⁻¹ else v (wAt w p)

variable (F INVM BS NB RD RW RA H x t) in
theorem posStep_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hT : ∀ c < 4, x c * t = t * x c)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    {X : ℕ → G} {r w pos B : ℕ} (back : Bool) (hH : Hist2 RD RW RA H x t X r)
    (hc : wAt w pos < 15) {st : WS}
    (hB1 : 2 ^ 17 ≤ B) (hB2 : B + 2 ^ 16 ≤ 2 ^ 30) (ha : GD B st.2)
    (hf : wsFail (posStep F INVM BS NB RD RW RA r w pos back st).1 = 0) :
    CE H (X (wsK st.1) * val x st.2 * pval v w back pos)
      (X (wsK (posStep F INVM BS NB RD RW RA r w pos back st).1) *
        val x (posStep F INVM BS NB RD RW RA r w pos back st).2) ∧
    GD (B + 2 ^ 16) (posStep F INVM BS NB RD RW RA r w pos back st).2 := by
  obtain ⟨s, a⟩ := st
  dsimp only at ha ⊢
  rw [posStep_mk] at hf ⊢
  unfold pval
  by_cases h1 : Nat.beq (wsFail s) 1 = true
  · rw [if_pos h1] at hf
    exact absurd hf (by rw [wsBad_fail]; norm_num)
  rw [if_neg h1] at hf ⊢
  by_cases h12 : Nat.blt (wAt w pos) 12 = true
  · rw [if_pos h12] at hf ⊢
    have hc12 : wAt w pos < 12 := Nat.blt_eq.mp h12
    have hd : (if back = true then ivL INVM (wAt w pos) else wAt w pos) < 12 := by
      split_ifs
      · exact (hinv _ hc12).1
      · exact hc12
    obtain ⟨o1, o2, o3⟩ := wOne_spec (c := if back = true then ivL INVM (wAt w pos) else wAt w pos)
      (by omega)
    have hO : GD 2 (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)) :=
      ⟨o2, by rw [o3]; simpa using hd, by omega⟩
    obtain ⟨g, e⟩ := ha.cat hO (by omega)
    refine ⟨CE.of_eq ?_, g.mono (by omega)⟩
    dsimp only
    rw [val_cat e, mul_assoc]
    congr 2
    rw [show val x (wOne (if back = true then ivL INVM (wAt w pos) else wAt w pos)) =
        x (if back = true then ivL INVM (wAt w pos) else wAt w pos) by
      rw [val, o3]; simp [evalWord]]
    cases back <;> simp [hv _ hc12, (hinv _ hc12).2]
  · rw [if_neg h12] at hf ⊢
    have hc12 : 12 ≤ wAt w pos := by
      have : ¬ wAt w pos < 12 := fun h => h12 (Nat.blt_eq.mpr h)
      omega
    by_cases h14 : Nat.beq (wAt w pos) 14 = true
    · rw [if_pos h14] at hf ⊢
      obtain ⟨hce, hgd⟩ := eStep_spec RD RW RA INVM H x t hinv back hH ha (by omega) hf
      refine ⟨?_, hgd.mono (by omega)⟩
      rw [Nat.eq_of_beq_eq_true h14, hv14, inv_one, ite_self, mul_one]
      exact hce
    · rw [if_neg h14] at hf ⊢
      have hc14 : wAt w pos ≠ 14 := fun h => h14 (by rw [h]; rfl)
      obtain ⟨hce, hgd⟩ := tStep_spec F RD RW RA INVM BS NB H x t hinv hT hone _ hH
        (ha.mono (by omega)) hf
      refine ⟨?_, hgd.mono (by omega)⟩
      convert hce using 2
      obtain hc' | hc' : wAt w pos = 12 ∨ wAt w pos = 13 := by omega
      all_goals rw [hc']
      all_goals cases back
      all_goals simp [hv12, hv13]

variable (F INVM BS NB RD RW RA H x t) in
theorem walk_list (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hT : ∀ c < 4, x c * t = t * x c)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    {X : ℕ → G} {r w : ℕ} (back : Bool) (hH : Hist2 RD RW RA H x t X r) (ps : List ℕ)
    (hps : ∀ p ∈ ps, wAt w p < 15) :
    ∀ (st : WS) (B : ℕ), 131072 ≤ B → B + 65536 * ps.length ≤ 1073741824 → GD B st.2 →
    wsFail (ps.foldl (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st).1 = 0 →
    CE H (X (wsK st.1) * val x st.2 * (ps.map (pval v w back)).prod)
      (X (wsK (ps.foldl (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st).1) *
        val x (ps.foldl (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st).2) ∧
    GD (B + 65536 * ps.length)
      (ps.foldl (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st).2 := by
  induction ps with
  | nil =>
    intro st B _ _ ha _
    exact ⟨CE.of_eq (by simp), by simpa using ha⟩
  | cons p ps ih =>
    intro st B hB1 hB2 ha hf
    simp only [List.foldl_cons, List.length_cons, List.map_cons, List.prod_cons] at hf hB2 ⊢
    have hB4 : B + 65536 + 65536 * ps.length ≤ 1073741824 :=
      le_of_eq_of_le (by ring) hB2
    have hB3 : B + 65536 ≤ 1073741824 := le_trans (Nat.le_add_right _ _) hB4
    have hf1 : wsFail (posStep F INVM BS NB RD RW RA r w p back st).1 = 0 := by
      have := wsFail_lt (posStep F INVM BS NB RD RW RA r w p back st).1
      by_contra hne
      have h1 := foldl_fail (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD)
        (RW := RW) (RA := RA) r w back ps (st := posStep F INVM BS NB RD RW RA r w p back st)
        (by omega)
      omega
    obtain ⟨c1, g1⟩ := posStep_spec F RD RW RA INVM BS NB H x t hinv hT hone v hv hv12 hv13 hv14
      back hH (hps p List.mem_cons_self) (le_trans (by norm_num) hB1) (le_trans (by norm_num) hB3)
      ha hf1
    obtain ⟨c2, g2⟩ := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)) _ (B + 65536)
      (Nat.le_add_right_of_le hB1) hB4 (g1.mono (le_of_eq (by norm_num))) hf
    refine ⟨?_, by
      rw [show B + 65536 * (ps.length + 1) = B + 65536 + 65536 * ps.length by ring]; exact g2⟩
    rw [← mul_assoc]
    exact (c1.mul_right _).trans c2

@[expose] noncomputable def wR2 (r w a n : ℕ) (back : Bool) (j : ℕ) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (posStep F INVM BS NB RD RW RA r w
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) back) back
          (Prod.mk s' x'))))) st)
    j

theorem walkRun_eq (r w a n : ℕ) (back : Bool) (st : WS) :
    walkRun F INVM BS NB RD RW RA r w a n back st =
      ((List.range' 0 n).map (fun o => if back = true then a - o else a + o)).foldl
        (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st := by
  have key : ∀ j, j ≤ n → ∀ st : WS,
      wR2 (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD) (RW := RW) (RA := RA)
        r w a n back j st =
      ((List.range' (n - j) j).map (fun o => if back = true then a - o else a + o)).foldl
        (fun st p => posStep F INVM BS NB RD RW RA r w p back st) st := by
    intro j
    induction j with
    | zero => intro _ st; rfl
    | succ j ih =>
      intro hj st
      obtain ⟨s, x⟩ := st
      have e : wR2 (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
          (RA := RA) r w a n back (j + 1) (s, x) =
          wR2 (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
          (RA := RA) r w a n back j (posStep F INVM BS NB RD RW RA r w
            (if back = true then a - (n - 1 - j) else a + (n - 1 - j)) back (s, x)) := by
        have e0 : wR2 (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
            (RA := RA) r w a n back (j + 1) (s, x) = sW s (fun s' => sW x (fun x' =>
              wR2 (F := F) (INVM := INVM) (BS := BS) (NB := NB) (RD := RD) (RW := RW)
                (RA := RA) r w a n back j (posStep F INVM BS NB RD RW RA r w
                  (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n 1) j))
                    (Nat.sub a (Nat.sub (Nat.sub n 1) j)) back) back (s', x')))) := rfl
        rw [e0, sW_eq, sW_eq, brec_eq]
        rfl
      rw [e, ih (by omega), show n - (j + 1) = n - 1 - j by omega,
        show n - j = n - 1 - j + 1 by omega, List.range'_succ]
      rfl
  have := key n le_rfl st
  rw [Nat.sub_self] at this
  exact this

theorem prod_split (f : ℕ → G) : ∀ (m s : ℕ),
    ((List.range' 0 m).map (fun o => (f (s + m - 1 - o))⁻¹)).prod =
      (((List.range' s m).map f).prod)⁻¹
  | 0, _ => by simp
  | m + 1, s => by
    have e1 : List.range' 0 (m + 1) = List.range' 0 m ++ [m] := by
      rw [List.range'_1_concat, Nat.zero_add]
    have e2 : List.range' s (m + 1) = s :: List.range' (s + 1) m := List.range'_succ
    rw [e1, e2, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      List.map_cons, List.prod_cons, mul_inv_rev, ← prod_split f m (s + 1)]
    congr 1
    · refine congrArg List.prod (List.map_congr_left fun o _ => ?_)
      rw [show s + (m + 1) - 1 - o = s + 1 + m - 1 - o by omega]
    · rw [show s + (m + 1) - 1 - m = s by omega]

theorem walk_prod (f : ℕ → G) {L g : ℕ} (hg : g < L) (h1 : ((List.range L).map f).prod = 1) :
    ((List.range' 0 g).map f).prod * f g =
      ((List.range' 0 (L - 1 - g)).map (fun o => (f (L - 1 - o))⁻¹)).prod := by
  have e1 : List.range L = List.range' 0 g ++ g :: List.range' (g + 1) (L - 1 - g) := by
    rw [List.range_eq_range', ← List.range'_succ]
    have := List.range'_append_1 (s := 0) (m := g) (n := L - 1 - g + 1)
    rw [Nat.zero_add] at this
    rw [this]
    congr 1
    omega
  have e2 := prod_split f (L - 1 - g) (g + 1)
  rw [show g + 1 + (L - 1 - g) - 1 = L - 1 by omega] at e2
  rw [e2]
  rw [e1, List.map_append, List.map_cons, List.prod_append, List.prod_cons, ← mul_assoc] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem wsK_wsMk {k : ℕ} (hk : k < 4096) (J : ℕ) : wsK (wsMk k 0 J) = k :=
  (wsMk_spec hk (by norm_num) J).1

theorem walk_finish {H : Subgroup G} {X : ℕ → G} {k1 k2 kf kb : ℕ} {a0 a0' af ab : G}
    {fw fb : ℕ → G} {L g a n : ℕ}
    (c1 : CE H (X k1 * a0 * (((List.range' 0 g).map
      (fun o => if false = true then 0 - o else 0 + o)).map fw).prod) (X kf * af))
    (c2 : CE H (X k2 * a0' * (((List.range' 0 n).map
      (fun o => if true = true then a - o else a + o)).map fb).prod) (X kb * ab))
    (hk : k1 = k2) (ha0 : a0 = a0') (hfb : ∀ p, fb p = (fw p)⁻¹) (hg : g < L)
    (ha : a = L - 1) (hn : n = L - 1 - g) (h1 : ((List.range L).map fw).prod = 1) :
    CE H (X kf * af * fw g) (X kb * ab) := by
  subst hk ha0 ha hn
  have e := walk_prod fw hg h1
  have ef : ((List.range' 0 g).map (fun o => if false = true then 0 - o else 0 + o)).map fw =
      (List.range' 0 g).map fw := by
    simp
  have eb : ((List.range' 0 (L - 1 - g)).map
      (fun o => if true = true then L - 1 - o else L - 1 + o)).map fb =
      (List.range' 0 (L - 1 - g)).map (fun o => (fw (L - 1 - o))⁻¹) := by
    simp [hfb, Function.comp_def]
  rw [ef] at c1
  rw [eb, ← e] at c2
  exact (c1.symm.mul_right _).trans (by simpa only [mul_assoc] using c2)

theorem walk_core (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    {X : ℕ → G} {r d c : ℕ} {sf sb : WS} {vg : G}
    (hRW : GD (2 ^ 16) (RW r)) (hRA : GD (2 ^ 16) (RA r))
    (gf : GD (2 ^ 29) sf.2) (gb : GD (2 ^ 29) sb.2)
    (key : CE H (X (wsK sf.1) * val x sf.2 * vg) (X (wsK sb.1) * val x sb.2))
    (hv12 : c = 12 → vg = t) (hv13 : c = 13 → vg = t⁻¹) (hv14 : c = 14 → vg = 1)
    (h : Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq c 14) (andB (Nat.beq (dKind d) 3)
        (andB (Nat.beq (wsK sf.1) (dN1 d)) (andB (Nat.beq (wsK sb.1) (dN2 d))
          (isOne F BS NB (wCat (wInv INVM (RW r)) (wCat sb.2 (wInv INVM sf.2))))))))
      (andB (Nat.beq (dKind d) 2)
        (Bool.rec (motive := fun _ => Bool)
          (andB (Nat.beq c 13)
            (andB (Nat.beq (wsK sb.1) (dN1 d)) (andB (Nat.beq (wsK sf.1) (dN2 d))
            (andB (isOne F BS NB (wCat (wInv INVM (RW r)) sb.2))
              (isOne F BS NB (wCat (wInv INVM (RA r)) sf.2))))))
          (andB (Nat.beq (wsK sf.1) (dN1 d)) (andB (Nat.beq (wsK sb.1) (dN2 d))
            (andB (isOne F BS NB (wCat (wInv INVM (RW r)) sf.2))
              (isOne F BS NB (wCat (wInv INVM (RA r)) sb.2)))))
          (Nat.beq c 12)))
      (Nat.blt c 14) = true) :
    (dKind d = 2 ∧ CE H (X (dN1 d) * val x (RW r) * t) (X (dN2 d) * val x (RA r))) ∨
    (dKind d = 3 ∧ CE H (X (dN1 d)) (X (dN2 d) * val x (RW r))) := by
  rw [brec_eq] at h
  by_cases h14 : Nat.blt c 14 = true
  · rw [if_pos h14, kandB_iff, brec_eq] at h
    obtain ⟨hk2, h⟩ := h
    left
    refine ⟨Nat.eq_of_beq_eq_true hk2, ?_⟩
    by_cases h12 : Nat.beq c 12 = true
    · rw [if_pos h12] at h
      simp only [kandB_iff] at h
      obtain ⟨hkf, hkb, h1f, h1b⟩ := h
      rw [hv12 (Nat.eq_of_beq_eq_true h12)] at key
      rw [← Nat.eq_of_beq_eq_true hkf, ← Nat.eq_of_beq_eq_true hkb,
        val_eq_of_isOne2 hinv hone hRW gf (by norm_num) h1f,
        val_eq_of_isOne2 hinv hone hRA gb (by norm_num) h1b]
      exact key
    · rw [if_neg h12] at h
      simp only [kandB_iff] at h
      obtain ⟨h13, hkb, hkf, h1b, h1f⟩ := h
      rw [hv13 (Nat.eq_of_beq_eq_true h13)] at key
      rw [← Nat.eq_of_beq_eq_true hkb, ← Nat.eq_of_beq_eq_true hkf,
        val_eq_of_isOne2 hinv hone hRW gb (by norm_num) h1b,
        val_eq_of_isOne2 hinv hone hRA gf (by norm_num) h1f]
      exact ce_flip_inv key
  · rw [if_neg h14] at h
    simp only [kandB_iff] at h
    obtain ⟨h14', hk3, hkf, hkb, h1⟩ := h
    right
    refine ⟨Nat.eq_of_beq_eq_true hk3, ?_⟩
    rw [hv14 (Nat.eq_of_beq_eq_true h14'), mul_one] at key
    obtain ⟨gi, ei⟩ := gf.inv hinv
    obtain ⟨g3, e3⟩ := gb.cat gi (by norm_num)
    have hv := val_eq_of_isOne2 hinv hone hRW g3 (by norm_num) h1
    rw [val_cat e3, ei] at hv
    rw [← Nat.eq_of_beq_eq_true hkf, ← Nat.eq_of_beq_eq_true hkb, hv]
    have := key.mul_right (val x sf.2)⁻¹
    rw [mul_inv_cancel_right] at this
    simpa only [mul_assoc] using this

variable (F INVM BS NB RD RW RA WD H x t) in
theorem walkOK_spec (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hT : ∀ c < 4, x c * t = t * x c)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
        fld BS (16 * i) 65535) → evalWord x w = 1)
    (v : ℕ → G) (hv : ∀ c < 12, v c = x c) (hv12 : v 12 = t) (hv13 : v 13 = t⁻¹)
    (hv14 : v 14 = 1)
    (hWD : ∀ i < 4096, wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ lst (WD i), c < 15) ∧
      evalWord v (lst (WD i)) = 1)
    {X : ℕ → G} {r d J : ℕ} (hH : Hist2 RD RW RA H x t X r) (hRW : GD (2 ^ 16) (RW r))
    (hRA : GD (2 ^ 16) (RA r)) (h : walkOK F INVM BS NB RD RW RA WD r d J = true) :
    (dKind d = 2 ∧ CE H (X (dN1 d) * val x (RW r) * t) (X (dN2 d) * val x (RA r))) ∨
    (dKind d = 3 ∧ CE H (X (dN1 d)) (X (dN2 d) * val x (RW r))) := by
  unfold walkOK at h
  simp only [sB_eq, prod_rec_eq, walkRun_eq, kandB_iff] at h
  obtain ⟨hh0, hg, hff, hfb, -, h⟩ := h
  obtain ⟨hL, hlt, hwv⟩ := hWD _ (land4095_lt J)
  generalize WD (Nat.land J 4095) = w at hL hlt hwv hg hff hfb h
  generalize Nat.land (hAfterWord (hDrop J 24)) 255 = g at hg hff hfb h
  have hgL : g < wLen w := Nat.blt_eq.mp hg
  replace hff := Nat.eq_of_beq_eq_true hff
  replace hfb := Nat.eq_of_beq_eq_true hfb
  have hi : fld J 12 4095 < 4096 := fld_lt_succ _ _ _
  have hat : ∀ p < wLen w, wAt w p < 15 := fun p hp =>
    hlt _ (List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩)
  have h0 : GD 131072 (hWord (hDrop J 24)) :=
    ⟨(wBelow_spec hh0).1, (wBelow_spec hh0).2, lt_trans (hWord_spec _).1 (by norm_num)⟩
  have hL' : wLen w < 4096 := by simpa using hL
  obtain ⟨c1, g1⟩ := walk_list F RD RW RA INVM BS NB H x t hinv hT hone v hv hv12 hv13 hv14
    false hH _ (by
      intro p hp
      simp only [List.mem_map, List.mem_range'_1] at hp
      obtain ⟨o, ho, rfl⟩ := hp
      exact hat _ (by simp only [Nat.sub_eq, Bool.false_eq_true, ↓reduceIte] at ho ⊢; omega))
    _ 131072 le_rfl (by simp only [List.length_map, List.length_range']; omega) h0 hff
  obtain ⟨c2, g2⟩ := walk_list F RD RW RA INVM BS NB H x t hinv hT hone v hv hv12 hv13 hv14
    true hH _ (by
      intro p hp
      simp only [List.mem_map, List.mem_range'_1] at hp
      obtain ⟨o, ho, rfl⟩ := hp
      exact hat _ (by simp only [Nat.sub_eq, ↓reduceIte] at ho ⊢; omega))
    _ 131072 le_rfl (by simp only [List.length_map, List.length_range', Nat.sub_eq]; omega) h0 hfb
  have h1 : ((List.range (wLen w)).map (pval v w false)).prod = 1 := by
    rw [← hwv]
    unfold evalWord lst
    rw [List.map_map]
    congr 1
  have key := walk_finish c1 c2 ((wsK_wsMk hi _).trans (wsK_wsMk hi _).symm) rfl
    (fun p => by simp [pval]) hgL rfl rfl h1
  exact walk_core hinv hone hRW hRA
    (g1.mono (by simp only [List.length_map, List.length_range']; omega))
    (g2.mono (by simp only [List.length_map, List.length_range', Nat.sub_eq]; omega)) key
    (fun e => by simp [pval, e, hv12]) (fun e => by simp [pval, e, hv13])
    (fun e => by simp [pval, e, hv14]) h

end Walk

end CFSG.Certificates.TwDce2.Walk

end

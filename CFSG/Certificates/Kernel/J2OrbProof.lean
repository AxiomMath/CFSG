module

public import Certificates.Data.Kernel.J2Orb
public import Certificates.Data.CFSGNative.J1.Vec
public import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.J2Orb

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.J1.Native

theorem band_iff {a b : Bool} : (Bool.rec (motive := fun _ => Bool) false b a) = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem forIn_inv {σ : Type} (f : Nat → σ → Id (ForInStep σ)) (I : Nat → σ → Prop) {N cap : Nat}
    (hN : N ≤ cap) (hstep : ∀ h < N, ∀ s, I h s → ∃ s', f h s = pure (.yield s') ∧ I (h + 1) s')
    (hstop : ∀ s, I N s → N < cap → f N s = pure (.done s)) :
    ∀ k ≤ N, ∀ s, I k s → I N (Id.run (forIn (List.range' k (cap - k)) s f)) := by
  intro k
  induction h : N - k generalizing k with
  | zero =>
    intro hk s hs
    have hkN : k = N := by omega
    subst hkN
    rcases Nat.eq_or_lt_of_le hN with he | hlt
    · have e0 : cap - k = 0 := by omega
      rw [e0]
      simpa using hs
    · obtain ⟨m, hm⟩ : ∃ m, cap - k = m + 1 := ⟨cap - k - 1, by omega⟩
      rw [hm, List.range'_succ, List.forIn_cons, hstop s hs hlt]
      simpa using hs
  | succ m ih =>
    intro hk s hs
    have hlt : k < N := by omega
    obtain ⟨s', hs1, hs2⟩ := hstep k hlt s hs
    obtain ⟨m', hm⟩ : ∃ m', cap - k = m' + 1 := ⟨cap - k - 1, by omega⟩
    rw [hm, List.range'_succ, List.forIn_cons, hs1]
    have e : m' = cap - (k + 1) := by omega
    simp only [pure_bind]
    rw [e]
    exact ih (k + 1) (by omega) (by omega) s' hs2

def eV : List Nat → Nat
  | [] => 0
  | x :: v => x + 8 * eV v

theorem codeL_shift : ∀ (v : List Nat) (s : Nat), (∀ x ∈ v, x < 8) →
    List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s (nat_lit 3)))) v s =
      2 ^ s * eV v
  | [], _, _ => by simp [eV]
  | x :: v, s, h => by
    have hx : x < 8 := h x List.mem_cons_self
    have ih := codeL_shift v (s + 3) fun y hy => h y (List.mem_cons_of_mem _ hy)
    change Nat.lor (Nat.shiftLeft x s) (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 3))) v (s + 3)) = _
    rw [ih, CFSG.KS.PackFld.shl_eq]
    have hlt : x * 2 ^ s < 2 ^ (s + 3) := by
      rw [Nat.pow_add]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos s) |>.trans_le
        (by rw [Nat.mul_comm])
    change x * 2 ^ s ||| 2 ^ (s + 3) * eV v = _
    rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hlt, eV, Nat.pow_add]
    ring

theorem codeL_eq {v : List Nat} (h : ∀ x ∈ v, x < 8) : codeL v = eV v := by
  have := codeL_shift v 0 h
  rw [Nat.pow_zero, Nat.one_mul] at this
  exact this

theorem eV_inj : ∀ {u v : List Nat}, u.length = v.length → (∀ x ∈ u, x < 8) →
    (∀ x ∈ v, x < 8) → eV u = eV v → u = v
  | [], [], _, _, _, _ => rfl
  | x :: u, y :: v, hl, hu, hv, he => by
    have hx := hu x List.mem_cons_self
    have hy := hv y List.mem_cons_self
    simp only [eV] at he
    have e1 : x = y := by omega
    have e2 : eV u = eV v := by omega
    rw [e1, eV_inj (by simpa using hl) (fun z hz => hu z (List.mem_cons_of_mem _ hz))
      (fun z hz => hv z (List.mem_cons_of_mem _ hz)) e2]

theorem pg_eV : ∀ (v : List Nat) (k : Nat), (∀ x ∈ v, x < 8) →
    pg (nat_lit 3) (nat_lit 7) (eV v) k = v.getD k 0
  | [], k, _ => by
    simp only [eV, List.getD_nil]
    change Nat.land (Nat.shiftRight 0 _) 7 = 0
    simp
  | x :: v, k, h => by
    have hx := h x List.mem_cons_self
    have ih := pg_eV v
    change Nat.land (Nat.shiftRight (x + 8 * eV v) (3 * k)) 7 = _
    rw [CFSG.KS.PackFld.shr_eq]
    change (x + 8 * eV v) / 2 ^ (3 * k) &&& (2 ^ 3 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    cases k with
    | zero => simp; omega
    | succ k =>
      have e : (x + 8 * eV v) / 2 ^ (3 * (k + 1)) = eV v / 2 ^ (3 * k) := by
        rw [show 3 * (k + 1) = 3 + 3 * k by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      have := ih k fun y hy => h y (List.mem_cons_of_mem _ hy)
      change Nat.land (Nat.shiftRight (eV v) (3 * k)) 7 = _ at this
      rw [CFSG.KS.PackFld.shr_eq] at this
      change eV v / 2 ^ (3 * k) &&& (2 ^ 3 - 1) = _ at this
      rw [Nat.and_two_pow_sub_one_eq_mod] at this
      rw [e, this]
      simp

theorem dotK_eq (p : Nat) {v : List Nat} (hv : ∀ x ∈ v, x < 8) :
    ∀ (r : List Nat) (k : Nat), k + r.length = v.length →
      List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
        (fun a _ ih k => Nat.add (Nat.mul a (pg (nat_lit 3) (nat_lit 7) (eV v) k))
          (ih (Nat.succ k))) r k = dotL r (v.drop k)
  | [], k, _ => by
    cases h : v.drop k <;> rfl
  | a :: r, k, hl => by
    have hk : k < v.length := by simp at hl; omega
    have ih := dotK_eq p hv r (k + 1) (by simp at hl ⊢; omega)
    change Nat.add (Nat.mul a (pg 3 7 (eV v) k)) (List.rec (motive := fun _ => Nat → Nat)
      (fun _ => 0) (fun a _ ih k => Nat.add (Nat.mul a (pg 3 7 (eV v) k)) (ih (Nat.succ k))) r
      (k + 1)) = _
    rw [ih, pg_eV v k hv, List.drop_eq_getElem_cons hk, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk, Option.getD_some]
    rfl

theorem mvK_codeL (p : Nat) {v : List Nat} (hv : ∀ x ∈ v, x < 8) :
    ∀ (X : List (List Nat)) (s : Nat), (∀ r ∈ X, r.length = v.length) →
      List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
        (fun r _ ih s => Nat.lor (Nat.shiftLeft (dotK p r (eV v)) s) (ih (Nat.add s (nat_lit 3))))
        X s =
      List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
        (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s (nat_lit 3)))) (mvL p X v) s
  | [], _, _ => rfl
  | r :: X, s, hX => by
    have ih := mvK_codeL p hv X (s + 3) fun r' hr' => hX r' (List.mem_cons_of_mem _ hr')
    change Nat.lor (Nat.shiftLeft (dotK p r (eV v)) s) _ =
      Nat.lor (Nat.shiftLeft (dotL r v % p) s) _
    have hd : dotK p r (eV v) = dotL r v % p := by
      unfold dotK
      rw [dotK_eq p hv r 0 (by simp [hX r List.mem_cons_self]), List.drop_zero]
      rfl
    rw [hd]
    congr 1

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = _
    rw [ih]
    rfl

theorem allLtL_iff (p : Nat) (v : List Nat) : allLtL p v = true ↔ ∀ x ∈ v, x < p := by
  induction v with
  | nil => simp [allLtL]
  | cons x v ih =>
    change (Bool.rec (motive := fun _ => Bool) false (allLtL p v) (Nat.blt x p)) = true ↔ _
    rw [band_iff, ih, Nat.blt_eq]
    simp

theorem rows_iff (p d : Nat) (X : List (List Nat)) :
    List.rec (motive := fun _ => Bool) true
      (fun r _ ih => Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false ih (allLtL p r)) (Nat.beq (lenK r) d)) X = true ↔
    ∀ r ∈ X, r.length = d ∧ ∀ x ∈ r, x < p := by
  induction X with
  | nil => simp
  | cons r X ih =>
    change (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false _
      (allLtL p r)) (Nat.beq (lenK r) d)) = true ↔ _
    rw [band_iff, band_iff, Nat.beq_eq, lenK_eq, allLtL_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem wfMK_iff (p d : Nat) (X : List (List Nat)) : wfMK p d X = true ↔
    X.length = d ∧ ∀ r ∈ X, r.length = d ∧ ∀ x ∈ r, x < p := by
  unfold wfMK
  rw [band_iff, Nat.beq_eq, lenK_eq, rows_iff]

def WF (d : Nat) (v : List Nat) : Prop := v.length = d ∧ ∀ x ∈ v, x < 8

theorem mvL_facts {p d : Nat} (hp8 : p ≤ 8) {X : List (List Nat)} (hX : wfMK p d X = true)
    {v : List Nat} (hv : WF d v) :
    WF d (mvL p X v) ∧ codeL (mvL p X v) = mvK p X (codeL v) := by
  obtain ⟨hXl, hXr⟩ := (wfMK_iff p d X).1 hX
  have hlt : ∀ x ∈ mvL p X v, x < 8 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    rcases Nat.eq_zero_or_pos p with hp | hp
    · obtain ⟨hrl, hre⟩ := hXr r hr
      cases r with
      | nil =>
        simp only [List.length_nil] at hrl
        subst hrl
        cases X with
        | nil => simp at hr
        | cons r' X => simp at hXl
      | cons y r => exact absurd (hre y List.mem_cons_self) (by omega)
    · have := Nat.mod_lt (dotL r v) hp
      omega
  refine ⟨⟨by simp [mvL, hXl], hlt⟩, ?_⟩
  rw [codeL_eq hv.2]
  exact (mvK_codeL p hv.2 X 0 fun r hr => (hXr r hr).1.trans hv.1.symm).symm

theorem stepC_ne {c a : Nat} (h : stepC c a ≠ 0) :
    (a < c ∧ stepC c a = c) ∨ (a = c ∧ stepC c a = c + 1) := by
  unfold stepC at *
  cases h0 : Nat.beq c 0
  · simp only [h0] at h ⊢
    cases h1 : Nat.blt a c
    · simp only [h1] at h ⊢
      cases h2 : Nat.beq a c
      · simp only [h2] at h
        exact absurd rfl h
      · right
        exact ⟨Nat.eq_of_beq_eq_true h2, rfl⟩
    · left
      exact ⟨Nat.blt_eq.mp h1, rfl⟩
  · simp only [h0] at h
    exact absurd rfl h

theorem stepC_le {c a : Nat} (h : stepC c a ≠ 0) : c ≤ stepC c a := by
  rcases stepC_ne h with ⟨-, e⟩ | ⟨-, e⟩ <;> omega

theorem bfsCnt_succ (h ALP BEP : Nat) : bfsCnt (h + 1) ALP BEP =
    if h < bfsCnt h ALP BEP then
      stepC (stepC (bfsCnt h ALP BEP) (pg 9 511 ALP h)) (pg 9 511 BEP h) else 0 := by
  change strictN (bfsCnt h ALP BEP) (fun c' => Bool.rec (motive := fun _ => Nat) 0
    (strictN (stepC c' (pg 9 511 ALP h)) fun c2 => stepC c2 (pg 9 511 BEP h)) (Nat.blt h c')) = _
  rw [CFSG.KS.PackFld.strictN_eqP]
  cases hb : Nat.blt h (bfsCnt h ALP BEP)
  · have : ¬ h < bfsCnt h ALP BEP := fun hh => by
      rw [Nat.blt_eq.mpr hh] at hb
      cases hb
    simp only [this, ↓reduceIte]
  · simp only [Nat.blt_eq.mp hb, ↓reduceIte]
    exact CFSG.KS.PackFld.strictN_eqP _ _

theorem bfsCnt_zero_up {ALP BEP : Nat} : ∀ h, bfsCnt h ALP BEP = 0 →
    ∀ k, bfsCnt (h + k) ALP BEP = 0 := by
  intro h hh k
  induction k with
  | zero => exact hh
  | succ k ih =>
    rw [← Nat.add_assoc, bfsCnt_succ, ih]
    simp

theorem bfsCnt_mono {ALP BEP N : Nat} (hN : bfsCnt N ALP BEP ≠ 0) :
    ∀ h ≤ N, bfsCnt h ALP BEP ≠ 0 ∧ bfsCnt h ALP BEP ≤ bfsCnt N ALP BEP := by
  intro h hh
  induction hk : N - h generalizing h with
  | zero => exact ⟨by rwa [show h = N by omega], by rw [show h = N by omega]⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (h + 1) (by omega) (by omega)
    rw [bfsCnt_succ] at ih1 ih2
    split at ih1
    · next hlt =>
      simp only [hlt, ↓reduceIte] at ih2
      have h1 : stepC (bfsCnt h ALP BEP) (pg 9 511 ALP h) ≠ 0 := fun e => by
        rw [e] at ih1
        exact ih1 (by unfold stepC; rfl)
      have := stepC_le h1
      have := stepC_le ih1
      exact ⟨by omega, by omega⟩
    · exact absurd rfl ih1

section Search

variable {p d cap N : Nat} {A B : List (List Nat)} {root : List Nat} {PTP ALP BEP : Nat}

noncomputable abbrev pt (d PTP i : Nat) : Nat :=
  pg (Nat.mul (nat_lit 3) d) (mask (Nat.mul (nat_lit 3) d)) PTP i

noncomputable abbrev ta (T i : Nat) : Nat := pg (nat_lit 9) (nat_lit 511) T i

theorem push_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt]

theorem push_eq {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i = a.size) :
    (a.push x)[i]! = x := by
  subst h
  rw [getElem!_pos (a.push x) a.size (by simp)]
  simp

structure Facts (p d cap N : Nat) (A B : List (List Nat)) (root : List Nat)
    (PTP ALP BEP : Nat) : Prop where
  p8 : p ≤ 8
  N1 : 1 ≤ N
  Ncap : N ≤ cap
  wA : wfMK p d A = true
  wB : wfMK p d B = true
  rlen : root.length = d
  rlt : ∀ x ∈ root, x < p
  r0 : codeL root = pt d PTP 0
  tab : ∀ i < N, ta ALP i < N ∧ ta BEP i < N ∧ mvK p A (pt d PTP i) = pt d PTP (ta ALP i) ∧
    mvK p B (pt d PTP i) = pt d PTP (ta BEP i)
  dist : ∀ i < N, ∀ j < i, pt d PTP i ≠ pt d PTP j
  cnt : bfsCnt N ALP BEP = N

theorem facts_of (h : orbK p d cap N A B root PTP ALP BEP = true) :
    Facts p d cap N A B root PTP ALP BEP := by
  unfold orbK at h
  rw [CFSG.KS.PackFld.strictB_eqP, CFSG.KS.PackFld.strictB_eqP] at h
  simp only [band_iff, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq, lenK_eq, allLtL_iff] at h
  obtain ⟨hp, hN1, hNc, -, hA, hB, hrl, hrt, hr0, htab, hdist, hcnt⟩ := h
  refine ⟨hp, hN1, hNc, hA, hB, hrl, hrt, hr0, fun i hi => ?_, fun i hi j hj => ?_, hcnt⟩
  · have := CFSG.KS.Raw.Orb.allN_iff.1 htab i hi
    simp only [CFSG.KS.PackFld.strictB_eqP, band_iff, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · have := CFSG.KS.Raw.Orb.allN_iff.1 hdist i hi
    rw [CFSG.KS.PackFld.strictB_eqP] at this
    have h2 := CFSG.KS.Raw.Orb.allN_iff.1 this j hj
    intro e
    change Bool.rec (motive := fun _ => Bool) true false (Nat.beq (pt d PTP i) (pt d PTP j)) =
      true at h2
    rw [Nat.beq_eq.mpr e] at h2
    cases h2

def MapInv (d PTP c : Nat) (idx : Std.HashMap (List Nat) Nat) (pts : Array (List Nat)) : Prop :=
  pts.size = c ∧ (∀ j < c, codeL pts[j]! = pt d PTP j ∧ WF d pts[j]!) ∧
    ∀ v j, idx[v]? = some j ↔ (j < c ∧ pts[j]! = v)

theorem pt_inj (F : Facts p d cap N A B root PTP ALP BEP) {i j : Nat} (hi : i < N) (hj : j < N)
    (h : pt d PTP i = pt d PTP j) : i = j := by
  rcases Nat.lt_trichotomy i j with hl | rfl | hl
  · exact absurd h.symm (F.dist j hj i hl)
  · rfl
  · exact absurd h (F.dist i hi j hl)

theorem wf_eq {d : Nat} {u v : List Nat} (hu : WF d u) (hv : WF d v) (h : codeL u = codeL v) :
    u = v := by
  rw [codeL_eq hu.2, codeL_eq hv.2] at h
  exact eV_inj (hu.1.trans hv.1.symm) hu.2 hv.2 h

theorem lookup_some (F : Facts p d cap N A B root PTP ALP BEP) {c : Nat} {idx pts}
    (M : MapInv d PTP c idx pts) (hc : c ≤ N) {w : List Nat} {t : Nat}
    (hw : codeL w = pt d PTP t) (ht : t < N) {j : Nat} (h : idx[w]? = some j) : j = t ∧ t < c := by
  obtain ⟨hj, hpj⟩ := (M.2.2 w j).1 h
  have e := (M.2.1 j hj).1
  rw [hpj, hw] at e
  have := pt_inj F ht (by omega) e
  exact ⟨this.symm, by omega⟩

theorem lookup_none {c : Nat} {idx pts}
    (M : MapInv d PTP c idx pts) {w : List Nat} {t : Nat}
    (hw : codeL w = pt d PTP t) (hwf : WF d w) (h : idx[w]? = none) (hs : stepC c t ≠ 0) :
    t = c ∧ stepC c t = c + 1 ∧ MapInv d PTP (c + 1) (idx.insert w c) (pts.push w) := by
  rcases stepC_ne hs with ⟨hlt, -⟩ | ⟨rfl, he⟩
  · exfalso
    have ht := M.2.1 t hlt
    have : pts[t]! = w := wf_eq ht.2 hwf (by rw [ht.1, hw])
    rw [(M.2.2 w t).2 ⟨hlt, this⟩] at h
    cases h
  · refine ⟨rfl, he, ?_, ?_, ?_⟩
    · rw [Array.size_push, M.1]
    · intro j hj
      rcases Nat.lt_or_ge j t with hj' | hj'
      · rw [push_lt (by rw [M.1]; exact hj')]
        exact M.2.1 j hj'
      · have : j = t := by omega
        subst this
        rw [push_eq (by rw [M.1])]
        exact ⟨hw, hwf⟩
    · intro v j
      rw [Std.HashMap.getElem?_insert]
      by_cases hv : w = v
      · subst hv
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨by omega, ?_⟩
          rw [push_eq (by rw [M.1])]
        · rintro ⟨hj, hpj⟩
          by_contra hne
          have hj' : j < t := by omega
          rw [push_lt (by rw [M.1]; exact hj')] at hpj
          rw [(M.2.2 w j).2 ⟨hj', hpj⟩] at h
          cases h
      · have hb : (w == v) = false := by simpa using hv
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [M.2.2 v j]
        constructor
        · rintro ⟨hj, hpj⟩
          refine ⟨by omega, ?_⟩
          rw [push_lt (by rw [M.1]; exact hj)]
          exact hpj
        · rintro ⟨hj, hpj⟩
          rcases Nat.lt_or_ge j t with hj' | hj'
          · rw [push_lt (by rw [M.1]; exact hj')] at hpj
            exact ⟨hj', hpj⟩
          · have : j = t := by omega
            subst this
            rw [push_eq (by rw [M.1])] at hpj
            exact absurd hpj hv

theorem ofFn_push (T k : Nat) :
    Array.ofFn (n := k + 1) (fun i => UInt32.ofNat (pg 9 511 T i.val)) =
      (Array.ofFn (n := k) fun i => UInt32.ofNat (pg 9 511 T i.val)).push
        (UInt32.ofNat (pg 9 511 T k)) := by
  rw [Array.ofFn_succ]
  rfl

theorem run_props {σ : Type} (f : Nat → σ → Id (ForInStep σ)) (I : Nat → σ → Prop) {N cap : Nat}
    (hN : N ≤ cap) (hstep : ∀ h < N, ∀ s, I h s → ∃ s', f h s = pure (.yield s') ∧ I (h + 1) s')
    (hstop : ∀ s, I N s → N < cap → f N s = pure (.done s)) (s0 : σ) (h0 : I 0 s0)
    (G : σ → Prop) (hG : ∀ s, I N s → G s) : G (Id.run (forIn (List.range' 0 cap) s0 f)) := by
  have := forIn_inv f I hN hstep hstop 0 (Nat.zero_le _) s0 h0
  rw [Nat.sub_zero] at this
  exact hG _ this

end Search

abbrev St : Type := Std.HashMap (List Nat) Nat × Array (List Nat) × Array Nat × Array Nat ×
  CFSG.Sporadic.Th.Native.Table × CFSG.Sporadic.Th.Native.Table

theorem orbBFS_sound_proved {p d cap N : Nat} {A B : List (List Nat)} {root : List Nat}
    {PTP ALP BEP : Nat} (h : orbK p d cap N A B root PTP ALP BEP = true) :
    (orbBFS p id A B root cap).alpha =
        Array.ofFn (n := N) (fun i => UInt32.ofNat (pg 9 511 ALP i.val)) ∧
      (orbBFS p id A B root cap).beta =
        Array.ofFn (n := N) (fun i => UInt32.ofNat (pg 9 511 BEP i.val)) := by
  have F := facts_of h
  have hR : ∀ k ≤ N, bfsCnt k ALP BEP ≠ 0 ∧ bfsCnt k ALP BEP ≤ N := fun k hk => by
    have := bfsCnt_mono (N := N) (ALP := ALP) (BEP := BEP) (by rw [F.cnt]; have := F.N1; omega) k hk
    rw [F.cnt] at this
    exact this
  dsimp only [orbBFS, Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  refine run_props _ (fun k (s : St) => MapInv d PTP (bfsCnt k ALP BEP) s.1 s.2.1 ∧
      s.2.2.2.2.1 = Array.ofFn (n := k) (fun i => UInt32.ofNat (pg 9 511 ALP i.val)) ∧
      s.2.2.2.2.2 = Array.ofFn (n := k) (fun i => UInt32.ofNat (pg 9 511 BEP i.val)))
    F.Ncap ?_ ?_ _ ?_ (fun (s : St) => s.2.2.2.2.1 = _ ∧ s.2.2.2.2.2 = _) fun s hs => hs.2
  · intro k hk s hs
    obtain ⟨idx, pts, par, lab, al, be⟩ := s
    obtain ⟨M, hal, hbe⟩ := hs
    dsimp only at M hal hbe ⊢
    obtain ⟨hk1, hk2⟩ := hR (k + 1) hk
    rw [bfsCnt_succ] at hk1 hk2
    split at hk1
    case isFalse => exact absurd rfl hk1
    rename_i hlt
    simp only [hlt, ↓reduceIte] at hk2
    have hc1 : stepC (bfsCnt k ALP BEP) (pg 9 511 ALP k) ≠ 0 := fun e => by
      rw [e] at hk1
      exact hk1 (by unfold stepC; rfl)
    have e2 : bfsCnt (k + 1) ALP BEP =
        stepC (stepC (bfsCnt k ALP BEP) (pg 9 511 ALP k)) (pg 9 511 BEP k) := by
      rw [bfsCnt_succ]
      simp only [hlt, ↓reduceIte]
    have hRk := (hR k (by omega)).2
    have hsz : pts.size = bfsCnt k ALP BEP := M.1
    have hkp : k < pts.size := by omega
    have hv := M.2.1 k hlt
    obtain ⟨ta1, tb1, tA, tB⟩ := F.tab k hk
    dsimp only [ta] at ta1 tb1 tA tB
    obtain ⟨hwa, hca⟩ := mvL_facts F.p8 F.wA hv.2
    obtain ⟨hwb, hcb⟩ := mvL_facts F.p8 F.wB hv.2
    rw [hv.1, tA] at hca
    rw [hv.1, tB] at hcb
    simp only [hkp, ↓reduceIte, id, Std.HashMap.get?_eq_getElem?]
    cases hA : idx[mvL p A pts[k]!]? with
    | some j =>
      obtain ⟨rfl, hjlt⟩ := lookup_some F M hRk hca ta1 hA
      have e1 : stepC (bfsCnt k ALP BEP) (pg 9 511 ALP k) = bfsCnt k ALP BEP := by
        rcases stepC_ne hc1 with ⟨-, e⟩ | ⟨e, -⟩
        · exact e
        · omega
      rw [e1] at e2 hk1
      cases hB : idx[mvL p B pts[k]!]? with
      | some j' =>
        obtain ⟨rfl, hjlt'⟩ := lookup_some F M hRk hcb tb1 hB
        have e3 : stepC (bfsCnt k ALP BEP) (pg 9 511 BEP k) = bfsCnt k ALP BEP := by
          rcases stepC_ne hk1 with ⟨-, e⟩ | ⟨e, -⟩
          · exact e
          · omega
        refine ⟨_, rfl, ?_, ?_, ?_⟩
        · rw [e2, e3]
          exact M
        · dsimp only
          rw [ofFn_push, hal]
        · dsimp only
          rw [ofFn_push, hbe]
      | none =>
        obtain ⟨e4, e5, M'⟩ := lookup_none M hcb hwb hB hk1
        refine ⟨_, rfl, ?_, ?_, ?_⟩
        · rw [e2, e5, hsz]
          exact M'
        · dsimp only
          rw [ofFn_push, hal]
        · dsimp only
          rw [ofFn_push, hbe, hsz, e4]
    | none =>
      obtain ⟨e4, e5, M1⟩ := lookup_none M hca hwa hA hc1
      rw [e5] at e2 hk1
      have hle : bfsCnt k ALP BEP + 1 ≤ N := by
        have := stepC_le hk1
        omega
      cases hB : (idx.insert (mvL p A pts[k]!) pts.size)[mvL p B pts[k]!]? with
      | some j' =>
        rw [hsz] at hB
        obtain ⟨rfl, hjlt'⟩ := lookup_some F M1 hle hcb tb1 hB
        have e3 : stepC (bfsCnt k ALP BEP + 1) (pg 9 511 BEP k) = bfsCnt k ALP BEP + 1 := by
          rcases stepC_ne hk1 with ⟨-, e⟩ | ⟨e, -⟩
          · exact e
          · omega
        refine ⟨_, rfl, ?_, ?_, ?_⟩
        · rw [e2, e3, hsz]
          exact M1
        · dsimp only
          rw [ofFn_push, hal, hsz, e4]
        · dsimp only
          rw [ofFn_push, hbe]
      | none =>
        rw [hsz] at hB
        obtain ⟨e6, e7, M2⟩ := lookup_none M1 hcb hwb hB hk1
        refine ⟨_, rfl, ?_, ?_, ?_⟩
        · rw [e2, e7, Array.size_push, hsz]
          exact M2
        · dsimp only
          rw [ofFn_push, hal, hsz, e4]
        · dsimp only
          rw [ofFn_push, hbe, Array.size_push, hsz, e6]
  · intro s hs hlt
    obtain ⟨idx, pts, par, lab, al, be⟩ := s
    obtain ⟨M, -, -⟩ := hs
    dsimp only at M ⊢
    have hn : ¬ N < pts.size := by rw [M.1, F.cnt]; omega
    simp only [hn, ↓reduceIte]
  · refine ⟨⟨rfl, fun j hj => ?_, fun v j => ?_⟩, rfl, rfl⟩
    · have hj0 : j = 0 := by
        change j < 1 at hj
        omega
      subst hj0
      have e : (#[root] : Array (List Nat))[0]! = root := rfl
      rw [e]
      exact ⟨F.r0, F.rlen, fun x hx => by have := F.rlt x hx; have := F.p8; omega⟩
    · rw [Std.HashMap.getElem?_insert]
      by_cases hv : root = v
      · subst hv
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq]
        constructor
        · rintro rfl
          refine ⟨?_, rfl⟩
          change 0 < 1
          omega
        · rintro ⟨hj, -⟩
          change j < 1 at hj
          omega
      · have hb : (root == v) = false := by simpa using hv
        simp only [hb, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_empty,
          reduceCtorEq, false_iff, not_and]
        intro hj hrv
        have hj0 : j = 0 := by
          change j < 1 at hj
          omega
        subst hj0
        exact hv hrv

end CFSG.KC.J2Orb

end

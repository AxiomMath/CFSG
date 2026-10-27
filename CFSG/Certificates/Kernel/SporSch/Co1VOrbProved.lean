module

public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import CFSG.Certificates.Kernel.VecKOrbit
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Th.Native CFSG.KS.Raw

theorem ptK_lt (T : Nat → Nat) (k : Nat) : ptK T k < 2 ^ 24 :=
  lt_of_le_of_lt (Nat.and_le_right (n := recK T k) (m := 16777215)) (by norm_num)

theorem iaK_le (T : Nat → Nat) (k : Nat) : iaK T k ≤ 131071 :=
  Nat.and_le_right

theorem ibK_le (T : Nat → Nat) (k : Nat) : ibK T k ≤ 131071 :=
  Nat.and_le_right

theorem imgStep_ok {T : Nat → Nat} {w i c : Nat} (h : imgStep T w i c < failC) :
    i ≤ c ∧ ptK T i = w ∧ imgStep T w i c = if i = c then c + 1 else c := by
  unfold imgStep at h ⊢
  simp only [Orb.nIf_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h ⊢
  by_cases h1 : i ≤ c ∧ ptK T i = w
  · rw [ite_eq_left h1]
    refine ⟨h1.1, h1.2, ?_⟩
    by_cases h2 : i = c
    · simp [h2]
    · simp [h2]
  · rw [ite_eq_right h1] at h
    exact absurd h (Nat.lt_irrefl _)

theorem bfsStep_fail {A B : Nat} {T : Nat → Nat} {n h c : Nat} (hc : ¬ c < failC) :
    bfsStep A B T n h c = failC := by
  unfold bfsStep
  simp only [Orb.nIf_eq, Nat.blt_eq, hc, ite_false]

theorem bfsStep_high {A B : Nat} {T : Nat → Nat} {n h c : Nat} (hc : c < failC) (hh : ¬ h < n) :
    bfsStep A B T n h c = c := by
  unfold bfsStep
  simp only [Orb.nIf_eq, Nat.blt_eq, hc, hh, ite_true, ite_false]

theorem bfsStep_ok {A B : Nat} {T : Nat → Nat} {n h c : Nat} (hc : c < failC) (hh : h < n)
    (hr : bfsStep A B T n h c < failC) :
    h < c ∧ imgStep T (actK A (ptK T h)) (iaK T h) c < failC ∧
      bfsStep A B T n h c =
        imgStep T (actK B (ptK T h)) (ibK T h) (imgStep T (actK A (ptK T h)) (iaK T h) c) := by
  unfold bfsStep at hr ⊢
  simp only [Orb.nIf_eq, Nat.blt_eq, hc, hh, ite_true, Orb.strictN_eq] at hr ⊢
  by_cases h1 : h < c
  · rw [ite_eq_left h1] at hr ⊢
    by_cases h2 : imgStep T (actK A (ptK T h)) (iaK T h) c < failC
    · rw [ite_eq_left h2] at hr ⊢
      exact ⟨h1, h2, rfl⟩
    · rw [ite_eq_right h2] at hr
      exact absurd hr (Nat.lt_irrefl _)
  · rw [ite_eq_right h1] at hr
    exact absurd hr (Nat.lt_irrefl _)

noncomputable def G (A B : Nat) (T : Nat → Nat) (n k : Nat) : Nat :=
  (List.range k).foldl (fun c i => bfsStep A B T n i c) 1

theorem G_succ (A B : Nat) (T : Nat → Nat) (n k : Nat) :
    G A B T n (k + 1) = bfsStep A B T n k (G A B T n k) := by
  unfold G
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem G_add (A B : Nat) (T : Nat → Nat) (n k m : Nat) :
    G A B T n (k + m) = (List.range m).foldl (fun c d => bfsStep A B T n (k + d) c)
      (G A B T n k) := by
  unfold G
  rw [List.range_add, List.foldl_append, List.foldl_map]

theorem foldl_fail (A B : Nat) (T : Nat → Nat) (n k : Nat) :
    ∀ (m c : Nat), ¬ c < failC →
      ¬ (List.range m).foldl (fun c d => bfsStep A B T n (k + d) c) c < failC := by
  intro m
  induction m with
  | zero => intro c hc; simpa using hc
  | succ m ih =>
    intro c hc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [bfsStep_fail (ih c hc)]
    exact Nat.lt_irrefl _

theorem G_slices {A B n NS L : Nat} {T C : Nat → Nat} (hc0 : C 0 = 1)
    (hb : ∀ s < NS, bfsSl A B T n (s * L) L (C s) (C (s + 1)) = true) :
    ∀ s ≤ NS, G A B T n (s * L) = C s := by
  intro s
  induction s with
  | zero => intro _; rw [Nat.zero_mul, hc0]; rfl
  | succ s ih =>
    intro hs
    have h := Nat.eq_of_beq_eq_true (hb s (by omega))
    rw [Orb.foldUp_eq] at h
    rw [Nat.succ_mul, G_add, ih (by omega)]
    exact h

noncomputable def sqT (T : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then iaK T (k / 2) else ibK T (k / 2)

noncomputable def cnt (T : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => if sqT T k = cnt T k then cnt T k + 1 else cnt T k

theorem sqT_even (T : Nat → Nat) (h : Nat) : sqT T (2 * h) = iaK T h := by
  unfold sqT
  rw [ite_eq_left (by omega)]
  congr 1
  omega

theorem sqT_odd (T : Nat → Nat) (h : Nat) : sqT T (2 * h + 1) = ibK T h := by
  unfold sqT
  rw [ite_eq_right (by omega)]
  congr 1
  omega

theorem cnt_succ_le (T : Nat → Nat) (k : Nat) : cnt T k ≤ cnt T (k + 1) ∧ cnt T (k + 1) ≤ cnt T k + 1 := by
  change cnt T k ≤ (if sqT T k = cnt T k then cnt T k + 1 else cnt T k) ∧
    (if sqT T k = cnt T k then cnt T k + 1 else cnt T k) ≤ cnt T k + 1
  split <;> omega

theorem cnt_mono (T : Nat → Nat) {j k : Nat} (h : j ≤ k) : cnt T j ≤ cnt T k := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    rw [this]
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h1 | h1
    · exact (ih (by omega)).trans (cnt_succ_le T k).1
    · rw [h1]

theorem lt_cnt_succ (T : Nat → Nat) {k : Nat} (h : sqT T k ≤ cnt T k) : sqT T k < cnt T (k + 1) := by
  change sqT T k < (if sqT T k = cnt T k then cnt T k + 1 else cnt T k)
  split <;> omega

structure Fact (A B : Nat) (T : Nat → Nat) (h : Nat) : Prop where
  lt : h < cnt T (2 * h)
  la : iaK T h ≤ cnt T (2 * h)
  lb : ibK T h ≤ cnt T (2 * h + 1)
  pa : ptK T (iaK T h) = actK A (ptK T h)
  pb : ptK T (ibK T h) = actK B (ptK T h)

theorem G_eq {A B : Nat} {T : Nat → Nat} {n N : Nat} (hN : n ≤ N)
    (hall : ∀ k ≤ N, G A B T n k < failC) :
    ∀ h ≤ n, G A B T n h = cnt T (2 * h) ∧ ∀ j < h, Fact A B T j := by
  intro h
  induction h with
  | zero => intro _; exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ h ih =>
    intro hh
    obtain ⟨hG, hF⟩ := ih (by omega)
    have hc := hall h (by omega)
    have hr := hall (h + 1) (by omega)
    rw [hG] at hc
    rw [G_succ, hG] at hr
    obtain ⟨h1, h2, h3⟩ := bfsStep_ok hc (by omega) hr
    obtain ⟨a1, a2, a3⟩ := imgStep_ok h2
    have e1 : imgStep T (actK A (ptK T h)) (iaK T h) (cnt T (2 * h)) = cnt T (2 * h + 1) := by
      rw [a3]
      change _ = if sqT T (2 * h) = cnt T (2 * h) then cnt T (2 * h) + 1 else cnt T (2 * h)
      rw [sqT_even]
    rw [h3, e1] at hr
    obtain ⟨b1, b2, b3⟩ := imgStep_ok hr
    refine ⟨?_, fun j hj => ?_⟩
    · rw [G_succ, hG, h3, e1, b3]
      have e : 2 * (h + 1) = 2 * h + 1 + 1 := by omega
      rw [e]
      change _ = if sqT T (2 * h + 1) = cnt T (2 * h + 1) then cnt T (2 * h + 1) + 1
        else cnt T (2 * h + 1)
      rw [sqT_odd]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact hF j hj
      · subst hj
        exact ⟨h1, a1, e1 ▸ b1, a2, b2⟩

noncomputable def foT (T : Nat → Nat) (y : Nat) : Nat := by
  classical
  exact if h : ∃ k, y < cnt T (k + 1) then Nat.find h else 0

theorem foT_spec {T : Nat → Nat} {y : Nat} (h : ∃ k, y < cnt T (k + 1)) :
    y < cnt T (foT T y + 1) ∧ ∀ k < foT T y, ¬ y < cnt T (k + 1) := by
  classical
  unfold foT
  rw [dite_eq_left h]
  exact ⟨Nat.find_spec h, fun k hk => Nat.find_min h hk⟩

theorem foT_le {T : Nat → Nat} {y k : Nat} (h : y < cnt T (k + 1)) : foT T y ≤ k := by
  have hs := foT_spec ⟨k, h⟩
  by_contra hc
  exact hs.2 k (by omega) h

theorem foT_cnt {T : Nat → Nat} {y : Nat} (hy : 1 ≤ y) (h : ∃ k, y < cnt T (k + 1)) :
    cnt T (foT T y) = y ∧ sqT T (foT T y) = y := by
  obtain ⟨h1, h2⟩ := foT_spec h
  have hle : cnt T (foT T y) ≤ y := by
    rcases Nat.eq_zero_or_pos (foT T y) with h0 | h0
    · rw [h0]
      exact hy
    · have := h2 (foT T y - 1) (by omega)
      rw [Nat.sub_add_cancel h0] at this
      omega
  have h3 := cnt_succ_le T (foT T y)
  have e : cnt T (foT T y) = y := by omega
  refine ⟨e, ?_⟩
  by_contra hne
  have : cnt T (foT T y + 1) = cnt T (foT T y) := by
    change (if sqT T (foT T y) = cnt T (foT T y) then cnt T (foT T y) + 1 else cnt T (foT T y)) = _
    rw [ite_eq_right (by rw [e]; exact hne)]
  omega

theorem perm_at {S T : Nat → Nat} {n NS L : Nat} (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) {k : Nat} (hk : k < n) :
    msK S k < n ∧ invK S k < n ∧ invK S (msK S k) = k ∧ msK S (invK S k) = k ∧
      (k + 1 < n → ptK T (msK S k) < ptK T (msK S (k + 1))) := by
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hL
      omega
    · exact h
  have hs : k / L < NS := by
    rw [Nat.div_lt_iff_lt_mul hL0]
    omega
  have h := Orb.allN_iff.1 (hp (k / L) hs) (k % L) (Nat.mod_lt _ hL0)
  have ek : Nat.add (k / L * L) (k % L) = k := Nat.div_add_mod' k L
  rw [Orb.strictB_eq, ek] at h
  simp only [Orb.bAnd_eq, Orb.strictB_eq] at h
  simp only [Orb.bIf_eq, Nat.blt_eq, Nat.beq_eq, hk, ite_true, Bool.and_eq_true,
    Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun hk1 => ?_⟩
  rw [ite_eq_left hk1] at h5
  simpa using h5

theorem sorted_mono {S T : Nat → Nat} {n NS L : Nat} (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) :
    ∀ x y, x < y → y < n → ptK T (msK S x) < ptK T (msK S y) := by
  intro x y hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    have h := (perm_at hL hp (k := y) (by omega)).2.2.2.2 hy
    rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h1 | h1
    · exact (ih h1 (by omega)).trans h
    · rw [h1]
      exact h

theorem ptK_inj {S T : Nat → Nat} {n NS L : Nat} (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) :
    ∀ i < n, ∀ j < n, ptK T i = ptK T j → i = j := by
  intro i hi j hj e
  obtain ⟨-, hi2, -, hi4, -⟩ := perm_at hL hp hi
  obtain ⟨-, hj2, -, hj4, -⟩ := perm_at hL hp hj
  have hm := sorted_mono hL hp
  have hk : invK S i = invK S j := by
    rcases Nat.lt_trichotomy (invK S i) (invK S j) with h1 | h1 | h1
    · have := hm _ _ h1 hj2
      rw [hi4, hj4] at this
      omega
    · exact h1
    · have := hm _ _ h1 hi2
      rw [hi4, hj4] at this
      omega
  rw [← hi4, ← hj4, hk]

theorem bsK_zero (T S : Nat → Nat) (v lo len : Nat) : bsK T S v 0 lo len = lo := rfl

theorem bsK_succ (T S : Nat → Nat) (v f lo len : Nat) :
    bsK T S v (f + 1) lo len = if len = 0 then lo else
      if ptK T (msK S (lo + len / 2)) < v then bsK T S v f (lo + len / 2 + 1) (len - len / 2 - 1)
      else bsK T S v f lo (len / 2) := by
  change nIf(Nat.beq len 0, lo, strictN (Nat.shiftRight len 1) (fun h =>
      nIf(Nat.blt (ptK T (msK S (Nat.add lo h))) v,
        bsK T S v f (Nat.succ (Nat.add lo h)) (Nat.sub (Nat.sub len h) 1), bsK T S v f lo h))) = _
  have e : Nat.shiftRight len 1 = len / 2 ^ 1 := Nat.shiftRight_eq_div_pow len 1
  rw [Orb.strictN_eq, e, Nat.pow_one]
  simp only [Orb.nIf_eq, Nat.beq_eq, Nat.blt_eq, Nat.succ_eq_add_one]
  rfl

theorem bsK_spec {S T : Nat → Nat} {n : Nat} (v : Nat)
    (hmono : ∀ x y, x ≤ y → y < n → ptK T (msK S x) ≤ ptK T (msK S y)) :
    ∀ (f lo len : Nat), len < 2 ^ f → lo + len ≤ n →
      lo ≤ bsK T S v f lo len ∧ bsK T S v f lo len ≤ lo + len ∧
      (∀ q, lo ≤ q → q < bsK T S v f lo len → ptK T (msK S q) < v) ∧
      (∀ q, bsK T S v f lo len ≤ q → q < lo + len → v ≤ ptK T (msK S q)) := by
  intro f
  induction f with
  | zero =>
    intro lo len hlen _
    have : len = 0 := by omega
    subst this
    rw [bsK_zero]
    exact ⟨le_refl _, by omega, fun q h1 h2 => by omega, fun q h1 h2 => by omega⟩
  | succ f ih =>
    intro lo len hlen hn
    rw [bsK_succ]
    by_cases h0 : len = 0
    · rw [ite_eq_left h0]
      exact ⟨le_refl _, by omega, fun q h1 h2 => by omega, fun q h1 h2 => by omega⟩
    rw [ite_eq_right h0]
    have hh : len / 2 < len := Nat.div_lt_self (by omega) (by omega)
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hc : ptK T (msK S (lo + len / 2)) < v
    · rw [ite_eq_left hc]
      obtain ⟨r1, r2, r3, r4⟩ := ih (lo + len / 2 + 1) (len - len / 2 - 1) (by omega) (by omega)
      refine ⟨by omega, by omega, fun q h1 h2 => ?_, fun q h1 h2 => r4 q h1 (by omega)⟩
      by_cases hq : lo + len / 2 + 1 ≤ q
      · exact r3 q hq h2
      · exact lt_of_le_of_lt (hmono q (lo + len / 2) (by omega) (by omega)) hc
    · rw [ite_eq_right hc]
      obtain ⟨r1, r2, r3, r4⟩ := ih lo (len / 2) (by omega) (by omega)
      refine ⟨r1, by omega, r3, fun q h1 h2 => ?_⟩
      by_cases hq : q < lo + len / 2
      · exact r4 q h1 hq
      · exact le_trans (by omega) (hmono (lo + len / 2) q (by omega) (by omega))

theorem memK_iff {S T : Nat → Nat} {n NS L : Nat} (hn : n < 131072) (hL : n ≤ NS * L)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) (v : Nat) :
    memK T S n v = true ↔ ∃ i < n, ptK T i = v := by
  have hmono : ∀ x y, x ≤ y → y < n → ptK T (msK S x) ≤ ptK T (msK S y) := by
    intro x y hxy hy
    rcases Nat.lt_or_eq_of_le hxy with h | h
    · exact le_of_lt (sorted_mono hL hp x y h hy)
    · rw [h]
  obtain ⟨r1, r2, r3, r4⟩ := bsK_spec v hmono 18 0 n (by omega) (by omega)
  unfold memK
  rw [Orb.strictB_eq]
  simp only [Orb.bIf_eq, Nat.blt_eq]
  constructor
  · intro h
    by_cases hlo : bsK T S v 18 0 n < n
    · rw [ite_eq_left hlo] at h
      exact ⟨msK S (bsK T S v 18 0 n), (perm_at hL hp hlo).1, Nat.eq_of_beq_eq_true h⟩
    · rw [ite_eq_right hlo] at h
      exact absurd h Bool.false_ne_true
  · rintro ⟨i, hi, e⟩
    obtain ⟨-, hr, -, hr4, -⟩ := perm_at hL hp hi
    have hq : ptK T (msK S (invK S i)) = v := by rw [hr4, e]
    have hle : bsK T S v 18 0 n ≤ invK S i := by
      by_contra hc
      have := r3 (invK S i) (Nat.zero_le _) (by omega)
      omega
    have hlo : bsK T S v 18 0 n < n := by omega
    rw [ite_eq_left hlo]
    have h1 := r4 (bsK T S v 18 0 n) (le_refl _) (by omega)
    have h2 := hmono _ _ hle hr
    rw [hq] at h2
    have e : ptK T (msK S (bsK T S v 18 0 n)) = v := by omega
    rw [e]
    exact Nat.beq_refl v

def pIns (t : Table) (h : Nat) (s : Array Nat × Nat) : Array Nat × Nat :=
  if (ap t h == s.2) = true then (s.1.set! s.2 h, s.2 + 1) else s

theorem forIn_yield_foldl {σ : Type} (g : σ → Nat → σ) (f : Nat → σ → Id (ForInStep σ))
    (hf : ∀ h s, f h s = pure (.yield (g s h))) :
    ∀ (l : List Nat) (init : σ), (forIn l init f : Id σ) = pure (l.foldl g init) := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, hf, List.foldl_cons]
    exact ih _

theorem parentsOf_eq (O : VOrbit) (n : Nat) :
    parentsOf O n = ((List.range n).foldl (fun s h => pIns O.beta h (pIns O.alpha h s))
      (Array.replicate n 0, 1)).1 := by
  unfold parentsOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [forIn_yield_foldl (fun s h => pIns O.beta h (pIns O.alpha h s))]
  · rfl
  · intro h s
    unfold pIns
    by_cases h1 : (ap O.alpha h == s.2) = true
    · by_cases h2 : (ap O.beta h == s.2 + 1) = true
      · simp only [h1, h2, ↓reduceIte]
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    · by_cases h2 : (ap O.beta h == s.2) = true
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

theorem pIns_inv {t : Table} {h x n c : Nat} {par : Array Nat} (Q : Nat → Nat → Prop)
    (hx : ap t h = x) (hxc : x ≤ c) (hhc : h < c) (hc' : (if x = c then c + 1 else c) ≤ n)
    (hsz : par.size = n) (hI : ∀ j, 1 ≤ j → j < c → par[j]! < j ∧ Q j par[j]!) (hQ : Q x h) :
    (pIns t h (par, c)).2 = (if x = c then c + 1 else c) ∧ (pIns t h (par, c)).1.size = n ∧
      ∀ j, 1 ≤ j → j < (pIns t h (par, c)).2 →
        (pIns t h (par, c)).1[j]! < j ∧ Q j (pIns t h (par, c)).1[j]! := by
  unfold pIns
  by_cases hxe : x = c
  · have hb : (ap t h == (par, c).2) = true := by rw [hx, hxe]; exact beq_self_eq_true c
    simp only [hb, ite_true, hxe] at hc' ⊢
    refine ⟨by simp, by rw [Array.size_set!, hsz], fun j hj1 hj2 => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj | hj
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact hI j hj1 hj
    · subst hj
      rw [Array.getElem!_set!_self _ _ _ (by omega)]
      exact ⟨hhc, hxe ▸ hQ⟩
  · have hb : (ap t h == (par, c).2) = false := by
      rw [hx]
      exact beq_false_of_ne hxe
    simp only [hb, Bool.false_eq_true, ite_false, hxe]
    exact ⟨by simp, hsz, hI⟩

theorem arr_get (p : Nat → Nat) {m y : Nat} (hy : y < m) :
    ((List.range m).map p).toArray[y]! = p y := by
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

theorem ap_arr {n : Nat} (f : Nat → Nat) (hf : ∀ i < n, f i < n) (hn : n < 2 ^ 32) {i : Nat}
    (hi : i < n) : ap ((List.range n).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
  unfold ap
  rw [getElem!_pos _ i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := hf i hi; omega)

theorem allIn_iff' {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' h1] using this
  · intro h ⟨k, hk⟩ _
    exact h (lo + k) (by omega) (by omega)

theorem vorbK_sound_proved {A B v₀ n NS L : Nat} {T S C : Nat → Nat}
    (hr : ptK T 0 = v₀) (hn0 : 0 < n) (hn : n < 131072) (hL : n ≤ NS * L)
    (hc0 : C 0 = 1) (hcN : C NS = n)
    (hb : ∀ s < NS, bfsSl A B T n (s * L) L (C s) (C (s + 1)) = true)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) :
    enumOK (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B)) v₀ n
        (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B))
          v₀ n) = true ∧
      (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B))
          v₀ n).pts.size = n ∧
      (∀ i < n, (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A))
          (transposeRows 24 (unpack 24 24 B)) v₀ n).pts[i]! = ptK T i) ∧
      ∀ v, ((List.range n).any fun i => (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A))
          (transposeRows 24 (unpack 24 24 B)) v₀ n).pts[i]! == v) = memK T S n v := by
  have hGN : G A B T n (NS * L) = n := by rw [G_slices hc0 hb NS (le_refl _), hcN]
  have hall : ∀ k ≤ NS * L, G A B T n k < failC := by
    intro k hk
    by_contra hc
    have := foldl_fail A B T n k (NS * L - k) _ hc
    rw [← G_add, Nat.add_sub_cancel' hk, hGN] at this
    exact this (lt_of_lt_of_le hn (by unfold failC; decide))
  have hhigh : ∀ m, n + m ≤ NS * L → G A B T n (n + m) = G A B T n n := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [← Nat.add_assoc, G_succ, bfsStep_high (hall _ (by omega)) (by omega), ih (by omega)]
  obtain ⟨hGn, hF⟩ := G_eq hL hall n (le_refl _)
  have hcn : cnt T (2 * n) = n := by
    rw [← hGn, ← hhigh (NS * L - n) (by omega), Nat.add_sub_cancel' hL, hGN]
  have hcle : ∀ k ≤ 2 * n, cnt T k ≤ n := fun k hk => hcn ▸ cnt_mono T hk
  have hfA : ∀ h < n, iaK T h < cnt T (2 * h + 1) := by
    intro h hh
    have := lt_cnt_succ T (k := 2 * h) (by rw [sqT_even]; exact (hF h hh).la)
    rwa [sqT_even] at this
  have hfB : ∀ h < n, ibK T h < cnt T (2 * h + 1 + 1) := by
    intro h hh
    have := lt_cnt_succ T (k := 2 * h + 1) (by rw [sqT_odd]; exact (hF h hh).lb)
    rwa [sqT_odd] at this
  have haN : ∀ h < n, iaK T h < n := fun h hh => lt_of_lt_of_le (hfA h hh) (hcle _ (by omega))
  have hbN : ∀ h < n, ibK T h < n := fun h hh => lt_of_lt_of_le (hfB h hh) (hcle _ (by omega))
  have hex : ∀ y < n, ∃ k, y < cnt T (k + 1) := fun y hy =>
    ⟨2 * n - 1, by rw [Nat.sub_add_cancel (by omega), hcn]; exact hy⟩
  have hcA := ActL.vecMulN_unpack A
  have hcB := ActL.vecMulN_unpack B
  have hn30 : n < 2 ^ 30 := lt_trans hn (by norm_num)
  have hO := CFSG.KC.VecK.vOrbitBFS_sim (d := 24) (cA := transposeRows 24 (unpack 24 24 A))
    (cB := transposeRows 24 (unpack 24 24 B)) (p := ptK T) (a := iaK T) (b := ibK T)
    (fo := foT T) (sq := sqT T) hn0 hn30 (fun h _ => ptK_lt T h) haN hbN
    (fun h hh => by rw [hcA, (hF h hh).pa]) (fun h hh => by rw [hcB, (hF h hh).pb])
    (ptK_inj hL hp) (sqT_even T) (sqT_odd T) (fun y hy1 hyn => ?_) (fun y hy1 hyn => ?_)
    (fun h hh => Or.inr (foT_le (hfA h hh))) (fun h hh => Or.inr (foT_le (hfB h hh)))
  rotate_left
  · obtain ⟨e1, e2⟩ := foT_cnt hy1 (hex y hyn)
    have hk : foT T y ≤ 2 * n - 1 := foT_le (by rw [Nat.sub_add_cancel (by omega), hcn]; exact hyn)
    have hlt := (hF (foT T y / 2) (by omega)).lt
    have hm := cnt_mono T (j := 2 * (foT T y / 2)) (k := foT T y) (by omega)
    exact ⟨by omega, e2⟩
  · obtain ⟨e1, -⟩ := foT_cnt hy1 (hex y (by omega))
    obtain ⟨e3, -⟩ := foT_cnt (by omega) (hex (y + 1) hyn)
    by_contra hc
    have := cnt_mono T (j := foT T (y + 1)) (k := foT T y) (by omega)
    omega
  rw [hr] at hO
  rw [hO]
  have hget : ∀ i < n, ((List.range n).map (ptK T)).toArray[i]! = ptK T i :=
    fun i hi => arr_get (ptK T) hi
  have hapA := fun i (hi : i < n) => ap_arr (iaK T) haN (by omega) hi
  have hapB := fun i (hi : i < n) => ap_arr (ibK T) hbN (by omega) hi
  have hsz : ((List.range n).map (ptK T)).toArray.size = n := by simp
  refine ⟨?_, hsz, hget, fun v => ?_⟩
  · unfold enumOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨?_, by rw [hget 0 hn0, hr]⟩, ?_⟩
    · unfold vOrbitOK
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨⟨⟨hsz, by simp⟩, by simp⟩, CFSG.KS.TW.allIn_iff.2 fun i hi => ?_⟩
      have hpos := CFSG.KC.PosTable.posTable_get (d := 24)
        (pts := ((List.range n).map (ptK T)).toArray)
        (fun j hj => by rw [hget j (by omega)]; exact ptK_lt T j)
        (fun j hj k hk e => ptK_inj hL hp j (by omega) k (by omega)
          (by rwa [hget j (by omega), hget k (by omega)] at e))
        (by omega) (i := i) (by omega)
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨by rw [hget i hi]; exact ptK_lt T i, hpos⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [hapA i hi]; exact haN i hi
      · rw [hapA i hi, hget _ (haN i hi), hget i hi, hcA, (hF i hi).pa]
      · rw [hapB i hi]; exact hbN i hi
      · rw [hapB i hi, hget _ (hbN i hi), hget i hi, hcB, (hF i hi).pb]
    · rw [parentsOf_eq]
      let Q : Nat → Nat → Prop := fun j p => iaK T p = j ∨ ibK T p = j
      have key : ∀ k ≤ n,
          let s := (List.range k).foldl (fun s h => pIns ((List.range n).map fun h =>
            UInt32.ofNat (ibK T h)).toArray h (pIns ((List.range n).map fun h =>
            UInt32.ofNat (iaK T h)).toArray h s)) (Array.replicate n 0, 1)
          s.2 = cnt T (2 * k) ∧ s.1.size = n ∧ ∀ j, 1 ≤ j → j < s.2 → s.1[j]! < j ∧ Q j s.1[j]! := by
        intro k
        induction k with
        | zero => intro _; exact ⟨rfl, by simp, fun j h1 h2 => by change j < 1 at h2; omega⟩
        | succ k ih =>
          intro hk
          obtain ⟨i1, i2, i3⟩ := ih (by omega)
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          generalize ((List.range k).foldl _ (Array.replicate n 0, 1)) = s at i1 i2 i3 ⊢
          obtain ⟨par, c⟩ := s
          dsimp only at i1 i2 i3
          subst i1
          have F := hF k (by omega)
          have e1 : (if iaK T k = cnt T (2 * k) then cnt T (2 * k) + 1 else cnt T (2 * k)) =
              cnt T (2 * k + 1) := by
            change _ = if sqT T (2 * k) = cnt T (2 * k) then cnt T (2 * k) + 1 else cnt T (2 * k)
            rw [sqT_even]
          have e2 : (if ibK T k = cnt T (2 * k + 1) then cnt T (2 * k + 1) + 1
              else cnt T (2 * k + 1)) = cnt T (2 * (k + 1)) := by
            have e : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
            rw [e]
            change _ = if sqT T (2 * k + 1) = cnt T (2 * k + 1) then cnt T (2 * k + 1) + 1
              else cnt T (2 * k + 1)
            rw [sqT_odd]
          obtain ⟨j1, j2, j3⟩ := pIns_inv Q (hapA k (by omega)) F.la F.lt
            (by rw [e1]; exact hcle _ (by omega)) i2 i3 (Or.inl rfl)
          rw [e1] at j1
          generalize pIns _ k (par, cnt T (2 * k)) = s' at j1 j2 j3 ⊢
          obtain ⟨par', c'⟩ := s'
          dsimp only at j1 j2 j3
          subst j1
          obtain ⟨k1, k2, k3⟩ := pIns_inv Q (hapB k (by omega)) F.lb
            (lt_of_lt_of_le F.lt (cnt_succ_le T _).1) (by rw [e2]; exact hcle _ (by omega)) j2 j3
            (Or.inr rfl)
          rw [e2] at k1
          exact ⟨k1, k2, k3⟩
      obtain ⟨k1, -, k3⟩ := key n (le_refl _)
      rw [k1, hcn] at k3
      unfold connOK
      rw [allIn_iff']
      intro j hj1 hj2
      obtain ⟨l1, l2⟩ := k3 j hj1 hj2
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      refine ⟨l1, ?_⟩
      rw [hapA _ (by omega), hapB _ (by omega)]
      exact l2
  · rw [Bool.eq_iff_iff, memK_iff hn hL hp v, List.any_eq_true]
    simp only [List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨i, hi, e⟩
      exact ⟨i, hi, by rw [← hget i hi]; exact e⟩
    · rintro ⟨i, hi, e⟩
      exact ⟨i, hi, by rw [hget i hi]; exact e⟩

end CFSG.KS.SporSch.VOrb

end

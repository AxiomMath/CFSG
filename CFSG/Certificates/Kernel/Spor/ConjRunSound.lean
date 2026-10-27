module

public import Certificates.Data.Kernel.Spor.ConjRun
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.KS.ConjRun

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem strictN_eq' (y : Nat) (f : Nat → Nat) : strictN y f = f y := by cases y <;> rfl

theorem nIf_true {c : Bool} {t e : Nat} (h : c = true) :
    Bool.rec (motive := fun _ => Nat) e t c = t := by subst h; rfl

theorem nIf_false {c : Bool} {t e : Nat} (h : c = false) :
    Bool.rec (motive := fun _ => Nat) e t c = e := by subst h; rfl

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa [Nat.blt_eq] using h

theorem blt_f {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.2 (by simpa [Nat.blt_eq] using h)

theorem beq_t {a b : Nat} (h : a = b) : Nat.beq a b = true := by simpa [Nat.beq_eq] using h

theorem beq_f {a b : Nat} (h : ¬ a = b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 (by simpa [Nat.beq_eq] using h)

theorem ble_t {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by simpa [Nat.ble_eq] using h

theorem ble_f {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false :=
  Bool.eq_false_iff.2 (by simpa [Nat.ble_eq] using h)

variable {n : Nat}

@[expose] noncomputable def gL (k : Nat) (g : Nat → Equiv.Perm (Fin n)) (l : Nat) :
    Equiv.Perm (Fin n) :=
  if l < k then g l else if l < k + k then (g (l - k))⁻¹ else 1

@[expose] noncomputable def cW (k R : Nat) (PL : Nat → Nat) (g : Nat → Equiv.Perm (Fin n)) :
    Nat → Nat → Equiv.Perm (Fin n)
  | 0, _ => 1
  | d + 1, j => if j = R then 1 else
      gL k g (Nat.land (r32 PL j) 15) * cW k R PL g d (Nat.shiftRight (r32 PL j) 4)

@[expose] noncomputable def ptV (y : Equiv.Perm (Fin n)) (t : Nat) : Nat :=
  if h : t < n then (y ⟨t, h⟩ : Nat) else 0

@[expose] noncomputable def keyP (w r : Nat) (y : Equiv.Perm (Fin n)) : Nat :=
  ∑ t ∈ Finset.range r, Nat.shiftLeft (ptV y t) (Nat.mul w t)

theorem gL_mem {k : Nat} {g : Nat → Equiv.Perm (Fin n)} {H : Subgroup (Equiv.Perm (Fin n))}
    (hg : ∀ l < k, g l ∈ H) (l : Nat) : gL k g l ∈ H := by
  unfold gL
  split_ifs with h1 h2
  · exact hg l h1
  · exact H.inv_mem (hg _ (by omega))
  · exact H.one_mem

theorem cW_mem {k R : Nat} {PL : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    {H : Subgroup (Equiv.Perm (Fin n))} (hg : ∀ l < k, g l ∈ H) (d j : Nat) :
    cW k R PL g d j ∈ H := by
  induction d generalizing j with
  | zero => exact H.one_mem
  | succ d ih =>
    unfold cW
    split_ifs
    · exact H.one_mem
    · exact H.mul_mem (gL_mem hg _) (ih _)

@[expose] def GensRep (n w m k : Nat) (S SI : Nat → Nat) (g : Nat → Equiv.Perm (Fin n)) : Prop :=
  ∀ l < k, ∀ p (hp : p < n), pg w m (S l) p = (g l ⟨p, hp⟩ : Nat) ∧
    pg w m (SI l) p = ((g l)⁻¹ ⟨p, hp⟩ : Nat)

variable {w m k R B : Nat} {S SI PL : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
  {β : Equiv.Perm (Fin n)}

theorem cg_rep (hS : GensRep n w m k S SI g) {l : Nat} (hl : l < k + k) {p : Nat} (hp : p < n) :
    pg w m (cgK k S SI l) p = (gL k g l ⟨p, hp⟩ : Nat) ∧
      pg w m (cgiK k S SI l) p = ((gL k g l)⁻¹ ⟨p, hp⟩ : Nat) := by
  unfold cgK cgiK gL
  by_cases h : l < k
  · rw [nIf_true (blt_t h), nIf_true (blt_t h), if_pos h]
    exact hS l h p hp
  · rw [nIf_false (blt_f h), nIf_false (blt_f h), if_neg h, if_pos hl, inv_inv]
    exact (hS (l - k) (by omega) p hp).symm

theorem cvK_zero (j p : Nat) :
    cvK n w m k R B S SI PL 0 j p = nIf(Nat.beq j R, pg w m B p, n) := rfl

theorem cvK_succ (d j p : Nat) :
    cvK n w m k R B S SI PL (d + 1) j p = nIf(Nat.beq j R, pg w m B p,
      nIf(Nat.blt (Nat.land (r32 PL j) 15) (Nat.add k k),
        nIf(Nat.blt (cvK n w m k R B S SI PL d (Nat.shiftRight (r32 PL j) 4)
            (pg w m (cgiK k S SI (Nat.land (r32 PL j) 15)) p)) n,
          pg w m (cgK k S SI (Nat.land (r32 PL j) 15))
            (cvK n w m k R B S SI PL d (Nat.shiftRight (r32 PL j) 4)
              (pg w m (cgiK k S SI (Nat.land (r32 PL j) 15)) p)), n), n)) := by
  change nIf(Nat.beq j R, pg w m B p, strictN (r32 PL j) (fun e => strictN (Nat.land e 15)
    (fun l => nIf(Nat.blt l (Nat.add k k), strictN (pg w m (cgiK k S SI l) p) (fun q =>
      strictN (cvK n w m k R B S SI PL d (Nat.shiftRight e 4) q) (fun v =>
        nIf(Nat.blt v n, pg w m (cgK k S SI l) v, n))), n)))) = _
  simp only [strictN_eq']

theorem cvK_sound (hS : GensRep n w m k S SI g)
    (hB : ∀ p (hp : p < n), pg w m B p = (β ⟨p, hp⟩ : Nat)) (d : Nat) :
    ∀ j p (hp : p < n), cvK n w m k R B S SI PL d j p < n →
      cvK n w m k R B S SI PL d j p =
        ((cW k R PL g d j * β * (cW k R PL g d j)⁻¹) ⟨p, hp⟩ : Nat) := by
  induction d with
  | zero =>
    intro j p hp h
    rw [cvK_zero] at h ⊢
    by_cases hj : j = R
    · rw [nIf_true (beq_t hj)]
      simp [cW, hB p hp]
    · rw [nIf_false (beq_f hj)] at h
      exact absurd h (Nat.lt_irrefl n)
  | succ d ih =>
    intro j p hp h
    rw [cvK_succ] at h ⊢
    by_cases hj : j = R
    · rw [nIf_true (beq_t hj)]
      simp [cW, hj, hB p hp]
    · rw [nIf_false (beq_f hj)] at h ⊢
      set l := Nat.land (r32 PL j) 15 with hl_def
      set e := Nat.shiftRight (r32 PL j) 4 with he_def
      by_cases hl : l < k + k
      · rw [nIf_true (blt_t (show l < Nat.add k k from hl))] at h ⊢
        obtain ⟨-, hg2⟩ := cg_rep hS hl hp
        have hq : pg w m (cgiK k S SI l) p < n := by rw [hg2]; exact Fin.isLt _
        by_cases hv : cvK n w m k R B S SI PL d e (pg w m (cgiK k S SI l) p) < n
        · rw [nIf_true (blt_t hv)]
          have hv' := ih e _ hq hv
          rw [(cg_rep hS hl hv).1]
          have hfin : (⟨cvK n w m k R B S SI PL d e (pg w m (cgiK k S SI l) p), hv⟩ : Fin n) =
              (cW k R PL g d e * β * (cW k R PL g d e)⁻¹) ((gL k g l)⁻¹ ⟨p, hp⟩) := by
            apply Fin.ext
            change cvK n w m k R B S SI PL d e (pg w m (cgiK k S SI l) p) = _
            rw [hv']
            congr 2
            exact Fin.ext hg2
          rw [hfin]
          simp only [cW, if_neg hj, ← hl_def, ← he_def, Equiv.Perm.mul_apply, mul_inv_rev]
        · rw [nIf_false (blt_f hv)] at h
          exact absurd h (Nat.lt_irrefl n)
      · rw [nIf_false (blt_f (show ¬ l < Nat.add k k from hl))] at h
        exact absurd h (Nat.lt_irrefl n)

@[expose] noncomputable def keyGo (n w m k R B : Nat) (S SI PL : Nat → Nat) (d j F : Nat) :
    Nat → Nat :=
  fun i => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => strictN acc (fun a => strictN (cvK n w m k R B S SI PL d j t) (fun v =>
      nIf(Nat.blt v n, Nat.add a (Nat.shiftLeft v (Nat.mul w t)), F)))) i

theorem keyGo_succ (d j F i : Nat) : keyGo n w m k R B S SI PL d j F (i + 1) =
    nIf(Nat.blt (cvK n w m k R B S SI PL d j i) n,
      Nat.add (keyGo n w m k R B S SI PL d j F i)
        (Nat.shiftLeft (cvK n w m k R B S SI PL d j i) (Nat.mul w i)), F) := by
  change strictN (keyGo n w m k R B S SI PL d j F i) (fun a =>
    strictN (cvK n w m k R B S SI PL d j i) (fun v =>
      nIf(Nat.blt v n, Nat.add a (Nat.shiftLeft v (Nat.mul w i)), F))) = _
  simp only [strictN_eq']

theorem keyGo_spec (hS : GensRep n w m k S SI g)
    (hB : ∀ p (hp : p < n), pg w m B p = (β ⟨p, hp⟩ : Nat)) (d j F : Nat) :
    ∀ i ≤ n, F ≤ keyGo n w m k R B S SI PL d j F i ∨
      keyGo n w m k R B S SI PL d j F i =
        keyP w i (cW k R PL g d j * β * (cW k R PL g d j)⁻¹) := by
  intro i
  induction i with
  | zero => intro _; right; simp [keyP, keyGo]
  | succ i ih =>
    intro hi
    rw [keyGo_succ]
    by_cases hv : cvK n w m k R B S SI PL d j i < n
    · rw [nIf_true (blt_t hv)]
      rcases ih (by omega) with h | h
      · left
        exact le_trans h (Nat.le_add_right _ _)
      · right
        rw [h, keyP, keyP, Finset.sum_range_succ, Nat.add_eq]
        congr 2
        rw [cvK_sound hS hB d j i (by omega) hv, ptV, dif_pos (by omega)]
    · rw [nIf_false (blt_f hv)]
      left
      exact le_refl _

theorem keyK_eq (hS : GensRep n w m k S SI g)
    (hB : ∀ p (hp : p < n), pg w m B p = (β ⟨p, hp⟩ : Nat)) {d r j : Nat} (hr : r ≤ n)
    (h : keyK n w m k R B S SI PL d r j < Nat.shiftLeft 1 (Nat.mul w r)) :
    keyK n w m k R B S SI PL d r j = keyP w r (cW k R PL g d j * β * (cW k R PL g d j)⁻¹) := by
  have e : keyK n w m k R B S SI PL d r j =
      keyGo n w m k R B S SI PL d j (Nat.shiftLeft 1 (Nat.mul w r)) r := rfl
  rw [e] at h ⊢
  rcases keyGo_spec (R := R) (PL := PL) hS hB d j (Nat.shiftLeft 1 (Nat.mul w r)) r hr with h' | h'
  · exact absurd h (Nat.not_lt.2 h')
  · exact h'

@[expose] noncomputable def nextK (n w m k R B : Nat) (S SI PL : Nat → Nat) (d r N j : Nat) :
    Nat :=
  if j + 1 < N then keyK n w m k R B S SI PL d r (j + 1) else Nat.shiftLeft 1 (Nat.mul w r)

theorem runGo_zero (d r lo : Nat) : ∀ len, runGo n w m k R B S SI PL d r lo len 0 = 0 := by
  intro len
  induction len with
  | zero => rfl
  | succ l ih =>
    change strictN (keyK n w m k R B S SI PL d r (Nat.add lo l)) (fun key =>
      strictN (nIf(Nat.blt key 0, key, nat_lit 0)) (runGo n w m k R B S SI PL d r lo l)) = 0
    simp only [strictN_eq']
    rw [nIf_false (blt_f (Nat.not_lt_zero _))]
    exact ih

theorem runGo_spec (d r lo : Nat) : ∀ len s, 0 < runGo n w m k R B S SI PL d r lo len s →
    ∀ t < len, keyK n w m k R B S SI PL d r (lo + t) <
      if t + 1 < len then keyK n w m k R B S SI PL d r (lo + t + 1) else s := by
  intro len
  induction len with
  | zero => intro s _ t ht; omega
  | succ l ih =>
    intro s h t ht
    change 0 < strictN (keyK n w m k R B S SI PL d r (Nat.add lo l)) (fun key =>
      strictN (nIf(Nat.blt key s, key, nat_lit 0)) (runGo n w m k R B S SI PL d r lo l)) at h
    simp only [strictN_eq'] at h
    by_cases hk : keyK n w m k R B S SI PL d r (Nat.add lo l) < s
    · rw [nIf_true (blt_t hk)] at h
      have ih' := ih _ h
      by_cases htl : t < l
      · have h1 := ih' t htl
        rw [if_pos (by omega : t + 1 < l + 1)]
        by_cases ht1 : t + 1 < l
        · rwa [if_pos ht1] at h1
        · rw [if_neg ht1] at h1
          have : lo + t + 1 = Nat.add lo l := by change lo + t + 1 = lo + l; omega
          rwa [this]
      · have : t = l := by omega
        subst this
        rw [if_neg (by omega)]
        exact hk
    · rw [nIf_false (blt_f hk), runGo_zero] at h
      exact absurd h (Nat.lt_irrefl 0)

theorem runK_spec {d r N lo len : Nat} (h : runK n w m k R B S SI PL d r N lo len = true) :
    ∀ t, t < len → lo + t < N →
      keyK n w m k R B S SI PL d r (lo + t) < nextK n w m k R B S SI PL d r N (lo + t) := by
  intro t ht htN
  have hl' : nIf(Nat.ble len (Nat.sub N lo), len, Nat.sub N lo) = min len (N - lo) := by
    by_cases hc : len ≤ N - lo
    · rw [nIf_true (ble_t (show len ≤ Nat.sub N lo from hc)), min_eq_left hc]
    · rw [nIf_false (ble_f (show ¬ len ≤ Nat.sub N lo from hc)), min_eq_right (by omega)]
      rfl
  have h' : runAt n w m k R B S SI PL d r N lo (min len (N - lo)) = true := by
    rw [← hl']
    exact h
  generalize hL : min len (N - lo) = len' at h'
  unfold runAt at h'
  have h0 := runGo_spec d r lo len' _ (Eq.mp Nat.blt_eq h') t (by omega)
  unfold nextK
  by_cases ht1 : t + 1 < len'
  · rw [if_pos ht1] at h0
    rw [if_pos (by omega)]
    exact h0
  · rw [if_neg ht1] at h0
    have ht2 : Nat.add lo len' = lo + t + 1 := by change lo + len' = lo + t + 1; omega
    rw [ht2] at h0
    by_cases hN : lo + t + 1 < N
    · rw [if_pos hN]
      rw [nIf_true (blt_t hN)] at h0
      exact h0
    · rw [if_neg hN]
      rw [nIf_false (blt_f hN)] at h0
      exact h0

theorem nextK_of_runs {d r N C L : Nat}
    (h : ∀ s < C, runK n w m k R B S SI PL d r N (Nat.mul s L) L = true) (hN : N ≤ C * L) :
    ∀ j < N, keyK n w m k R B S SI PL d r j < nextK n w m k R B S SI PL d r N j := by
  intro j hj
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; omega
    · exact h0
  have hs : j / L < C := by
    rw [Nat.div_lt_iff_lt_mul hL]
    omega
  have he : Nat.mul (j / L) L + j % L = j := by
    rw [Nat.mul_eq, Nat.mul_comm]
    exact Nat.div_add_mod j L
  have h1 := runK_spec (h (j / L) hs) (j % L) (Nat.mod_lt _ hL) (by rw [he]; exact hj)
  rwa [he] at h1

theorem conj_keys_of_next (hS : GensRep n w m k S SI g)
    (hB : ∀ p (hp : p < n), pg w m B p = (β ⟨p, hp⟩ : Nat)) {d r N : Nat} (hr : r ≤ n)
    (h : ∀ j < N, keyK n w m k R B S SI PL d r j < nextK n w m k R B S SI PL d r N j) :
    ∀ i < N, ∀ j < N,
      keyP w r (cW k R PL g d i * β * (cW k R PL g d i)⁻¹) =
        keyP w r (cW k R PL g d j * β * (cW k R PL g d j)⁻¹) → i = j := by
  set K := keyK n w m k R B S SI PL d r
  have hlast : ∀ t i, i + t + 1 = N → K i < Nat.shiftLeft 1 (Nat.mul w r) := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have := h i (by omega)
      unfold nextK at this
      rwa [if_neg (by omega)] at this
    | succ t ih =>
      intro i hi
      have := h i (by omega)
      unfold nextK at this
      rw [if_pos (by omega)] at this
      exact lt_trans this (ih (i + 1) (by omega))
  have hmono : ∀ t i, i + t + 1 < N → K i < K (i + t + 1) := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have := h i (by omega)
      unfold nextK at this
      rwa [if_pos (by omega)] at this
    | succ t ih =>
      intro i hi
      have h2 := h (i + t + 1) (by omega)
      unfold nextK at h2
      rw [if_pos (by omega)] at h2
      exact lt_trans (ih i (by omega)) h2
  have hval : ∀ i < N, K i = keyP w r (cW k R PL g d i * β * (cW k R PL g d i)⁻¹) := fun i hi =>
    keyK_eq hS hB hr (hlast (N - i - 1) i (by omega))
  intro i hi j hj e
  rw [← hval i hi, ← hval j hj] at e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hmono (j - i - 1) i (by omega)
    rw [show i + (j - i - 1) + 1 = j by omega] at this
    omega
  · have := hmono (i - j - 1) j (by omega)
    rw [show j + (i - j - 1) + 1 = i by omega] at this
    omega

end CFSG.KS.ConjRun

end

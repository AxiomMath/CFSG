module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Fi22LH.Loops
import Mathlib.Data.Fintype.Card

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KC.Enum

theorem get!_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem get!_set! {α : Type} [Inhabited α] (xs : Array α) {i j : Nat} (hi : i < xs.size)
    (hj : j < xs.size) (v : α) : (xs.set! i v)[j]! = if i = j then v else xs[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by rw [Array.size_setIfInBounds]; exact hj)]
  by_cases e : i = j
  · subst e
    rw [if_pos rfl, Array.getElem_setIfInBounds_self]
  · rw [if_neg e, Array.getElem_setIfInBounds_ne hj e, getElem!_pos xs j hj]

theorem size_set! {α : Type} (xs : Array α) (i : Nat) (v : α) : (xs.set! i v).size = xs.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem ofNat_ne_none32 {v : Nat} (hv : v < 2 ^ 32 - 1) : UInt32.ofNat v ≠ none32 := by
  intro e
  have := congrArg UInt32.toNat e
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
  change v = 4294967295 at this
  omega

theorem ap_ofNat {t : Table} {k v : Nat} (h : t[k]! = UInt32.ofNat v) (hv : v < 2 ^ 32) :
    ap t k = v := by
  unfold ap
  rw [h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hv]

theorem hitT_zero (par lab : Nat → Nat) (h l px : Nat) : hitT par lab h l px 0 = 0 := by
  unfold hitT
  rw [beq_true rfl]

theorem hitT_spec {par lab : Nat → Nat} {h l px m : Nat} (hne : hitT par lab h l px m ≠ 0) :
    (px < m ∧ hitT par lab h l px m = m) ∨
      (px = m ∧ par m = h ∧ lab m = l ∧ hitT par lab h l px m = m + 1) := by
  revert hne
  simp only [hitT, nIf_eq, Nat.beq_eq, Nat.blt_eq]
  split_ifs <;> omega

@[expose] def TInv (n : Nat) (pts pos par lab : Nat → Nat) (m : Nat)
    (s : Table × Table × Table × Table) : Prop :=
  s.1.size = n ∧ (∀ x < n, s.1[x]! = if pos x < m then UInt32.ofNat (pos x) else none32) ∧
    s.2.1.size = m ∧ (∀ k < m, s.2.1[k]! = UInt32.ofNat (pts k)) ∧
    s.2.2.1.size = m ∧ (∀ k < m, s.2.2.1[k]! = UInt32.ofNat (par k)) ∧
    s.2.2.2.size = m ∧ (∀ k < m, s.2.2.2[k]! = UInt32.ofNat (lab k)) ∧ ∀ k < m, pts k < n

@[expose] def tStep (letters : Array Table) (h p l : Nat) (s : Table × Table × Table × Table) :
    Table × Table × Table × Table :=
  if (s.1[ap letters[l]! p]! == none32) = true then
    (s.1.set! (ap letters[l]! p) (UInt32.ofNat s.2.1.size), s.2.1.push (UInt32.ofNat (ap letters[l]! p)),
      s.2.2.1.push (UInt32.ofNat h), s.2.2.2.push (UInt32.ofNat l))
  else s

theorem tStep_inv {n N none : Nat} {letters : Array Table} {pts pos par lab : Nat → Nat}
    (hnone : N ≤ none) (hnone32 : none < 2 ^ 32 - 1)
    (hP2 : ∀ x < n, pos x = none ∨ (pos x < N ∧ pts (pos x) = x))
    {h p l m : Nat} {s : Table × Table × Table × Table} (hs : TInv n pts pos par lab m s)
    (hq : ap letters[l]! p < n) (hne : hitT par lab h l (pos (ap letters[l]! p)) m ≠ 0)
    (hle : hitT par lab h l (pos (ap letters[l]! p)) m ≤ N) :
    TInv n pts pos par lab (hitT par lab h l (pos (ap letters[l]! p)) m) (tStep letters h p l s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  set q := ap letters[l]! p with hqd
  rcases hitT_spec hne with ⟨hlt, he⟩ | ⟨heq, hpar, hlab, he⟩
  · rw [he]
    have hc : (s.1[q]! == none32) = false := by
      rw [h2 q hq, if_pos hlt, beq_eq_false_iff_ne]
      exact ofNat_ne_none32 (by omega)
    unfold tStep
    rw [← hqd, hc]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · rw [he]
    have hm : m < N := by omega
    have hpq : pts m = q := by
      rcases hP2 q hq with h0 | ⟨_, h0⟩
      · omega
      · rw [← heq]; exact h0
    have hc : (s.1[q]! == none32) = true := by
      rw [h2 q hq, if_neg (by omega)]
      exact beq_self_eq_true _
    unfold tStep
    rw [← hqd, hc, if_pos rfl]
    refine ⟨by rw [size_set!, h1], fun x hx => ?_, by rw [Array.size_push, h3], fun k hk => ?_,
      by rw [Array.size_push, h5], fun k hk => ?_, by rw [Array.size_push, h7], fun k hk => ?_,
      fun k hk => ?_⟩
    · dsimp only
      rw [get!_set! _ (by rw [h1]; exact hq) (by rw [h1]; exact hx), h3]
      by_cases e : q = x
      · subst e
        rw [if_pos rfl, if_pos (by omega), heq]
      · rw [if_neg e, h2 x hx]
        by_cases e2 : pos x < m
        · rw [if_pos e2, if_pos (by omega)]
        · rw [if_neg e2, if_neg]
          intro e3
          have hxm : pos x = m := by omega
          rcases hP2 x hx with h0 | ⟨_, h0⟩
          · omega
          · rw [hxm, hpq] at h0
            exact e h0
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h3]; exact hk'), h4 k hk']
      · have : k = s.2.1.size := by omega
        rw [this, get!_push_eq, h3, hpq]
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h5]; exact hk'), h6 k hk']
      · have : k = s.2.2.1.size := by omega
        rw [this, get!_push_eq, h5, hpar]
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h7]; exact hk'), h8 k hk']
      · have : k = s.2.2.2.size := by omega
        rw [this, get!_push_eq, h7, hlab]
    · rcases Nat.lt_or_ge k m with hk' | hk'
      · exact h9 k hk'
      · rw [show k = m by omega, hpq]
        exact hq

theorem card_le_of_inj {f g : Nat → Nat} {m n : Nat} (hf : ∀ k < m, f k < n)
    (hg : ∀ k < m, g (f k) = k) : m ≤ n := by
  let F : Fin m → Fin n := fun k => ⟨f k, hf k k.2⟩
  have hF : Function.Injective F := by
    intro a b e
    have e' : f a = f b := congrArg Fin.val e
    apply Fin.ext
    rw [← hg a a.2, ← hg b b.2, e']
  have := Fintype.card_le_of_injective F hF
  simpa using this

theorem treeBFS_eq_of {n root nl N none : Nat} {letters : Array Table}
    {img : Nat → Nat → Nat} {pts pos par lab : Nat → Nat} (hn : n < 2 ^ 32)
    (hnone : N ≤ none) (hnone32 : none < 2 ^ 32 - 1) (hroot_lt : root < n)
    (hroot : pts 0 = root)
    (himg : ∀ h < N, pts h < n → ∀ l < nl, ap letters[l]! (pts h) = img h l ∧ img h l < n)
    (hpos : posK pts pos none n N = true) (hbfs : bfsT img nl pos par lab N = true) :
    (0 < N ∧ N ≤ n ∧ ∀ k < N, pts k < n) ∧ treeBFS n root letters (Array.range nl) =
      ⟨Array.ofFn (n := N) fun k => UInt32.ofNat (pts k.val),
        Array.ofFn (n := n) fun x => if pos x.val = none then none32 else UInt32.ofNat (pos x.val),
        Array.ofFn (n := N) fun k => UInt32.ofNat (par k.val),
        Array.ofFn (n := N) fun k => UInt32.ofNat (lab k.val)⟩ := by
  unfold posK at hpos
  rw [bAnd_eq, Bool.and_eq_true] at hpos
  obtain ⟨hp1, hp2⟩ := hpos
  have hP1 : ∀ k < N, pos (pts k) = k := fun k hk => Nat.eq_of_beq_eq_true (allN_iff.1 hp1 k hk)
  have hP2 : ∀ x < n, pos x = none ∨ (pos x < N ∧ pts (pos x) = x) := by
    intro x hx
    have := allN_iff.1 hp2 x hx
    rw [strictB_eq, bIf_eq] at this
    by_cases e : pos x = none
    · exact Or.inl e
    · rw [beq_false e, if_neg (by simp), bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
      exact Or.inr this
  unfold bfsT at hbfs
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq,
    foldUp_eq] at hbfs
  obtain ⟨hpar0, hlab0, hfold⟩ := hbfs
  let H : Nat → Nat → Nat → Nat := fun h l m => hitT par lab h l (pos (img h l)) m
  let S : Nat → Nat → Nat := fun h m =>
    if h < m then (List.range nl).foldl (fun m l => H h l m) m else 0
  let C : Nat → Nat := fun h => (List.range h).foldl (fun m h => S h m) 1
  have hCN : C N = N := by
    refine Eq.trans ?_ hfold
    change (List.range N).foldl (fun m h => S h m) 1 = _
    congr 1
    funext m h
    simp only [S, H, nIf_eq, Nat.blt_eq, foldUp_eq]
  have hC_succ : ∀ h, C (h + 1) = S h (C h) := fun h => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with e | e
    · have : C 0 = 1 := rfl
      rw [← e] at this
      omega
    · exact e
  have hH0 : ∀ h l, H h l 0 = 0 := fun h l => hitT_zero _ _ _ _ _
  have hHm : ∀ h l m, H h l m ≠ 0 → m ≤ H h l m := fun h l m hne => by
    rcases hitT_spec hne with ⟨_, he⟩ | ⟨_, _, _, he⟩
    · change m ≤ hitT par lab h l (pos (img h l)) m
      rw [he]
    · change m ≤ hitT par lab h l (pos (img h l)) m
      rw [he]
      omega
  have hS0 : ∀ h, S h 0 = 0 := fun h => by simp [S]
  have hSm : ∀ h m, S h m ≠ 0 → m ≤ S h m := fun h m hne => by
    simp only [S] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun l m => H h l m) (fun l => hH0 h l) (fun l m => hHm h l m) _ _ hne).2
    · exact absurd rfl hne
  have hC : ∀ h ≤ N, C h ≠ 0 ∧ C h ≤ N := by
    intro h hh
    have e : (List.range N).foldl (fun m h => S h m) 1 =
        ((List.range (N - h)).map (h + ·)).foldl (fun m h => S h m) (C h) := by
      have eN : N = h + (N - h) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have h2 : ((List.range (N - h)).map (h + ·)).foldl (fun m h => S h m) (C h) ≠ 0 := by
      rw [← e]
      change C N ≠ 0
      omega
    have := fold_nonzero S hS0 hSm _ _ h2
    rw [← e] at this
    change C h ≠ 0 ∧ C h ≤ C N at this
    rw [hCN] at this
    exact this
  have hCh : ∀ h < N, h < C h := by
    intro h hh
    have := (hC (h + 1) hh).1
    rw [hC_succ] at this
    simp only [S] at this
    split at this
    · assumption
    · exact absurd rfl this
  have hinner : ∀ h < N, ∀ s, TInv n pts pos par lab (C h) s →
      TInv n pts pos par lab (C (h + 1))
        ((List.range nl).foldl (fun s l => tStep letters h (pts h) l s) s) := by
    intro h hh s hs
    have hfin : C (h + 1) = (List.range nl).foldl (fun m l => H h l m) (C h) := by
      rw [hC_succ]
      simp only [S, if_pos (hCh h hh)]
    have hgen : ∀ j ≤ nl, TInv n pts pos par lab ((List.range j).foldl (fun m l => H h l m) (C h))
        ((List.range j).foldl (fun s l => tStep letters h (pts h) l s) s) := by
      intro j
      induction j with
      | zero => intro _; exact hs
      | succ j ih =>
        intro hj
        rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_cons, List.foldl_nil]
        have e : (List.range nl).foldl (fun m l => H h l m) (C h) =
            ((List.range (nl - (j + 1))).map ((j + 1) + ·)).foldl (fun m l => H h l m)
              (H h j ((List.range j).foldl (fun m l => H h l m) (C h))) := by
          have enl : nl = j + 1 + (nl - (j + 1)) := by omega
          conv_lhs => rw [enl]
          rw [List.range_add, List.foldl_append, List.range_succ, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
        have hne : ((List.range (nl - (j + 1))).map ((j + 1) + ·)).foldl (fun m l => H h l m)
            (H h j ((List.range j).foldl (fun m l => H h l m) (C h))) ≠ 0 := by
          rw [← e, ← hfin]
          exact (hC (h + 1) hh).1
        obtain ⟨hne1, hle1⟩ := fold_nonzero (fun l m => H h l m) (fun l => hH0 h l)
          (fun l m => hHm h l m) _ _ hne
        rw [← e, ← hfin] at hle1
        have hle2 := (hC (h + 1) hh).2
        obtain ⟨hi1, hi2⟩ := himg h hh (hs.2.2.2.2.2.2.2.2 h (hCh h hh)) j (by omega)
        have hne1' : hitT par lab h j (pos (img h j))
            ((List.range j).foldl (fun m l => H h l m) (C h)) ≠ 0 := hne1
        have hle1' : hitT par lab h j (pos (img h j))
            ((List.range j).foldl (fun m l => H h l m) (C h)) ≤ N := Nat.le_trans hle1 hle2
        have := tStep_inv (letters := letters) (p := pts h) (l := j) hnone hnone32 hP2 (ih (by omega))
          (by rw [hi1]; exact hi2) (by rw [hi1]; exact hne1') (by rw [hi1]; exact hle1')
        rw [hi1] at this
        exact this
    rw [hfin]
    exact hgen nl (le_refl _)
  obtain ⟨s, hs, hT, hNn⟩ : ∃ s : Table × Table × Table × Table,
      treeBFS n root letters (Array.range nl) = ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩ ∧
        TInv n pts pos par lab N s ∧ N ≤ n := by
    unfold treeBFS
    refine ⟨_, rfl, ?_⟩
    refine range_loop (fun q s => q ≤ N ∧ TInv n pts pos par lab (C q) s)
      (fun s => TInv n pts pos par lab N s ∧ N ≤ n) _ n _ ?_ ?_ ?_
    · intro q s hq hI
      obtain ⟨hqN, hI⟩ := hI
      rcases Nat.lt_or_ge q N with hlt | hge
      · have hqs : q < s.2.1.size := by rw [hI.2.2.1]; exact hCh q hlt
        have hp : ap s.2.1 q = pts q := ap_ofNat (hI.2.2.2.1 q (hCh q hlt))
          (Nat.lt_trans (hI.2.2.2.2.2.2.2.2 q (hCh q hlt)) hn)
        simp only [hqs, ↓reduceIte, hp]
        rw [← Array.forIn_toList, Array.toList_range,
          forIn_yield _ (fun l s => tStep letters q (pts q) l s) (fun a b => by
            unfold tStep
            split <;> rfl)]
        exact ⟨by omega, hinner q hlt s hI⟩
      · have e : q = N := by omega
        subst e
        have hqs : ¬ q < s.2.1.size := by rw [hI.2.2.1, hCN]; omega
        simp only [hqs, ↓reduceIte]
        rw [hCN] at hI
        exact ⟨hI, by omega⟩
    · intro s hs
      obtain ⟨hnN, hs⟩ := hs
      have e : n = N := by
        by_contra hne
        have hlt : n < N := by omega
        have h1 := hCh n hlt
        have h2 := card_le_of_inj (f := pts) (g := pos) (m := C n) (n := n)
          hs.2.2.2.2.2.2.2.2 fun k hk => hP1 k (by have := (hC n hnN).2; omega)
        omega
      have hCn : C n = N := by rw [e]; exact hCN
      rw [hCn] at hs
      exact ⟨hs, by omega⟩
    · refine ⟨Nat.zero_le _, ?_⟩
      change TInv n pts pos par lab 1 _
      refine ⟨by rw [size_set!, Array.size_replicate], fun x hx => ?_, rfl, fun k hk => ?_, rfl,
        fun k hk => ?_, rfl, fun k hk => ?_, fun k hk => ?_⟩
      · dsimp only
        rw [get!_set! _ (by rw [Array.size_replicate]; exact hroot_lt)
          (by rw [Array.size_replicate]; exact hx)]
        by_cases e : root = x
        · subst e
          rw [if_pos rfl, ← hroot, hP1 0 hN, if_pos (by omega)]
          rfl
        · rw [if_neg e, getElem!_pos _ x (by rw [Array.size_replicate]; exact hx),
            Array.getElem_replicate, if_neg]
          intro h0
          rcases hP2 x hx with h1 | ⟨_, h1⟩
          · omega
          · have : pos x = 0 := by omega
            rw [this, hroot] at h1
            exact e h1
      · have : k = 0 := by omega
        subst this
        rw [hroot]
        rfl
      · have : k = 0 := by omega
        subst this
        rw [hpar0]
        rfl
      · have : k = 0 := by omega
        subst this
        rw [hlab0]
        rfl
      · have : k = 0 := by omega
        subst this
        rw [hroot]
        exact hroot_lt
  refine ⟨⟨hN, hNn, hT.2.2.2.2.2.2.2.2⟩, ?_⟩
  rw [hs]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hT
  have hof : ∀ (a : Table) (m : Nat) (g : Nat → UInt32), a.size = m → (∀ k < m, a[k]! = g k) →
      a = Array.ofFn (n := m) fun k => g k.val := by
    intro a m g hs hg
    apply Array.ext (by rw [hs, Array.size_ofFn])
    intro i hi1 hi2
    rw [Array.getElem_ofFn, ← getElem!_pos a i hi1, hg i (by omega)]
  congr 1
  · exact hof _ _ _ h3 h4
  · refine hof _ _ (fun x => if pos x = none then none32 else UInt32.ofNat (pos x)) h1
      fun x hx => ?_
    rw [h2 x hx]
    rcases hP2 x hx with e | ⟨hlt, _⟩
    · rw [if_neg (by omega), if_pos e]
    · rw [if_pos hlt, if_neg (by omega)]
  · exact hof _ _ _ h5 h6
  · exact hof _ _ _ h7 h8

theorem bfsT_facts {n nl N none : Nat} {img : Nat → Nat → Nat} {pts pos par lab : Nat → Nat}
    (hnone : N ≤ none)
    (hpos : posK pts pos none n N = true) (hbfs : bfsT img nl pos par lab N = true)
    (himg : ∀ h < N, ∀ l < nl, img h l < n) :
    (∀ h < N, ∀ l < nl, pos (img h l) < N ∧ pts (pos (img h l)) = img h l) ∧
      ∀ k, 0 < k → k < N → par k < k ∧ lab k < nl ∧ img (par k) (lab k) = pts k := by
  unfold posK at hpos
  rw [bAnd_eq, Bool.and_eq_true] at hpos
  obtain ⟨hp1, hp2⟩ := hpos
  have hP2 : ∀ x < n, pos x = none ∨ (pos x < N ∧ pts (pos x) = x) := by
    intro x hx
    have := allN_iff.1 hp2 x hx
    rw [strictB_eq, bIf_eq] at this
    by_cases e : pos x = none
    · exact Or.inl e
    · rw [beq_false e, if_neg (by simp), bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
      exact Or.inr this
  unfold bfsT at hbfs
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq,
    foldUp_eq] at hbfs
  obtain ⟨-, -, hfold⟩ := hbfs
  let H : Nat → Nat → Nat → Nat := fun h l m => hitT par lab h l (pos (img h l)) m
  let S : Nat → Nat → Nat := fun h m =>
    if h < m then (List.range nl).foldl (fun m l => H h l m) m else 0
  let C : Nat → Nat := fun h => (List.range h).foldl (fun m h => S h m) 1
  have hCN : C N = N := by
    refine Eq.trans ?_ hfold
    change (List.range N).foldl (fun m h => S h m) 1 = _
    congr 1
    funext m h
    simp only [S, H, nIf_eq, Nat.blt_eq, foldUp_eq]
  have hC_succ : ∀ h, C (h + 1) = S h (C h) := fun h => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hH0 : ∀ h l, H h l 0 = 0 := fun h l => hitT_zero _ _ _ _ _
  have hHm : ∀ h l m, H h l m ≠ 0 → m ≤ H h l m := fun h l m hne => by
    rcases hitT_spec hne with ⟨_, he⟩ | ⟨_, _, _, he⟩
    · change m ≤ hitT par lab h l (pos (img h l)) m
      rw [he]
    · change m ≤ hitT par lab h l (pos (img h l)) m
      rw [he]
      omega
  have hS0 : ∀ h, S h 0 = 0 := fun h => by simp [S]
  have hSm : ∀ h m, S h m ≠ 0 → m ≤ S h m := fun h m hne => by
    simp only [S] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun l m => H h l m) (fun l => hH0 h l) (fun l m => hHm h l m) _ _ hne).2
    · exact absurd rfl hne
  have hC : ∀ h ≤ N, C h ≠ 0 ∧ C h ≤ N := by
    intro h hh
    have e : (List.range N).foldl (fun m h => S h m) 1 =
        ((List.range (N - h)).map (h + ·)).foldl (fun m h => S h m) (C h) := by
      have eN : N = h + (N - h) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with e0 | e0
      · have : C 0 = 1 := rfl
        rw [← e0] at this
        omega
      · exact e0
    have h2 : ((List.range (N - h)).map (h + ·)).foldl (fun m h => S h m) (C h) ≠ 0 := by
      rw [← e]
      change C N ≠ 0
      omega
    have := fold_nonzero S hS0 hSm _ _ h2
    rw [← e] at this
    change C h ≠ 0 ∧ C h ≤ C N at this
    rw [hCN] at this
    exact this
  have hCh : ∀ h < N, h < C h := by
    intro h hh
    have := (hC (h + 1) hh).1
    rw [hC_succ] at this
    simp only [S] at this
    split at this
    · assumption
    · exact absurd rfl this
  let M : Nat → Nat → Nat := fun h j => (List.range j).foldl (fun m l => H h l m) (C h)
  have hM : ∀ h < N, ∀ j < nl, H h j (M h j) ≠ 0 ∧ H h j (M h j) ≤ N ∧ C h ≤ M h j := by
    intro h hh j hj
    have hfin : C (h + 1) = (List.range nl).foldl (fun m l => H h l m) (C h) := by
      rw [hC_succ]
      simp only [S, if_pos (hCh h hh)]
    have e : (List.range nl).foldl (fun m l => H h l m) (C h) =
        ((List.range (nl - (j + 1))).map ((j + 1) + ·)).foldl (fun m l => H h l m)
          (H h j (M h j)) := by
      have enl : nl = j + 1 + (nl - (j + 1)) := by omega
      conv_lhs => rw [enl]
      rw [List.range_add, List.foldl_append, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    have hne : ((List.range (nl - (j + 1))).map ((j + 1) + ·)).foldl (fun m l => H h l m)
        (H h j (M h j)) ≠ 0 := by
      rw [← e, ← hfin]
      exact (hC (h + 1) hh).1
    obtain ⟨hne1, hle1⟩ := fold_nonzero (fun l m => H h l m) (fun l => hH0 h l)
      (fun l m => hHm h l m) _ _ hne
    rw [← e, ← hfin] at hle1
    have hpre : C h ≤ M h j := by
      have hne2 : (List.range j).foldl (fun m l => H h l m) (C h) ≠ 0 := by
        intro e0
        have : H h j (M h j) = 0 := by
          change H h j ((List.range j).foldl (fun m l => H h l m) (C h)) = 0
          rw [e0]
          exact hH0 h j
        exact hne1 this
      exact (fold_nonzero (fun l m => H h l m) (fun l => hH0 h l) (fun l m => hHm h l m) _ _
        hne2).2
    exact ⟨hne1, Nat.le_trans hle1 (hC (h + 1) hh).2, hpre⟩
  have hM_succ : ∀ h j, M h (j + 1) = H h j (M h j) := fun h j => by
    simp only [M, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  refine ⟨fun h hh l hl => ?_, ?_⟩
  · obtain ⟨hne, hle, -⟩ := hM h hh l hl
    have hne' : hitT par lab h l (pos (img h l)) (M h l) ≠ 0 := hne
    have hle' : hitT par lab h l (pos (img h l)) (M h l) ≤ N := hle
    have hq := himg h hh l hl
    have hlt : pos (img h l) < N := by
      rcases hitT_spec hne' with ⟨h1, h2⟩ | ⟨h1, _, _, h2⟩
      · rw [h2] at hle'
        omega
      · rw [h2] at hle'
        omega
    rcases hP2 _ hq with e | ⟨_, e⟩
    · omega
    · exact ⟨hlt, e⟩
  ·
    have hP : ∀ h ≤ N, ∀ k, 0 < k → k < C h →
        par k < k ∧ lab k < nl ∧ img (par k) (lab k) = pts k := by
      intro h
      induction h with
      | zero =>
        intro _ k hk0 hk
        have : C 0 = 1 := rfl
        omega
      | succ h ih =>
        intro hh k hk0 hk
        have hQ : ∀ j ≤ nl, ∀ k, 0 < k → k < M h j →
            par k < k ∧ lab k < nl ∧ img (par k) (lab k) = pts k := by
          intro j
          induction j with
          | zero => intro _ k hk0 hk; exact ih (by omega) k hk0 hk
          | succ j ihj =>
            intro hj k hk0 hk
            rw [hM_succ] at hk
            obtain ⟨hne, hle, hpre⟩ := hM h (by omega) j (by omega)
            rcases hitT_spec hne with ⟨_, he⟩ | ⟨heq, hpar, hlab, he⟩
            · change hitT par lab h j (pos (img h j)) (M h j) = M h j at he
              rw [show H h j (M h j) = M h j from he] at hk
              exact ihj (by omega) k hk0 hk
            · change hitT par lab h j (pos (img h j)) (M h j) = M h j + 1 at he
              rw [show H h j (M h j) = M h j + 1 from he] at hk
              rcases Nat.lt_or_ge k (M h j) with h1 | h1
              · exact ihj (by omega) k hk0 h1
              · have hk' : k = M h j := by omega
                subst hk'
                have hq := himg h (by omega) j (by omega)
                have hpq : pts (M h j) = img h j := by
                  rcases hP2 _ hq with e | ⟨_, e⟩
                  · change hitT par lab h j (pos (img h j)) (M h j) ≤ N at hle
                    omega
                  · rw [← heq]
                    exact e
                have := hCh h (by omega)
                exact ⟨by rw [hpar]; omega, by rw [hlab]; omega, by rw [hpar, hlab, hpq]⟩
        have hfin : C (h + 1) = M h nl := by
          rw [hC_succ]
          simp only [S, M, if_pos (hCh h (by omega))]
        rw [hfin] at hk
        exact hQ nl (Nat.le_refl _) k hk0 hk
    intro k hk0 hk
    exact hP N (Nat.le_refl _) k hk0 (by rw [hCN]; exact hk)

theorem ap_ofFn {n k : Nat} {g : Nat → UInt32} (hk : k < n) :
    ap (Array.ofFn (n := n) fun x => g x.val) k = (g k).toNat := by
  unfold ap
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem toNat_ofNat32 {v : Nat} (hv : v < 2 ^ 32) : (UInt32.ofNat v).toNat = v := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hv]

theorem treeOK_of {n root nl N none : Nat} {letters : Array Table}
    {img : Nat → Nat → Nat} {pts pos par lab : Nat → Nat} (hn : n < 2 ^ 32) (hnl : nl < 2 ^ 32)
    (hnone : N ≤ none) (hnone32 : none < 2 ^ 32 - 1) (hroot_lt : root < n)
    (hroot : pts 0 = root)
    (himg : ∀ h < N, pts h < n → ∀ l < nl, ap letters[l]! (pts h) = img h l ∧ img h l < n)
    (hpos : posK pts pos none n N = true) (hbfs : bfsT img nl pos par lab N = true) {T : Tree}
    (hT : T = ⟨Array.ofFn (n := N) fun k => UInt32.ofNat (pts k.val),
        Array.ofFn (n := n) fun x => if pos x.val = none then none32 else UInt32.ofNat (pos x.val),
        Array.ofFn (n := N) fun k => UInt32.ofNat (par k.val),
        Array.ofFn (n := N) fun k => UInt32.ofNat (lab k.val)⟩) :
    CFSG.Perm.Native.treeOK n root T letters (Array.range nl) = true := by
  subst hT
  obtain ⟨⟨hN, hNn, hpts⟩, -⟩ := treeBFS_eq_of hn hnone hnone32 hroot_lt hroot himg hpos hbfs
  have himg' : ∀ h < N, ∀ l < nl, img h l < n := fun h hh l hl => (himg h hh (hpts h hh) l hl).2
  obtain ⟨hcl, htr⟩ := bfsT_facts hnone hpos hbfs himg'
  have hP1 : ∀ k < N, pos (pts k) = k := by
    unfold posK at hpos
    rw [bAnd_eq, Bool.and_eq_true] at hpos
    exact fun k hk => Nat.eq_of_beq_eq_true (allN_iff.1 hpos.1 k hk)
  have hapPos : ∀ x < n, pos x < N → ap (Array.ofFn (n := n) fun x =>
      if pos x.val = none then none32 else UInt32.ofNat (pos x.val)) x = pos x := by
    intro x hx hlt
    rw [ap_ofFn (g := fun x => if pos x = none then none32 else UInt32.ofNat (pos x)) hx,
      if_neg (by omega), toNat_ofNat32 (by omega)]
  have hapPts : ∀ k < N, ap (Array.ofFn (n := N) fun k => UInt32.ofNat (pts k.val)) k = pts k :=
    fun k hk => by
      rw [ap_ofFn (g := fun k => UInt32.ofNat (pts k)) hk, toNat_ofNat32 (by have := hpts k hk; omega)]
  have hapPar : ∀ k < N, 0 < k → ap (Array.ofFn (n := N) fun k => UInt32.ofNat (par k.val)) k =
      par k := fun k hk hk0 => by
    rw [ap_ofFn (g := fun k => UInt32.ofNat (par k)) hk,
      toNat_ofNat32 (by have := (htr k hk0 hk).1; omega)]
  have hapLab : ∀ k < N, 0 < k → ap (Array.ofFn (n := N) fun k => UInt32.ofNat (lab k.val)) k =
      lab k := fun k hk hk0 => by
    rw [ap_ofFn (g := fun k => UInt32.ofNat (lab k)) hk,
      toNat_ofNat32 (by have := (htr k hk0 hk).2.1; omega)]
  have hall : ∀ f : Nat → Bool, (Array.range nl).all f = true ↔ ∀ l < nl, f l = true := by
    intro f
    rw [Array.all_eq_true]
    simp
  have hcon : ∀ x, (Array.range nl).contains x = true ↔ x < nl := by
    intro x
    simp
  unfold CFSG.Perm.Native.treeOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.size_ofFn]
  refine ⟨⟨hN, by rw [hapPts 0 hN, hroot]⟩, ?_⟩
  rw [CFSG.KS.TW.allIn_iff]
  intro k hk
  unfold treeAt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.size_ofFn, Bool.or_eq_true,
    hall, hcon, hapPts k hk]
  refine ⟨⟨⟨hpts k hk, by rw [hapPos _ (hpts k hk) (by rw [hP1 k hk]; exact hk), hP1 k hk]⟩,
    fun l hl => ?_⟩, ?_⟩
  · obtain ⟨e1, e2⟩ := himg k hk (hpts k hk) l hl
    obtain ⟨c1, c2⟩ := hcl k hk l hl
    rw [e1, hapPos _ e2 c1, hapPts _ c1, c2]
    exact ⟨c1, rfl⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inl h0
    · right
      obtain ⟨t1, t2, t3⟩ := htr k h0 hk
      rw [hapPar k hk h0, hapLab k hk h0, hapPts _ (by omega),
        (himg _ (by omega) (hpts _ (by omega)) _ t2).1, t3]
      exact ⟨⟨t1, t2⟩, rfl⟩

end CFSG.KS.Fi22LH

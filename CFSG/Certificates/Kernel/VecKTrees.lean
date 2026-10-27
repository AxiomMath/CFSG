module

public import Certificates.Data.Kernel.VecK
public import Certificates.Data.CFSGNative.HS.Cert
public import CFSG.Certificates.Kernel.Spor.TabWords
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.VecK

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

private theorem notB_eq (a : Bool) : notB a = !a := by
  cases a <;> rfl

private theorem bif_eq (c a b : Bool) :
    (Bool.rec (motive := fun _ => Bool) b a c = true) = (if c = true then a = true else b = true) := by
  cases c <;> rfl

private theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.one_shiftLeft]

private theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · subst h
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (by omega)⟩

private theorem allL_iff {α : Type} {f : α → Bool} : ∀ L : List α, allL f L = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allL]
  | a :: L => by
    change andB (f a) (allL f L) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, allL_iff L]
    simp

private theorem getL_eq (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L[i]?.getD x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change getL x L i = _
    rw [getL_eq x L i]
    rfl

private theorem getL_list {L : List Nat} {i : Nat} (hi : i < L.length) : getL 0 L i = L[i] := by
  rw [getL_eq, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem getL_array (A : Array Nat) {i : Nat} (hi : i < A.size) : getL 0 A.toList i = A[i]! := by
  rw [getL_list (by simpa using hi), Array.getElem_toList, getElem!_pos A i hi]

inductive Reach (good : Nat → Prop) (f : Nat → Nat → Nat) (r : Nat) : Nat → Prop
  | root : Reach good f r r
  | step {p l : Nat} : Reach good f r p → good l → Reach good f r (f l p)

structure TreeFacts (m r : Nat) (good : Nat → Prop) (f : Nat → Nat → Nat) (pt ix : Nat → Nat) :
    Prop where
  m_pos : 0 < m
  root : pt 0 = r
  ix_pt : ∀ t < m, ix (pt t) = t
  clos : ∀ t < m, ∀ l, good l → ix (f l (pt t)) < m ∧ pt (ix (f l (pt t))) = f l (pt t)
  par : ∀ t < m, 0 < t → ∃ u < t, ∃ l, good l ∧ f l (pt u) = pt t

theorem TreeFacts.reach_iff {m r : Nat} {good : Nat → Prop} {f : Nat → Nat → Nat}
    {pt ix : Nat → Nat} (H : TreeFacts m r good f pt ix) (q : Nat) :
    Reach good f r q ↔ ∃ t < m, pt t = q := by
  constructor
  · intro hq
    induction hq with
    | root => exact ⟨0, H.m_pos, H.root⟩
    | step _ hl ih =>
      obtain ⟨t, ht, rfl⟩ := ih
      exact ⟨_, (H.clos t ht _ hl).1, (H.clos t ht _ hl).2⟩
  · rintro ⟨t, ht, rfl⟩
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        rw [H.root]
        exact Reach.root
      · obtain ⟨u, hu, l, hl, e⟩ := H.par t ht h0
        rw [← e]
        exact Reach.step (ih u hu (by omega)) hl

theorem TreeFacts.mem_iff {m m' r : Nat} {good : Nat → Prop} {f : Nat → Nat → Nat}
    {pt ix pt' ix' : Nat → Nat} (H : TreeFacts m r good f pt ix) (H' : TreeFacts m' r good f pt' ix')
    (q : Nat) : (∃ t < m, pt t = q) ↔ ∃ t < m', pt' t = q := by
  rw [← H.reach_iff, ← H'.reach_iff]

private theorem card_image_pt {m : Nat} {pt ix : Nat → Nat} (h : ∀ t < m, ix (pt t) = t) :
    ((Finset.range m).image pt).card = m := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb e
  have ha' : a < m := by simpa using ha
  have hb' : b < m := by simpa using hb
  rw [← h a ha', ← h b hb', e]

theorem TreeFacts.card_eq {m m' r : Nat} {good : Nat → Prop} {f : Nat → Nat → Nat}
    {pt ix pt' ix' : Nat → Nat} (H : TreeFacts m r good f pt ix) (H' : TreeFacts m' r good f pt' ix') :
    m = m' := by
  have himg : (Finset.range m).image pt = (Finset.range m').image pt' := by
    ext q
    simp only [Finset.mem_image, Finset.mem_range]
    exact H.mem_iff H' q
  rw [← card_image_pt H.ix_pt, ← card_image_pt H'.ix_pt, himg]

theorem TreeFacts.congr {n m r : Nat} {good good' : Nat → Prop} {f f' : Nat → Nat → Nat}
    {pt ix : Nat → Nat} (H : TreeFacts m r good f pt ix) (hpt : ∀ t < m, pt t < n)
    (hg : ∀ l, good' l ↔ good l) (hf : ∀ l, good l → ∀ x < n, f' l x = f l x) :
    TreeFacts m r good' f' pt ix where
  m_pos := H.m_pos
  root := H.root
  ix_pt := H.ix_pt
  clos t ht l hl := by
    rw [hf l ((hg l).1 hl) _ (hpt t ht)]
    exact H.clos t ht l ((hg l).1 hl)
  par t ht h0 := by
    obtain ⟨u, hu, l, hl, e⟩ := H.par t ht h0
    exact ⟨u, hu, l, (hg l).2 hl, by rw [hf l hl _ (hpt u (by omega))]; exact e⟩

private theorem forIn_yield_inv {α β : Type} (l0 : List α) (R : List α → β → Prop) (g : α → β → β)
    (hg : ∀ pre a b, a ∈ l0 → R pre b → R (pre ++ [a]) (g a b)) :
    ∀ (l pre : List α) (b : β), (∀ a ∈ l, a ∈ l0) → R pre b →
      R (pre ++ l) (forIn (m := Id) l b fun a b => pure (ForInStep.yield (g a b)))
  | [], pre, b, _, h => by
    rw [List.append_nil, List.forIn_nil]
    exact h
  | a :: l, pre, b, hl, h => by
    rw [List.forIn_cons]
    have := forIn_yield_inv l0 R g hg l (pre ++ [a]) (g a b) (fun x hx => hl x (by simp [hx]))
      (hg pre a b (hl a (by simp)) h)
    rw [List.append_assoc, List.singleton_append] at this
    exact this

private theorem range_size (N : Nat) : ([0:N] : Std.Legacy.Range).size = N := by
  simp [Std.Legacy.Range.size]

private theorem forIn_range_yield {β : Type} (N : Nat) (R : List Nat → β → Prop) (g : Nat → β → β)
    (init : β) (h0 : R [] init) (hg : ∀ pre j b, j < N → R pre b → R (pre ++ [j]) (g j b)) :
    R (List.range' 0 N) (forIn (m := Id) [0:N] init fun j b => pure (ForInStep.yield (g j b))) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_size]
  have := forIn_yield_inv (List.range' 0 N) R g
    (fun pre a b ha hR => hg pre a b (by have := List.mem_range'_1.1 ha; omega) hR)
    (List.range' 0 N) [] init (fun a ha => ha) h0
  rw [List.nil_append] at this
  exact this

private theorem forIn_range_inv {β : Type} (R : Nat → β → Prop) (Q : β → Prop) (E : Nat)
    (f : Nat → β → Id (ForInStep β))
    (hf : ∀ j b, j < E → R j b →
      (∃ b', f j b = pure (.yield b') ∧ R (j + 1) b') ∨ (∃ b', f j b = pure (.done b') ∧ Q b'))
    (hE : ∀ b, R E b → Q b) :
    ∀ k a (init : β), a + k = E → R a init → Q (forIn (List.range' a k) init f)
  | 0, a, init, hk, h => by
    rw [List.range'_zero, List.forIn_nil]
    rw [Nat.add_zero] at hk
    subst hk
    exact hE init h
  | k + 1, a, init, hk, h => by
    rcases hf a init (by omega) h with ⟨b', hb, hR⟩ | ⟨b', hb, hQ⟩
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact forIn_range_inv R Q E f hf hE k (a + 1) b' (by omega) hR
    · rw [List.range'_succ, List.forIn_cons, hb]
      exact hQ

abbrev TSt := Table × Table × Table × Table

@[expose] def insL (letters : Array Table) (p h l : Nat) (s : TSt) : TSt :=
  if (s.1[ap letters[l]! p]! == none32) = true then
    (s.1.set! (ap letters[l]! p) (UInt32.ofNat s.2.1.size), s.2.1.push (UInt32.ofNat (ap letters[l]! p)),
      s.2.2.1.push (UInt32.ofNat h), s.2.2.2.push (UInt32.ofNat l))
  else s

@[expose] def insB (letters : Array Table) (p h l : Nat) (s : TSt) : Id (ForInStep TSt) :=
  if (s.1[ap letters[l]! p]! == none32) = true then
    pure (.yield (s.1.set! (ap letters[l]! p) (UInt32.ofNat s.2.1.size),
      s.2.1.push (UInt32.ofNat (ap letters[l]! p)), s.2.2.1.push (UInt32.ofNat h),
      s.2.2.2.push (UInt32.ofNat l)))
  else pure (.yield s)

@[expose] def tBody (letters : Array Table) (lv : Array Nat) (h : Nat) (s : TSt) : Id (ForInStep TSt) :=
  if h < s.2.1.size then
    (do let s' ← forIn lv s (insB letters (ap s.2.1 h) h); pure (.yield s'))
  else pure (.done s)

@[expose] def bfsRun (n root : Nat) (letters : Array Table) (lv : Array Nat) : TSt :=
  (forIn [0:n] (((Array.replicate n none32).set! root 0, #[UInt32.ofNat root], #[0], #[0]) : TSt)
    (tBody letters lv) : Id TSt)

theorem treeBFS_eq (n root : Nat) (letters : Array Table) (lv : Array Nat) :
    treeBFS n root letters lv = ⟨(bfsRun n root letters lv).2.1, (bfsRun n root letters lv).1,
      (bfsRun n root letters lv).2.2.1, (bfsRun n root letters lv).2.2.2⟩ := rfl

private theorem insB_eq (letters : Array Table) (p h l : Nat) (s : TSt) :
    insB letters p h l s = pure (.yield (insL letters p h l s)) := by
  unfold insB insL
  split <;> rfl

structure TInv' (n root : Nat) (letters : Array Table) (lv : Array Nat) (D : Nat → Nat → Prop)
    (pos pts par lab : Table) : Prop where
  pos_size : pos.size = n
  par_size : par.size = pts.size
  lab_size : lab.size = pts.size
  m_pos : 0 < pts.size
  m_le : pts.size ≤ n
  pt_lt : ∀ k < pts.size, ap pts k < n
  pt_pos : ∀ k < pts.size, ap pos (ap pts k) = k
  pos_pt : ∀ q < n, pos[q]! ≠ none32 → ap pos q < pts.size ∧ ap pts (ap pos q) = q
  root : ap pts 0 = root
  par : ∀ k, 0 < k → k < pts.size → ap par k < k ∧ ap lab k ∈ lv ∧
    ap letters[ap lab k]! (ap pts (ap par k)) = ap pts k
  clos : ∀ k < pts.size, ∀ l ∈ lv, D k l → ∃ k' < pts.size, ap pts k' = ap letters[l]! (ap pts k)

abbrev TInv (n root : Nat) (letters : Array Table) (lv : Array Nat) (D : Nat → Nat → Prop)
    (s : TSt) : Prop :=
  TInv' n root letters lv D s.1 s.2.1 s.2.2.1 s.2.2.2

theorem TInv.mono {n root : Nat} {letters : Array Table} {lv : Array Nat} {D D' : Nat → Nat → Prop}
    {s : TSt} (H : TInv n root letters lv D s) (hD : ∀ k l, l ∈ lv → D' k l → D k l) :
    TInv n root letters lv D' s :=
  { H with clos := fun k hk l hl hd => H.clos k hk l hl (hD k l hl hd) }

private theorem ap_push_lt {a : Table} {x : UInt32} {k : Nat} (hk : k < a.size) :
    ap (a.push x) k = ap a k := by
  unfold ap
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, getElem!_pos a k hk]

private theorem ap_push_eq (a : Table) (x : UInt32) : ap (a.push x) a.size = x.toNat := by
  unfold ap
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

private theorem ap_set_ne {a : Table} {q x : Nat} {v : UInt32} (hx : x ≠ q) :
    ap (a.set! q v) x = ap a x := by
  unfold ap
  rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hx)]

private theorem ap_push_eq' {a : Table} {x : UInt32} {k : Nat} (hk : k = a.size) :
    ap (a.push x) k = x.toNat := by
  rw [hk, ap_push_eq]

private theorem toNat_ofNat {x : Nat} (hx : x < 2 ^ 32) : (UInt32.ofNat x).toNat = x := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hx]

private theorem none32_toNat : (none32 ()).toNat = 4294967295 := rfl

private theorem le_of_inj {m n : Nat} {f : Nat → Nat} (hf : ∀ k < m, f k < n)
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) : m ≤ n := by
  have h := Finset.card_le_card_of_injOn f (s := Finset.range m) (t := Finset.range n)
    (by
      intro a ha
      have ha' : a < m := by simpa using ha
      simpa using hf a ha')
    (by
      intro a ha b hb e
      exact hinj a (by simpa using ha) b (by simpa using hb) e)
  simpa using h

private theorem insL_pre (letters : Array Table) (p h l : Nat) (s : TSt) :
    s.2.1.size ≤ (insL letters p h l s).2.1.size ∧
      ∀ k < s.2.1.size, ap (insL letters p h l s).2.1 k = ap s.2.1 k := by
  unfold insL
  split
  · exact ⟨by simp, fun k hk => ap_push_lt hk⟩
  · exact ⟨le_refl _, fun _ _ => rfl⟩

theorem tree_ins_step {n root : Nat} {letters : Array Table} {lv : Array Nat} {D : Nat → Nat → Prop}
    {s : TSt} {h l : Nat} (hn : n < 2 ^ 32) (hl32 : l < 2 ^ 32) (hl : l ∈ lv)
    (hL : ∀ x < n, ap letters[l]! x < n) (H : TInv n root letters lv D s) (hh : h < s.2.1.size)
    (hD : ∀ k l', D k l' → k ≤ h) :
    TInv n root letters lv (fun k l' => D k l' ∨ (k = h ∧ l' = l)) (insL letters (ap s.2.1 h) h l s) := by
  obtain ⟨pos, pts, par, lab⟩ := s
  change TInv' n root letters lv D pos pts par lab at H
  change h < pts.size at hh
  have hn' : n < 4294967296 := hn
  have hp : ap pts h < n := H.pt_lt h hh
  have hqn := hL _ hp
  unfold insL TInv
  dsimp only
  generalize hq' : ap letters[l]! (ap pts h) = q at hqn ⊢
  by_cases hc : (pos[q]! == none32) = true
  · rw [ite_eq_left hc]
    dsimp only
    have hnone : pos[q]! = none32 := by simpa using hc
    have hm := H.m_le
    have hfresh : ∀ k < pts.size, ap pts k ≠ q := by
      intro k hk e
      have h1 := H.pt_pos k hk
      rw [e] at h1
      unfold ap at h1
      rw [hnone, none32_toNat] at h1
      omega
    have hm1 : pts.size + 1 ≤ n := by
      refine le_of_inj (f := fun k => if k < pts.size then ap pts k else q) (fun k hk => ?_) ?_
      · by_cases hk' : k < pts.size
        · rw [ite_eq_left hk']
          exact H.pt_lt k hk'
        · rw [ite_eq_right hk']
          exact hqn
      · intro i hi j hj e
        by_cases hi' : i < pts.size <;> by_cases hj' : j < pts.size
        · rw [ite_eq_left hi', ite_eq_left hj'] at e
          rw [← H.pt_pos i hi', ← H.pt_pos j hj', e]
        · rw [ite_eq_left hi', ite_eq_right hj'] at e
          exact absurd e (hfresh i hi')
        · rw [ite_eq_right hi', ite_eq_left hj'] at e
          exact absurd e.symm (hfresh j hj')
        · omega
    have hpush : ∀ k < pts.size + 1, ap (pts.push (UInt32.ofNat q)) k =
        if k < pts.size then ap pts k else q := by
      intro k hk
      by_cases hk' : k < pts.size
      · rw [ite_eq_left hk', ap_push_lt hk']
      · rw [ite_eq_right hk']
        have : k = pts.size := by omega
        rw [this, ap_push_eq, toNat_ofNat (by omega)]
    have hposq : ap (pos.set! q (UInt32.ofNat pts.size)) q = pts.size := by
      unfold ap
      rw [Array.getElem!_set!_self _ _ _ (by rw [H.pos_size]; exact hqn), toNat_ofNat (by omega)]
    have hposx : ∀ x, x ≠ q → (pos.set! q (UInt32.ofNat pts.size))[x]! = pos[x]! := fun x hx =>
      Array.getElem!_set!_ne _ _ _ _ (Ne.symm hx)
    have hpar : par.size = pts.size := H.par_size
    have hlab : lab.size = pts.size := H.lab_size
    refine ⟨by rw [Array.size_set!, H.pos_size], by simp [hpar], by simp [hlab], by simp,
      by simp; omega, fun k hk => ?_, fun k hk => ?_, fun x hx hne => ?_, ?_, fun k hk0 hk => ?_,
      fun k hk l' hl' hd => ?_⟩
    · rw [Array.size_push] at hk
      rw [hpush k hk]
      split
      · exact H.pt_lt k (by assumption)
      · exact hqn
    · rw [Array.size_push] at hk
      rw [hpush k hk]
      split
      · rename_i hk'
        rw [ap_set_ne (hfresh k hk')]
        exact H.pt_pos k hk'
      · rename_i hk'
        rw [hposq]
        omega
    · rw [Array.size_push]
      by_cases hxq : x = q
      · subst hxq
        rw [hposq, ap_push_eq, toNat_ofNat (by omega)]
        exact ⟨by omega, rfl⟩
      · have hne' : pos[x]! ≠ none32 := by rwa [hposx x hxq] at hne
        obtain ⟨a1, a2⟩ := H.pos_pt x hx hne'
        have e : ap (pos.set! q (UInt32.ofNat pts.size)) x = ap pos x := by
          unfold ap
          rw [hposx x hxq]
        rw [e, ap_push_lt a1]
        exact ⟨by omega, a2⟩
    · rw [ap_push_lt H.m_pos]
      exact H.root
    · rw [Array.size_push] at hk
      by_cases hk' : k < pts.size
      · rw [ap_push_lt (by omega), ap_push_lt (by omega)]
        obtain ⟨a1, a2, a3⟩ := H.par k hk0 hk'
        rw [ap_push_lt (by omega), ap_push_lt hk']
        exact ⟨a1, a2, a3⟩
      · have hk2 : k = pts.size := by omega
        rw [hk2, ap_push_eq' hpar.symm, ap_push_eq' hlab.symm, toNat_ofNat (by omega), toNat_ofNat hl32,
          ap_push_lt hh, ap_push_eq, toNat_ofNat (by omega)]
        exact ⟨hh, hl, hq'⟩
    · rw [Array.size_push] at hk
      rcases hd with hd | ⟨rfl, rfl⟩
      · have hk' : k < pts.size := by have := hD k l' hd; omega
        obtain ⟨k', hk'1, e⟩ := H.clos k hk' l' hl' hd
        refine ⟨k', by rw [Array.size_push]; omega, ?_⟩
        rw [ap_push_lt hk'1, ap_push_lt hk', e]
      · refine ⟨pts.size, by rw [Array.size_push]; omega, ?_⟩
        rw [ap_push_eq, toNat_ofNat (by omega), ap_push_lt hh, hq']
  · rw [ite_eq_right hc]
    dsimp only
    have hne : pos[q]! ≠ none32 := by
      intro e
      exact hc (by rw [e]; exact beq_self_eq_true _)
    refine { H with clos := fun k hk l' hl' hd => ?_ }
    rcases hd with hd | ⟨rfl, rfl⟩
    · exact H.clos k hk l' hl' hd
    · obtain ⟨a1, a2⟩ := H.pos_pt q hqn hne
      exact ⟨ap pos q, a1, by rw [a2, hq']⟩

theorem inner_step {n root : Nat} {letters : Array Table} {lv : Array Nat} {s : TSt} {h : Nat}
    (hn : n < 2 ^ 32) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (hL : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    (H : TInv n root letters lv (fun k _ => k < h) s) (hh : h < s.2.1.size) :
    TInv n root letters lv (fun k _ => k < h + 1)
        (forIn (m := Id) lv.toList s fun l t => pure (ForInStep.yield (insL letters (ap s.2.1 h) h l t))) ∧
      h < (forIn (m := Id) lv.toList s fun l t =>
        pure (ForInStep.yield (insL letters (ap s.2.1 h) h l t))).2.1.size := by
  let R : List Nat → TSt → Prop := fun pre t =>
    TInv n root letters lv (fun k l => k < h ∨ (k = h ∧ l ∈ pre)) t ∧ h < t.2.1.size ∧
      ap t.2.1 h = ap s.2.1 h
  have hR := forIn_yield_inv lv.toList R (fun l t => insL letters (ap s.2.1 h) h l t)
    (fun pre a t ha ⟨Ht, ht, hp⟩ => by
      have ha' : a ∈ lv := by simpa using ha
      have Hs := tree_ins_step (D := fun k l => k < h ∨ (k = h ∧ l ∈ pre)) hn (hlv a ha') ha' (hL a ha') Ht ht
        (fun k l' hd => by rcases hd with hd | hd <;> omega)
      rw [hp] at Hs
      obtain ⟨p1, p2⟩ := insL_pre letters (ap s.2.1 h) h a t
      refine ⟨Hs.mono fun k l _ hd => ?_, by omega, by rw [p2 h ht, hp]⟩
      rcases hd with hd | ⟨hd1, hd2⟩
      · exact Or.inl (Or.inl hd)
      · rcases List.mem_append.1 hd2 with h2 | h2
        · exact Or.inl (Or.inr ⟨hd1, h2⟩)
        · exact Or.inr ⟨hd1, by simpa using h2⟩)
    lv.toList [] s (fun a ha => ha)
    ⟨H.mono fun k l _ hd => by rcases hd with hd | ⟨_, hd⟩; exact hd; simp at hd, hh, rfl⟩
  rw [List.nil_append] at hR
  obtain ⟨H1, H2, -⟩ := hR
  refine ⟨H1.mono fun k l hl hd => ?_, H2⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr ⟨hd, by simpa using hl⟩

theorem tBody_step {n root : Nat} {letters : Array Table} {lv : Array Nat} (hn : n < 2 ^ 32)
    (hlv : ∀ l ∈ lv, l < 2 ^ 32) (hL : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n) (h : Nat) (s : TSt)
    (H : TInv n root letters lv (fun k _ => k < h) s) (hh : h ≤ s.2.1.size) :
    (∃ s', tBody letters lv h s = pure (.yield s') ∧
        TInv n root letters lv (fun k _ => k < h + 1) s' ∧ h + 1 ≤ s'.2.1.size) ∨
      (∃ s', tBody letters lv h s = pure (.done s') ∧
        TInv n root letters lv (fun k _ => k < s'.2.1.size) s') := by
  by_cases hlt : h < s.2.1.size
  · left
    have e : tBody letters lv h s = pure (.yield (forIn (m := Id) lv.toList s fun l t =>
        pure (ForInStep.yield (insL letters (ap s.2.1 h) h l t)))) := by
      unfold tBody
      rw [ite_eq_left hlt, ← Array.forIn_toList]
      have : insB letters (ap s.2.1 h) h = fun l t => pure (ForInStep.yield (insL letters (ap s.2.1 h) h l t)) := by
        funext l t
        exact insB_eq _ _ _ _ _
      rw [this]
      rfl
    obtain ⟨H1, H2⟩ := inner_step hn hlv hL H hlt
    exact ⟨_, e, H1, H2⟩
  · right
    have e : h = s.2.1.size := by omega
    refine ⟨s, by unfold tBody; rw [ite_eq_right hlt], ?_⟩
    rw [← e]
    exact H

private theorem bfs_init {n root : Nat} {letters : Array Table} {lv : Array Nat} (hn : n < 2 ^ 32)
    (hr : root < n) :
    TInv n root letters lv (fun k _ => k < 0)
      ((Array.replicate n none32).set! root 0, #[UInt32.ofNat root], #[0], #[0]) := by
  have hrs : (Array.replicate n (none32 ())).size = n := Array.size_replicate
  have hpt : ap #[UInt32.ofNat root] 0 = root := by
    change (UInt32.ofNat root).toNat = root
    exact toNat_ofNat (by omega)
  have hpos : ap ((Array.replicate n (none32 ())).set! root 0) root = 0 := by
    unfold ap
    rw [Array.getElem!_set!_self _ _ _ (by rw [hrs]; exact hr)]
    rfl
  refine ⟨by rw [Array.size_set!, hrs], rfl, rfl, by simp, by simp; omega, fun k hk => ?_,
    fun k hk => ?_, fun q hq hne => ?_, hpt, fun k hk0 hk => ?_, fun k _ l _ hd => absurd hd (by omega)⟩
  · have : k = 0 := by simpa using hk
    subst this
    rw [hpt]
    exact hr
  · have : k = 0 := by simpa using hk
    subst this
    rw [hpt, hpos]
  · by_cases hqr : q = root
    · subst hqr
      rw [hpos, hpt]
      exact ⟨by simp, rfl⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hqr), getElem!_pos _ q (by rw [hrs]; exact hq),
        Array.getElem_replicate] at hne
      exact absurd rfl hne
  · have : k < 1 := by simpa using hk
    omega

structure BFSSpec (n root : Nat) (letters : Array Table) (lv : Array Nat) (T : Tree) : Prop where
  ok : CFSG.Perm.Native.treeOK n root T letters lv = true
  facts : TreeFacts T.pts.size root (· ∈ lv) (fun l x => ap letters[l]! x) (ap T.pts) (ap T.pos)
  pt_lt : ∀ t < T.pts.size, ap T.pts t < n
  pos_size : T.pos.size = n
  size_le : T.pts.size ≤ n

private theorem spec_of_closed {n root : Nat} {letters : Array Table} {lv : Array Nat} {s : TSt}
    (H : TInv n root letters lv (fun k _ => k < s.2.1.size) s) :
    BFSSpec n root letters lv ⟨s.2.1, s.1, s.2.2.1, s.2.2.2⟩ := by
  have hcl : ∀ k < s.2.1.size, ∀ l ∈ lv, ∃ k' < s.2.1.size, ap s.2.1 k' = ap letters[l]! (ap s.2.1 k) :=
    fun k hk l hl => H.clos k hk l hl hk
  refine ⟨?_, ⟨H.m_pos, H.root, H.pt_pos, fun t ht l hl => ?_, fun t ht h0 => ?_⟩, H.pt_lt,
    H.pos_size, H.m_le⟩
  · unfold CFSG.Perm.Native.treeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, CFSG.KS.TW.allIn_iff]
    refine ⟨⟨H.m_pos, H.root⟩, fun k hk => ?_⟩
    unfold CFSG.Perm.Native.treeAt
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      Array.all_eq_true', Array.contains_iff_mem]
    refine ⟨⟨⟨H.pt_lt k hk, H.pt_pos k hk⟩, fun l hl => ?_⟩, ?_⟩
    · obtain ⟨k', hk', e⟩ := hcl k hk l hl
      rw [← e, H.pt_pos k' hk']
      exact ⟨hk', rfl⟩
    · rcases Nat.eq_zero_or_pos k with h0 | h0
      · exact Or.inl h0
      · obtain ⟨a, b, c⟩ := H.par k h0 hk
        exact Or.inr ⟨⟨a, b⟩, c⟩
  · obtain ⟨k', hk', e⟩ := hcl t ht l hl
    dsimp only
    rw [← e, H.pt_pos k' hk']
    exact ⟨hk', rfl⟩
  · obtain ⟨a, b, c⟩ := H.par t h0 ht
    exact ⟨_, a, _, b, c⟩

theorem treeBFS_spec {n root : Nat} {letters : Array Table} {lv : Array Nat} (hn : n < 2 ^ 32)
    (hr : root < n) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (hL : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n) :
    BFSSpec n root letters lv (treeBFS n root letters lv) := by
  rw [treeBFS_eq]
  apply spec_of_closed
  unfold bfsRun
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_size]
  refine forIn_range_inv (fun j s => TInv n root letters lv (fun k _ => k < j) s ∧ j ≤ s.2.1.size)
    (fun s => TInv n root letters lv (fun k _ => k < s.2.1.size) s) n (tBody letters lv)
    (fun j s _ ⟨H, hj⟩ => ?_) (fun s ⟨H, hs⟩ => ?_) n 0 _ (Nat.zero_add n) ⟨bfs_init hn hr, by simp⟩
  · rcases tBody_step hn hlv hL j s H hj with ⟨s', e, H', h'⟩ | ⟨s', e, H'⟩
    · exact Or.inl ⟨s', e, H', h'⟩
    · exact Or.inr ⟨s', e, H'⟩
  · have : s.2.1.size = n := by have := H.m_le; omega
    rw [this]
    exact H

theorem bfs_of_facts {n m r : Nat} {letters : Array Table} {lv : Array Nat} {pt ix : Nat → Nat}
    (hn : n < 2 ^ 32) (hr : r < n) (hlv : ∀ l ∈ lv, l < 2 ^ 32)
    (hL : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    (H : TreeFacts m r (· ∈ lv) (fun l x => ap letters[l]! x) pt ix) :
    BFSSpec n r letters lv (treeBFS n r letters lv) ∧ (treeBFS n r letters lv).pts.size = m ∧
      ∀ q, (∃ t < m, pt t = q) ↔ ∃ t < (treeBFS n r letters lv).pts.size, ap (treeBFS n r letters lv).pts t = q := by
  have hB := treeBFS_spec hn hr hlv hL
  exact ⟨hB, (H.card_eq hB.facts).symm, H.mem_iff hB.facts⟩

theorem labelsOf_eq (n : Nat) (S : Array Tree) :
    labelsOf n S = (forIn (m := Id) [0:S.size] (Array.replicate n 0) fun j labs =>
      pure (ForInStep.yield (Id.run (forIn (m := Id) [0:S[j]!.pts.size] labs fun k labs' =>
        pure (ForInStep.yield (labs'.set! (ap S[j]!.pts k) j)))))) := rfl

theorem labelsOf_spec {n : Nat} {S : Array Tree} {lbl : Nat → Nat}
    (hlt : ∀ j < S.size, ∀ t < S[j]!.pts.size, ap S[j]!.pts t < n)
    (hlbl : ∀ j < S.size, ∀ t < S[j]!.pts.size, lbl (ap S[j]!.pts t) = j)
    (hcov : ∀ p < n, ∃ j < S.size, ∃ t < S[j]!.pts.size, ap S[j]!.pts t = p) :
    ∀ p < n, (labelsOf n S)[p]! = lbl p := by
  let C : List Nat → Nat → Prop := fun pre p =>
    ∃ j ∈ pre, j < S.size ∧ ∃ t < S[j]!.pts.size, ap S[j]!.pts t = p
  have key := forIn_range_yield S.size
    (fun pre (labs : Array Nat) => labs.size = n ∧ ∀ p < n, C pre p → labs[p]! = lbl p)
    (fun j labs => Id.run (forIn (m := Id) [0:S[j]!.pts.size] labs fun k labs' =>
      pure (ForInStep.yield (labs'.set! (ap S[j]!.pts k) j))))
    (Array.replicate n 0) ⟨by simp, fun p _ ⟨j, hj, _⟩ => by simp at hj⟩
    (fun pre j labs hj ⟨hs, hold⟩ => by
      have inner := forIn_range_yield S[j]!.pts.size
        (fun pre' (labs' : Array Nat) => labs'.size = n ∧ ∀ p < n,
          (C pre p ∨ ∃ t ∈ pre', ap S[j]!.pts t = p) → labs'[p]! = lbl p)
        (fun k labs' => labs'.set! (ap S[j]!.pts k) j) labs
        ⟨hs, fun p hp hc => by
          rcases hc with hc | ⟨t, ht, _⟩
          · exact hold p hp hc
          · simp at ht⟩
        (fun pre' t labs' ht ⟨hs', h'⟩ => by
          refine ⟨by rw [Array.size_set!, hs'], fun p hp hc => ?_⟩
          by_cases e : ap S[j]!.pts t = p
          · subst e
            rw [Array.getElem!_set!_self _ _ _ (by rw [hs']; exact hlt j hj t ht), hlbl j hj t ht]
          · rw [Array.getElem!_set!_ne _ _ _ _ e]
            refine h' p hp ?_
            rcases hc with hc | ⟨t', ht', e'⟩
            · exact Or.inl hc
            · rcases List.mem_append.1 ht' with h2 | h2
              · exact Or.inr ⟨t', h2, e'⟩
              · have : t' = t := by simpa using h2
                subst this
                exact absurd e' e)
      refine ⟨inner.1, fun p hp ⟨j', hj', hj's, t, ht, e⟩ => inner.2 p hp ?_⟩
      rcases List.mem_append.1 hj' with h2 | h2
      · exact Or.inl ⟨j', h2, hj's, t, ht, e⟩
      · have : j' = j := by simpa using h2
        subst this
        exact Or.inr ⟨t, List.mem_range'_1.2 ⟨by omega, by omega⟩, e⟩)
  intro p hp
  rw [labelsOf_eq]
  obtain ⟨j, hj, t, ht, e⟩ := hcov p hp
  exact key.2 p hp ⟨j, List.mem_range'_1.2 ⟨by omega, by omega⟩, hj, t, ht, e⟩

theorem mem_levelLetters (L : Array Table) (base : Array Nat) (l : Nat) :
    ∀ i, l ∈ levelLetters L base i ↔ l < L.size ∧ ∀ k < i, ap L[l]! base[k]! = base[k]!
  | 0 => by simp [levelLetters, Array.mem_range]
  | i + 1 => by
    rw [levelLetters, Array.mem_filter, mem_levelLetters L base l i, beq_iff_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · subst h
        exact h3
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun k hk => h2 k (by omega)⟩, h2 i (by omega)⟩

theorem fixB_iff {LT : Nat → Nat → Nat} {B : Nat → Nat} {i l : Nat} :
    fixB LT B i l = true ↔ ∀ k < i, lk (LT l) 32 (B k) = B k := by
  unfold fixB
  rw [allN_iff]
  simp only [strictB_eq, Nat.beq_eq]

theorem level_iff {n kL i : Nat} {L : Array Table} {LT : Nat → Nat → Nat} {base : Array Nat}
    (hLs : L.size = kL) (hLeq : ∀ l < kL, ∀ x < n, ap L[l]! x = lk (LT l) 32 x)
    (hi : i ≤ base.size) (hb : ∀ k < i, base[k]! < n) (l : Nat) :
    l ∈ levelLetters L base i ↔ l < kL ∧ fixB LT (getL 0 base.toList) i l = true := by
  rw [mem_levelLetters, fixB_iff, hLs]
  refine and_congr_right fun hl => forall_congr' fun k => forall_congr' fun hk => ?_
  rw [getL_array base (by omega), hLeq l hl _ (hb k hk)]

theorem onto_of_inj {m : Nat} {φ : Nat → Nat} (hφ : ∀ t < m, φ t < m)
    (hinj : ∀ a < m, ∀ b < m, φ a = φ b → a = b) : ∀ t < m, ∃ u < m, φ u = t := by
  have hsub : (Finset.range m).image φ ⊆ Finset.range m := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hφ u (Finset.mem_range.1 hu))
  have hcard : ((Finset.range m).image φ).card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hinj a (by simpa using ha) b (by simpa using hb) e
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  intro t ht
  have hmem : t ∈ (Finset.range m).image φ := by
    rw [heq]
    exact Finset.mem_range.2 ht
  obtain ⟨u, hu, e⟩ := Finset.mem_image.1 hmem
  exact ⟨u, Finset.mem_range.1 hu, e⟩

theorem right_inv {n : Nat} {g g' : Nat → Nat} (hg : ∀ x < n, g x < n) (hgg : ∀ x < n, g' (g x) = x) :
    ∀ x < n, g (g' x) = x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := onto_of_inj hg (fun a ha b hb e => by rw [← hgg a ha, ← hgg b hb, e]) x hx
  rw [hgg y hy]

theorem clos_inv {n m : Nat} {pt ix g g' : Nat → Nat} (hix : ∀ t < m, ix (pt t) = t)
    (hpt : ∀ t < m, pt t < n) (hgg : ∀ x < n, g' (g x) = x)
    (hcl : ∀ t < m, ix (g (pt t)) < m ∧ pt (ix (g (pt t))) = g (pt t)) :
    ∀ t < m, ∃ u < m, g' (pt t) = pt u := by
  have hon := onto_of_inj (m := m) (φ := fun t => ix (g (pt t))) (fun t ht => (hcl t ht).1)
    (fun a ha b hb e => by
      have e1 : g (pt a) = g (pt b) := by
        rw [← (hcl a ha).2, ← (hcl b hb).2]
        exact congrArg pt e
      have e2 := congrArg g' e1
      rw [hgg _ (hpt a ha), hgg _ (hpt b hb)] at e2
      rw [← hix a ha, ← hix b hb, e2])
  intro t ht
  obtain ⟨u, hu, e⟩ := hon t ht
  have e' : ix (g (pt u)) = t := e
  have hpu : pt t = g (pt u) := by
    rw [← e']
    exact (hcl u hu).2
  exact ⟨u, hu, by rw [hpu, hgg _ (hpt u hu)]⟩

theorem clos_all {n kL m i : Nat} {LT : Nat → Nat → Nat} {B pt ix : Nat → Nat}
    (hkE : kL % 2 = 0) (hLn : ∀ l < kL, ∀ x < n, lk (LT l) 32 x < n)
    (hpair : ∀ j, 2 * j + 1 < kL → ∀ x < n, lk (LT (2 * j + 1)) 32 (lk (LT (2 * j)) 32 x) = x)
    (hB : ∀ k < i, B k < n) (hix : ∀ t < m, ix (pt t) = t) (hpt : ∀ t < m, pt t < n)
    (hev : ∀ j < kL / 2, fixB LT B i (2 * j) = true → ∀ t < m,
      ix (lk (LT (2 * j)) 32 (pt t)) < m ∧ pt (ix (lk (LT (2 * j)) 32 (pt t))) = lk (LT (2 * j)) 32 (pt t)) :
    ∀ l < kL, fixB LT B i l = true → ∀ t < m,
      ix (lk (LT l) 32 (pt t)) < m ∧ pt (ix (lk (LT l) 32 (pt t))) = lk (LT l) 32 (pt t) := by
  intro l hl hf t ht
  obtain ⟨j, rfl | rfl⟩ : ∃ j, l = 2 * j ∨ l = 2 * j + 1 := ⟨l / 2, by omega⟩
  · exact hev j (by omega) hf t ht
  · have hg : ∀ x < n, lk (LT (2 * j)) 32 x < n := hLn _ (by omega)
    have hgg := hpair j hl
    have hf0 : fixB LT B i (2 * j) = true := by
      rw [fixB_iff] at hf ⊢
      intro k hk
      have := right_inv (g := fun x => lk (LT (2 * j)) 32 x) (g' := fun x => lk (LT (2 * j + 1)) 32 x)
        hg hgg (B k) (hB k hk)
      have e : lk (LT (2 * j)) 32 (lk (LT (2 * j + 1)) 32 (B k)) = B k := this
      rw [hf k hk] at e
      exact e
    obtain ⟨u, hu, e⟩ := clos_inv (pt := pt) (ix := ix) (g := fun x => lk (LT (2 * j)) 32 x)
      (g' := fun x => lk (LT (2 * j + 1)) 32 x) hix hpt hgg (hev j (by omega) hf0) t ht
    have e' : lk (LT (2 * j + 1)) 32 (pt t) = pt u := e
    rw [e', hix u hu]
    exact ⟨hu, rfl⟩

theorem tree_dec {n kL m i r : Nat} {LT : Nat → Nat → Nat} {B Ot IX Op Ol : Nat → Nat}
    (h : ∀ t < m, CFSG.KC.VecK.treeAt n kL m i r LT B Ot IX Op Ol t = true) :
    ∀ t < m, lk Ot 32 t < n ∧ lk IX 32 (lk Ot 32 t) = t ∧
      (∀ j < kL / 2, fixB LT B i (2 * j) = false ∨
        (lk IX 32 (lk (LT (2 * j)) 32 (lk Ot 32 t)) < m ∧
          lk Ot 32 (lk IX 32 (lk (LT (2 * j)) 32 (lk Ot 32 t))) = lk (LT (2 * j)) 32 (lk Ot 32 t))) ∧
      (if t = 0 then lk Ot 32 t = r else lk Op 32 t < t ∧ lk Ol 32 t < kL ∧ fixB LT B i (lk Ol 32 t) = true ∧
        lk (LT (lk Ol 32 t)) 32 (lk Ot 32 (lk Op 32 t)) = lk Ot 32 t) := by
  intro t ht
  have := h t ht
  unfold CFSG.KC.VecK.treeAt at this
  simp only [strictB_eq, andB_eq, orB_eq, notB_eq, bif_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq, allN_iff] at this
  exact this

theorem tree_root {n kL m i r : Nat} {LT : Nat → Nat → Nat} {B Ot IX Op Ol : Nat → Nat} (hm : 0 < m)
    (h : ∀ t < m, CFSG.KC.VecK.treeAt n kL m i r LT B Ot IX Op Ol t = true) : r < n := by
  have d := tree_dec h 0 hm
  have e := d.2.2.2
  rw [ite_eq_left rfl] at e
  rw [← e]
  exact d.1

theorem kernel_tree {n kL m i r : Nat} {LT : Nat → Nat → Nat} {B Ot IX Op Ol : Nat → Nat}
    (hkE : kL % 2 = 0) (hLn : ∀ l < kL, ∀ x < n, lk (LT l) 32 x < n)
    (hpair : ∀ j, 2 * j + 1 < kL → ∀ x < n, lk (LT (2 * j + 1)) 32 (lk (LT (2 * j)) 32 x) = x)
    (hB : ∀ k < i, B k < n)
    (hm : 0 < m) (h : ∀ t < m, CFSG.KC.VecK.treeAt n kL m i r LT B Ot IX Op Ol t = true) :
    TreeFacts m r (fun l => l < kL ∧ fixB LT B i l = true) (fun l x => lk (LT l) 32 x) (lk Ot 32) (lk IX 32) ∧
      ∀ t < m, lk Ot 32 t < n := by
  have dec := tree_dec h
  have hcl := clos_all (pt := lk Ot 32) (ix := lk IX 32) hkE hLn hpair hB (fun t ht => (dec t ht).2.1)
    (fun t ht => (dec t ht).1) (fun j hj hf t ht => by
      rcases (dec t ht).2.2.1 j hj with h1 | h1
      · rw [hf] at h1
        exact absurd h1 (by decide)
      · exact h1)
  refine ⟨⟨hm, ?_, fun t ht => (dec t ht).2.1, fun t ht l ⟨hl, hf⟩ => hcl l hl hf t ht, fun t ht h0 => ?_⟩,
    fun t ht => (dec t ht).1⟩
  · have := (dec 0 hm).2.2.2
    rw [ite_eq_left rfl] at this
    exact this
  · have := (dec t ht).2.2.2
    rw [ite_eq_right (by omega)] at this
    obtain ⟨a, b, c, e⟩ := this
    exact ⟨_, a, _, ⟨b, c⟩, e⟩

theorem kernel_sub {n kL m j r : Nat} {LT : Nat → Nat → Nat} {B St LB PS Sp Sl : Nat → Nat}
    (hkE : kL % 2 = 0) (hLn : ∀ l < kL, ∀ x < n, lk (LT l) 32 x < n)
    (hpair : ∀ j, 2 * j + 1 < kL → ∀ x < n, lk (LT (2 * j + 1)) 32 (lk (LT (2 * j)) 32 x) = x)
    (hB : ∀ k < 1, B k < n)
    (hm : 0 < m) (h : ∀ t < m, subAt n kL m j r LT B St LB PS Sp Sl t = true) :
    TreeFacts m r (fun l => l < kL ∧ fixB LT B 1 l = true) (fun l x => lk (LT l) 32 x) (lk St 32) (lk PS 32) ∧
      ∀ t < m, lk St 32 t < n ∧ lk LB 32 (lk St 32 t) = j := by
  have dec : ∀ t < m, lk St 32 t < n ∧ lk LB 32 (lk St 32 t) = j ∧ lk PS 32 (lk St 32 t) = t ∧
      (∀ k < kL / 2, fixB LT B 1 (2 * k) = false ∨
        (lk LB 32 (lk (LT (2 * k)) 32 (lk St 32 t)) = j ∧ lk PS 32 (lk (LT (2 * k)) 32 (lk St 32 t)) < m ∧
          lk St 32 (lk PS 32 (lk (LT (2 * k)) 32 (lk St 32 t))) = lk (LT (2 * k)) 32 (lk St 32 t))) ∧
      (if t = 0 then lk St 32 t = r else lk Sp 32 t < t ∧ lk Sl 32 t < kL ∧ fixB LT B 1 (lk Sl 32 t) = true ∧
        lk (LT (lk Sl 32 t)) 32 (lk St 32 (lk Sp 32 t)) = lk St 32 t) := by
    intro t ht
    have := h t ht
    unfold subAt at this
    simp only [strictB_eq, andB_eq, orB_eq, notB_eq, bif_eq, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq, allN_iff] at this
    exact this
  have hcl := clos_all (pt := lk St 32) (ix := lk PS 32) hkE hLn hpair hB (fun t ht => (dec t ht).2.2.1)
    (fun t ht => (dec t ht).1) (fun k hk hf t ht => by
      rcases (dec t ht).2.2.2.1 k hk with h1 | h1
      · rw [hf] at h1
        exact absurd h1 (by decide)
      · exact h1.2)
  refine ⟨⟨hm, ?_, fun t ht => (dec t ht).2.2.1, fun t ht l ⟨hl, hf⟩ => hcl l hl hf t ht, fun t ht h0 => ?_⟩,
    fun t ht => ⟨(dec t ht).1, (dec t ht).2.1⟩⟩
  · have := (dec 0 hm).2.2.2.2
    rw [ite_eq_left rfl] at this
    exact this
  · have := (dec t ht).2.2.2.2
    rw [ite_eq_right (by omega)] at this
    obtain ⟨a, b, c, e⟩ := this
    exact ⟨_, a, _, ⟨b, c⟩, e⟩

theorem bfs_of_kernel {n kL m i r : Nat} {L : Array Table} {LT : Nat → Nat → Nat} {base : Array Nat}
    {pt ix : Nat → Nat} (hn : n < 2 ^ 32) (hkL : kL < 2 ^ 32) (hLs : L.size = kL)
    (hLeq : ∀ l < kL, ∀ x < n, ap L[l]! x = lk (LT l) 32 x) (hLn : ∀ l < kL, ∀ x < n, lk (LT l) 32 x < n)
    (hi : i ≤ base.size) (hb : ∀ k < i, base[k]! < n)
    (H : TreeFacts m r (fun l => l < kL ∧ fixB LT (getL 0 base.toList) i l = true)
      (fun l x => lk (LT l) 32 x) pt ix) (hpt : ∀ t < m, pt t < n) :
    BFSSpec n r L (levelLetters L base i) (treeBFS n r L (levelLetters L base i)) ∧
      (treeBFS n r L (levelLetters L base i)).pts.size = m ∧
      ∀ q, (∃ t < m, pt t = q) ↔ ∃ t < (treeBFS n r L (levelLetters L base i)).pts.size,
        ap (treeBFS n r L (levelLetters L base i)).pts t = q := by
  have hlv := level_iff hLs hLeq hi hb
  have hr : r < n := by rw [← H.root]; exact hpt 0 H.m_pos
  refine bfs_of_facts hn hr (fun l hl => by have := ((hlv l).1 hl).1; omega)
    (fun l hl x hx => by rw [hLeq l ((hlv l).1 hl).1 x hx]; exact hLn l ((hlv l).1 hl).1 x hx)
    (H.congr hpt hlv fun l hl x hx => hLeq l hl.1 x hx)

private theorem letAt_lt {d n N : Nat} {P T : Nat → Nat} {h : Nat} (hh : letAt d n N P T h = true) :
    lk T 32 h < n := by
  unfold letAt at hh
  simp only [strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq] at hh
  exact hh.1

theorem pair_of_inv {n kL : Nat} {L : Array Table} {LT : Nat → Nat → Nat}
    (hL : L.size = kL ∧ ∀ l < kL, L[l]!.size = n ∧ ∀ x < n, ap L[l]! x = lk (LT l) 32 x)
    (hLn : ∀ l < kL, ∀ x < n, lk (LT l) 32 x < n)
    (hinv : ∀ j < L.size / 2, invOK n L[2 * j]! L[2 * j + 1]! = true) :
    ∀ j, 2 * j + 1 < kL → ∀ x < n, lk (LT (2 * j + 1)) 32 (lk (LT (2 * j)) 32 x) = x := by
  intro j hj x hx
  have hi := hinv j (by rw [hL.1]; omega)
  unfold invOK at hi
  rw [CFSG.KS.TW.allIn_iff] at hi
  have h1 := hi x hx
  rw [beq_iff_eq, (hL.2 _ (by omega)).2 x hx, (hL.2 _ hj).2 _ (hLn _ (by omega) x hx)] at h1
  exact h1

theorem chainTrees_get {n : Nat} {L : Array Table} {base : Array Nat} {i : Nat} (hi : i < base.size) :
    (chainTrees n L base)[i]! = treeBFS n base[i]! L (levelLetters L base i) := by
  unfold chainTrees
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem chainTrees_spec (D : VecData) {d kL : Nat} {L : Array Table} {LM : List Nat} {P : Nat → Nat}
    {LT Ot IX Op Ol : Nat → Nat → Nat}
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hkL32 : Nat.blt kL (pw2 (nat_lit 32)) = true)
    (hL : L.size = kL ∧ ∀ l < kL, L[l]!.size = D.n ∧ ∀ x < D.n, ap L[l]! x = lk (LT l) 32 x)
    (hLT : ∀ j < kL, ∀ h < D.n, letAt d D.n (getL (nat_lit 0) LM j) P (LT j) h = true)
    (hkE : kL % 2 = 0) (hinv : ∀ j < L.size / 2, invOK D.n L[2 * j]! L[2 * j + 1]! = true)
    (hchain : andB (Nat.beq D.base.size D.orbSizes.length) (andB (Nat.beq D.qb.size D.base.size)
      (andB (allL (fun s => Nat.blt (nat_lit 0) s) D.orbSizes)
      (andB (allN D.basis.size fun t => Nat.blt (getL (nat_lit 0) D.basis.toList t) D.n)
      (allN D.base.size fun i => strictB (getL (nat_lit 0) D.qb.toList i) fun x =>
        andB (Nat.blt x D.basis.size)
          (Nat.beq (getL (nat_lit 0) D.basis.toList x) (getL (nat_lit 0) D.base.toList i)))))) = true)
    (htree : ∀ i < D.base.size, ∀ t < getL (nat_lit 0) D.orbSizes i,
      CFSG.KC.VecK.treeAt D.n kL (getL (nat_lit 0) D.orbSizes i) i (getL (nat_lit 0) D.base.toList i) LT
        (getL (nat_lit 0) D.base.toList) (Ot i) (IX i) (Op i) (Ol i) t = true) :
    orbitSizes (chainTrees D.n L D.base) = D.orbSizes ∧
      ∀ i < D.base.size, (chainTrees D.n L D.base)[i]! = treeBFS D.n D.base[i]! L (levelLetters L D.base i) ∧
        BFSSpec D.n D.base[i]! L (levelLetters L D.base i) (chainTrees D.n L D.base)[i]! := by
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, pw2_eq] at hn
  rw [Nat.blt_eq, pw2_eq] at hkL32
  have hn32 : D.n < 2 ^ 32 := lt_trans hn.2 (by decide)
  simp only [andB_eq, Bool.and_eq_true] at hchain
  obtain ⟨hlen, -, hpos, -, -⟩ := hchain
  have hlen := Nat.eq_of_beq_eq_true hlen
  rw [allL_iff] at hpos
  have hLn : ∀ l < kL, ∀ x < D.n, lk (LT l) 32 x < D.n := fun l hl x hx => letAt_lt (hLT l hl x hx)
  have hmpos : ∀ i < D.base.size, 0 < getL 0 D.orbSizes i := fun i hi => by
    have hi' : i < D.orbSizes.length := by omega
    rw [getL_list hi']
    have := hpos _ (List.getElem_mem hi')
    simpa using this
  have hpair := pair_of_inv hL hLn hinv
  have hb : ∀ k < D.base.size, D.base[k]! < D.n := fun k hk => by
    have := tree_root (hmpos k hk) (htree k hk)
    rw [getL_array _ hk] at this
    exact this
  have hK : ∀ i (hi : i < D.base.size), _ := fun i hi => kernel_tree hkE hLn hpair
    (fun k hk => by rw [getL_array _ (by omega)]; exact hb k (by omega)) (hmpos i hi) (htree i hi)
  have hBFS : ∀ i (hi : i < D.base.size), _ := fun i hi =>
    bfs_of_kernel hn32 hkL32 hL.1 (fun l hl => (hL.2 l hl).2) hLn (by omega) (fun k hk => hb k (by omega))
      (hK i hi).1 (hK i hi).2
  refine ⟨?_, fun i hi => ⟨chainTrees_get hi, ?_⟩⟩
  · unfold orbitSizes
    apply List.ext_getElem
    · simp [chainTrees, hlen]
    · intro i h1 h2
      have hi : i < D.base.size := by simpa [chainTrees] using h1
      rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos _ i (by simpa [chainTrees] using hi),
        chainTrees_get hi, ← getL_array _ hi, (hBFS i hi).2.1, getL_list h2]
  · rw [chainTrees_get hi, ← getL_array _ hi]
    exact (hBFS i hi).1

private theorem map_get {S : Array Nat} {f : Nat → Tree} {j : Nat} (hj : j < S.size) :
    (S.map f)[j]! = f S[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem subChecks_ok (D : VecData) {d kL : Nat} {L : Array Table} {LM : List Nat} {P : Nat → Nat}
    {LT : Nat → Nat → Nat} {STs SPs SLs : List (Nat → Nat)} {LB PS : Nat → Nat}
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hkL32 : Nat.blt kL (pw2 (nat_lit 32)) = true)
    (hL : L.size = kL ∧ ∀ l < kL, L[l]!.size = D.n ∧ ∀ x < D.n, ap L[l]! x = lk (LT l) 32 x)
    (hLT : ∀ j < kL, ∀ h < D.n, letAt d D.n (getL (nat_lit 0) LM j) P (LT j) h = true)
    (hkE : kL % 2 = 0) (hinv : ∀ j < L.size / 2, invOK D.n L[2 * j]! L[2 * j + 1]! = true)
    (hsub0 : andB (Nat.blt (nat_lit 0) D.base.size) (andB (Nat.beq (getL (nat_lit 0) D.base.toList 0) 0)
      (andB (Nat.blt (nat_lit 0) D.subReps.size) (andB (Nat.beq (getL (nat_lit 0) D.subReps.toList 0) 0)
      (andB (Nat.beq D.subSizes.length D.subReps.size)
        (allL (fun s => Nat.blt (nat_lit 0) s) D.subSizes))))) = true)
    (hsub : ∀ j < D.subReps.size, ∀ t < getL (nat_lit 0) D.subSizes j,
      subAt D.n kL (getL (nat_lit 0) D.subSizes j) j (getL (nat_lit 0) D.subReps.toList j) LT
        (getL (nat_lit 0) D.base.toList) (getF STs j) LB PS (getF SPs j) (getF SLs j) t = true)
    (hlab : ∀ p < D.n, labAt D.subReps.size D.subSizes STs LB PS p = true) :
    subChecks D L (levelLetters L D.base 1)
      (D.subReps.map fun r => treeBFS D.n r L (levelLetters L D.base 1)) = true := by
  rw [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, pw2_eq] at hn
  rw [Nat.blt_eq, pw2_eq] at hkL32
  have hn32 : D.n < 2 ^ 32 := lt_trans hn.2 (by decide)
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at hsub0
  obtain ⟨hb0, hB0, hk0, hR0, hlen, hpos⟩ := hsub0
  have hB0 := Nat.eq_of_beq_eq_true hB0
  have hR0 := Nat.eq_of_beq_eq_true hR0
  have hlen := Nat.eq_of_beq_eq_true hlen
  rw [allL_iff] at hpos
  have hLn : ∀ l < kL, ∀ x < D.n, lk (LT l) 32 x < D.n := fun l hl x hx => letAt_lt (hLT l hl x hx)
  have hmpos : ∀ j < D.subReps.size, 0 < getL 0 D.subSizes j := fun j hj => by
    have hj' : j < D.subSizes.length := by omega
    rw [getL_list hj']
    have := hpos _ (List.getElem_mem hj')
    simpa using this
  have hb : ∀ k < 1, D.base[k]! < D.n := fun k hk => by
    have : k = 0 := by omega
    subst this
    rw [← getL_array _ hb0, hB0]
    exact hn.1
  have hK : ∀ j (hj : j < D.subReps.size), _ := fun j hj => kernel_sub hkE hLn (pair_of_inv hL hLn hinv)
    (fun k hk => by rw [getL_array _ (by omega)]; exact hb k hk) (hmpos j hj) (hsub j hj)
  have hBFS : ∀ j (hj : j < D.subReps.size), _ := fun j hj =>
    bfs_of_kernel hn32 hkL32 hL.1 (fun l hl => (hL.2 l hl).2) hLn (by omega) hb (hK j hj).1
      (fun t ht => ((hK j hj).2 t ht).1)
  have hS : ∀ j < D.subReps.size, (D.subReps.map fun r => treeBFS D.n r L (levelLetters L D.base 1))[j]! =
      treeBFS D.n (getL 0 D.subReps.toList j) L (levelLetters L D.base 1) := fun j hj => by
    rw [map_get hj, getL_array _ hj]
  generalize hSd : (D.subReps.map fun r => treeBFS D.n r L (levelLetters L D.base 1)) = S at hS
  have hSs : S.size = D.subReps.size := by rw [← hSd, Array.size_map]
  have hlabs : ∀ p < D.n, (labelsOf D.n S)[p]! = lk LB 32 p := by
    refine labelsOf_spec (fun j hj t ht => ?_) (fun j hj t ht => ?_) (fun p hp => ?_)
    · rw [hSs] at hj
      rw [hS j hj] at ht ⊢
      exact (hBFS j hj).1.pt_lt t ht
    · rw [hSs] at hj
      rw [hS j hj] at ht ⊢
      obtain ⟨t', ht', e⟩ := ((hBFS j hj).2.2 _).2 ⟨t, ht, rfl⟩
      rw [← e]
      exact ((hK j hj).2 t' ht').2
    · have hl := hlab p hp
      unfold labAt at hl
      simp only [strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hl
      obtain ⟨h1, h2, h3⟩ := hl
      refine ⟨lk LB 32 p, by rw [hSs]; exact h1, ?_⟩
      rw [hS _ h1]
      exact ((hBFS _ h1).2.2 p).1 ⟨_, h2, h3⟩
  unfold subChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, CFSG.KS.TW.allIn_iff, inTreeB]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hb0, ?_⟩, hk0⟩, ?_⟩, hSs⟩, ?_⟩, fun j hj => ?_⟩, fun p hp => ?_⟩, fun j hj t ht => ?_⟩
  · rw [← getL_array _ hb0, hB0]
  · rw [← getL_array _ hk0, hR0]
  · apply List.ext_getElem
    · simp [hSs, hlen]
    · intro j h1 h2
      have hj : j < D.subReps.size := by simpa [hSs] using h1
      rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos _ j (by omega), hS j hj,
        (hBFS j hj).2.1, getL_list h2]
  · rw [hS j hj, ← getL_array _ hj]
    exact (hBFS j hj).1.ok
  · have hl := hlab p hp
    unfold labAt at hl
    simp only [strictB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    rw [hlabs p hp, hS _ h1]
    refine ⟨h1, ?_⟩
    obtain ⟨t, ht, e⟩ := ((hBFS _ h1).2.2 p).1 ⟨_, h2, h3⟩
    have hix := (hBFS _ h1).1.facts.ix_pt t ht
    rw [e] at hix
    rw [hix]
    exact ⟨ht, e⟩
  · rw [hS j hj] at ht ⊢
    rw [hlabs _ ((hBFS j hj).1.pt_lt t ht)]
    obtain ⟨t', ht', e⟩ := ((hBFS j hj).2.2 _).2 ⟨t, ht, rfl⟩
    rw [← e]
    exact ((hK j hj).2 t' ht').2

end CFSG.KC.VecK

end

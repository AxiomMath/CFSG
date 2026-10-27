
module

public import Certificates.Data.Kernel.SporSch.Co1GenK
public import Certificates.Data.Kernel.SporSch.Co1Elem
public import CFSG.Sporadic.Schreier.Co1GenCheckInputs
import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.KS.Raw

@[expose] def stepVP (cols : Array Rows) (q g v : Nat) : Nat :=
  canon q (vecMulN 24 (cols.getD g #[]) v)

@[expose] def bfsP (cols : Array Rows) (q : Nat) (gens : List Nat) (root bound : Nat) :
    Array (Nat × Nat × Nat) :=
  Id.run do
    let mut seen : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity 200000).insert root
    let mut out : Array (Nat × Nat × Nat) := #[(root, 0, 0)]
    for i in [0:bound] do
      if h : i < out.size then
        let v := out[i].1
        for g in gens do
          let w := stepVP cols q g v
          if !seen.contains w then
            seen := seen.insert w
            out := out.push (w, i, g)
    return out

@[expose] def treeOKP (cols : Array Rows) (q : Nat) (gens : List Nat) (root n : Nat)
    (t : Array (Nat × Nat × Nat)) : Bool :=
  t.size == n && (t.getD 0 (0, 0, 0)).1 == root &&
    (List.range n).all (fun m => decide ((t.getD m (0, 0, 0)).1 < 2 ^ 24) &&
      canon q (t.getD m (0, 0, 0)).1 == (t.getD m (0, 0, 0)).1 &&
      (m == 0 || (decide ((t.getD m (0, 0, 0)).2.1 < m) && gens.contains (t.getD m (0, 0, 0)).2.2 &&
        (t.getD m (0, 0, 0)).1 ==
          stepVP cols q (t.getD m (0, 0, 0)).2.2 (t.getD (t.getD m (0, 0, 0)).2.1 (0, 0, 0)).1))) &&
    strictSorted ((t.toList.map (·.1)).mergeSort fun a b => decide (a ≤ b))

@[expose] def fixOKP (cols : Array Rows) (qs bs : List Nat) (gs : List (List Nat)) (i : Nat) : Bool :=
  (gs.getD i []).all fun j => decide (j < 93) &&
    vecMulN 24 (cols.getD j #[]) (qs.getD i 0) == qs.getD i 0 &&
    (List.range i).all fun l => vecMulN 24 (cols.getD j #[]) (qs.getD l 0) == qs.getD l 0 &&
      (vecMulN 24 (cols.getD j #[]) (bs.getD l 0) == bs.getD l 0 ||
        vecMulN 24 (cols.getD j #[]) (bs.getD l 0) == bs.getD l 0 ^^^ qs.getD l 0)

@[expose] def genP (cols : Array Rows) (qs bs : List Nat) (gs : List (List Nat)) (ns : List Nat) :
    Bool :=
  (List.range 7).all fun i => decide (bs.getD i 0 < 2 ^ 24) && decide (qs.getD i 0 < 2 ^ 24) &&
    fixOKP cols qs bs gs i &&
    treeOKP cols (qs.getD i 0) (gs.getD i []) (bs.getD i 0) (ns.getD i 0)
      (bfsP cols (qs.getD i 0) (gs.getD i []) (bs.getD i 0) 100000)

namespace GenL

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

private theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem orRec (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

private theorem foldr_range_add (f : Nat → Nat → Nat) (a b s : Nat) :
    (List.range (a + b)).foldr f s =
      (List.range a).foldr f ((List.range b).foldr (fun l s => f (a + l) s) s) := by
  rw [List.range_add, List.foldr_append, List.foldr_map]

private theorem foldN_rec_eq (f : Nat → Nat → Nat) (h : Nat) : ∀ x : Nat,
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) h x
      = (List.range (h * 64)).foldr f x := by
  induction h with
  | zero => intro x; rfl
  | succ h ih =>
    intro x
    have hs : Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
        (h + 1) x
        = strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) x)
            (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
              (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
              h) :=
      rfl
    have e : (h + 1) * 64 = h * 64 + 64 := by omega
    rw [hs, MatL.strictN_eq, ih, MatL.foldBlk_eq, MatL.shiftLeft_six h, e,
      foldr_range_add f (h * 64) 64 x]

private theorem foldN_eq' (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  refine Eq.trans (foldN_rec_eq f (Nat.shiftRight n (nat_lit 6))
    (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
      (Nat.land n (nat_lit 63)) s)) ?_
  have e : n / 64 * 64 + n % 64 = n := by omega
  have e6 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  have e63 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  rw [MatL.foldBlk_eq, MatL.shiftLeft_six, e63, e6,
    ← foldr_range_add f (n / 64 * 64) (n % 64) s, e]

private theorem foldr_range_succ (h : Nat → Nat → Nat) (k s : Nat) :
    (List.range (k + 1)).foldr h s =
      h 0 ((List.range k).foldr (fun x y => h (Nat.succ x) y) s) := by
  rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]

private theorem foldr_rev_eq_foldl (g : Nat → Nat → Nat) (n : Nat) : ∀ s : Nat,
    (List.range n).foldr (fun i s => g (n - 1 - i) s) s
      = (List.range n).foldl (fun s i => g i s) s := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    have hf : (fun (x : Nat) (y : Nat) => g (n + 1 - 1 - Nat.succ x) y)
        = (fun (x : Nat) (y : Nat) => g (n - 1 - x) y) := by
      funext x y
      congr 1
      omega
    rw [foldr_range_succ, hf, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih s, Nat.sub_zero, Nat.add_sub_cancel]

private theorem foldUp_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp n f s = (List.range n).foldl (fun s i => f i s) s :=
  (foldN_eq' n (fun i s => f (Nat.sub (Nat.sub n (nat_lit 1)) i) s) s).trans
    (foldr_rev_eq_foldl f n s)

private theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nget l i = _
      rw [ih]
      simp

private theorem allLtN_iff (K : Nat) (l : List Nat) : allLtN K l = true ↔ ∀ x ∈ l, x < K := by
  induction l with
  | nil => simp [allLtN]
  | cons x l ih =>
    have e : allLtN K (x :: l) = (Nat.blt x K && allLtN K l) := MatL.bAnd_eq _ _
    simp [e, ih, Nat.blt_eq]

private theorem ptK_lt (T : Nat → Nat) (k : Nat) : ptK T k < 2 ^ 24 := by
  have e : ptK T k = recK T k &&& 16777215 := rfl
  rw [e]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem ptK_lt' (T : Nat → Nat) (k : Nat) : ptK T k < 16777216 := ptK_lt T k

private theorem canonK_eq (q v : Nat) : canonK q v = canon q v := by
  have ex : Nat.xor v q = v ^^^ q := rfl
  unfold canonK canon
  rw [MatL.strictN_eq, MatL.nIf_eq, ex, Nat.min_def]
  by_cases h : v ≤ v ^^^ q
  · rw [ite_eq_left (by simpa using h), ite_eq_left h]
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]

private theorem unpack_powK (X : Nat) : ∀ e, unpack 24 24 (powK X e) = pow (unpack 24 24 X) e
  | 0 => MatL.unpack_idM
  | e + 1 => by
    change unpack 24 24 (strictN (powK X e) (fun Y => mulK Y X)) =
      mul (pow (unpack 24 24 X) e) (unpack 24 24 X)
    rw [MatL.strictN_eq, MatL.unpack_mulK, unpack_powK X e]

private theorem fixQK_spec {M : Nat → Nat} {qs bs : List Nat} {i : Nat} : ∀ {gens : List Nat},
    fixQK M gens qs bs i = true → ∀ j ∈ gens, actK (M j) (qs.getD i 0) = qs.getD i 0 ∧
      ∀ l < i, actK (M j) (qs.getD l 0) = qs.getD l 0 ∧
        (actK (M j) (bs.getD l 0) = bs.getD l 0 ∨
          actK (M j) (bs.getD l 0) = Nat.xor (bs.getD l 0) (qs.getD l 0))
  | [], _ => by simp
  | j :: gs, h => by
    have e : fixQK M (j :: gs) qs bs i = (Nat.beq (actK (M j) (nget qs i)) (nget qs i) &&
        (allN i (fun l => strictB (nget qs l) (fun q => strictB (nget bs l) (fun b =>
          strictB (actK (M j) b) (fun w => bAnd(Nat.beq (actK (M j) q) q,
            bIf(Nat.beq w b, true, Nat.beq w (Nat.xor b q))))))) && fixQK M gs qs bs i)) := by
      rw [← MatL.bAnd_eq, ← MatL.bAnd_eq]
      rfl
    rw [e] at h
    simp only [Bool.and_eq_true, MatL.allN_iff, MatL.strictB_eq, MatL.bAnd_eq, orRec,
      Bool.or_eq_true, Nat.beq_eq, nget_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact ⟨h1, fun l hl => ⟨(h2 l hl).1, (h2 l hl).2⟩⟩
    · exact fixQK_spec h3 j' hj'

private abbrev St := Std.HashSet Nat × Array (Nat × Nat × Nat)

private def innerQ (cols : Array Rows) (q i v : Nat) (s : St) (g : Nat) : St :=
  if (!s.1.contains (stepVP cols q g v)) = true then
    (s.1.insert (stepVP cols q g v), s.2.push (stepVP cols q g v, i, g))
  else (s.1, s.2)

private def outerQ (cols : Array Rows) (q : Nat) (gens : List Nat) (s : St) (i : Nat) : St :=
  if h : i < s.2.size then gens.foldl (innerQ cols q i s.2[i].1) (s.1, s.2) else (s.1, s.2)

private theorem ite_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem dite_yield {β : Type} (c : Prop) [Decidable c] (a : c → β) (b : ¬c → β) :
    (if h : c then (pure (ForInStep.yield (a h)) : Id (ForInStep β))
      else pure (ForInStep.yield (b h))) =
      pure (ForInStep.yield (if h : c then a h else b h)) := by
  split <;> rfl

private theorem bfsP_eq (cols : Array Rows) (q : Nat) (gens : List Nat) (root bound : Nat) :
    bfsP cols q gens root bound = ((List.range bound).foldl (outerQ cols q gens)
      ((Std.HashSet.emptyWithCapacity 200000).insert root, #[(root, 0, 0)])).2 := by
  simp only [bfsP, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', ite_yield,
    List.forIn_pure_yield_eq_foldl, pure_bind, dite_yield]
  have hsz : [:bound].size = bound := by simp [Std.Legacy.Range.size]
  rw [hsz, ← List.range_eq_range']
  rfl

private theorem fold_outer_ge (cols : Array Rows) (q : Nat) (gens : List Nat) :
    ∀ (L : List Nat) (s : St), (∀ i ∈ L, s.2.size ≤ i) → L.foldl (outerQ cols q gens) s = s
  | [], _, _ => rfl
  | i :: L, s, hL => by
    have hs : outerQ cols q gens s i = s := by
      have hi : ¬ i < s.2.size := Nat.not_lt.2 (hL i (List.mem_cons_self ..))
      simp only [outerQ, hi, ↓reduceDIte]
    rw [List.foldl_cons, hs]
    exact fold_outer_ge cols q gens L s fun x hx => hL x (List.mem_cons_of_mem _ hx)

private theorem lvlQ_nil (M T E : Nat → Nat) (q G h v p c : Nat) :
    lvlGensQ M T E q G h v [] p c = c := rfl

private theorem lvlQ_cons (M T E : Nat → Nat) (q G h v g p c : Nat) (gs : List Nat) :
    lvlGensQ M T E q G h v (g :: gs) p c =
      if c < failC then
        (if eK17 E (h * G + p) ≤ c ∧ ptK T (eK17 E (h * G + p)) = canonK q (actK (M g) v) then
          (if eK17 E (h * G + p) = c then
            (if VOrb.parK T (eK17 E (h * G + p)) = h ∧ genK T (eK17 E (h * G + p)) = g then
              lvlGensQ M T E q G h v gs (p + 1) (c + 1) else failC)
          else lvlGensQ M T E q G h v gs (p + 1) c)
        else failC)
      else failC := by
  change nIf(Nat.blt c failC,
      strictN (eK17 E (Nat.add (Nat.mul h G) p)) (fun e =>
      strictN (canonK q (actK (M g) v)) (fun w =>
        nIf(bAnd(Nat.ble e c, Nat.beq (ptK T e) w),
          nIf(Nat.beq e c,
            nIf(bAnd(Nat.beq (VOrb.parK T e) h, Nat.beq (genK T e) g),
              lvlGensQ M T E q G h v gs (Nat.succ p) (Nat.succ c), failC),
            lvlGensQ M T E q G h v gs (Nat.succ p) c),
          failC))), failC) = _
  simp only [MatL.strictN_eq, MatL.nIf_eq, MatL.bAnd_eq, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq,
    Bool.and_eq_true, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one]

private theorem lvlQ_cons_ok {M T E : Nat → Nat} {q G h v g p c r : Nat} {gs : List Nat}
    (H : lvlGensQ M T E q G h v (g :: gs) p c = r) (hr : r < failC) :
    c < failC ∧ ∃ e, e ≤ c ∧ ptK T e = canonK q (actK (M g) v) ∧
      ((e = c ∧ VOrb.parK T c = h ∧ genK T c = g ∧ lvlGensQ M T E q G h v gs (p + 1) (c + 1) = r) ∨
        (e < c ∧ lvlGensQ M T E q G h v gs (p + 1) c = r)) := by
  rw [lvlQ_cons] at H
  by_cases h1 : c < failC
  · rw [ite_eq_left h1] at H
    refine ⟨h1, eK17 E (h * G + p), ?_⟩
    by_cases h2 : eK17 E (h * G + p) ≤ c ∧ ptK T (eK17 E (h * G + p)) = canonK q (actK (M g) v)
    · rw [ite_eq_left h2] at H
      refine ⟨h2.1, h2.2, ?_⟩
      by_cases h3 : eK17 E (h * G + p) = c
      · rw [ite_eq_left h3] at H
        by_cases h4 : VOrb.parK T (eK17 E (h * G + p)) = h ∧ genK T (eK17 E (h * G + p)) = g
        · rw [ite_eq_left h4] at H
          rw [h3] at h4
          exact Or.inl ⟨h3, h4.1, h4.2, H⟩
        · rw [ite_eq_right h4] at H
          omega
      · rw [ite_eq_right h3] at H
        exact Or.inr ⟨by omega, H⟩
    · rw [ite_eq_right h2] at H
      omega
  · rw [ite_eq_right h1] at H
    omega

private theorem lvlQ_mono {M T E : Nat → Nat} {q G h v : Nat} :
    ∀ (gs : List Nat) (p c r : Nat), lvlGensQ M T E q G h v gs p c = r → r < failC → c ≤ r
  | [], p, c, r, H, _ => by
    rw [lvlQ_nil] at H
    omega
  | g :: gs, p, c, r, H, hr => by
    obtain ⟨_, e, _, _, h | h⟩ := lvlQ_cons_ok H hr
    · have := lvlQ_mono gs _ _ _ h.2.2.2 hr
      omega
    · have := lvlQ_mono gs _ _ _ h.2 hr
      omega

private noncomputable def gstepQ (M : Nat → Nat) (q : Nat) (gens : List Nat) (n : Nat)
    (T E : Nat → Nat) (G h c : Nat) : Nat :=
  nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
    strictN (ptK T h) (fun v => nIf(Nat.beq (canonK q v) v,
      lvlGensQ M T E q G h v gens (nat_lit 0) c, failC)), failC), c), failC)

private theorem levelSlQ_iff (M : Nat → Nat) (q : Nat) (gens : List Nat) (n : Nat)
    (T E : Nat → Nat) (lo len c₀ c₁ : Nat) : levelSlQ M q gens n T E lo len c₀ c₁ = true ↔
      (List.range len).foldl (fun c d => gstepQ M q gens n T E (lenN gens) (lo + d) c) c₀ = c₁ := by
  have e : levelSlQ M q gens n T E lo len c₀ c₁ = Nat.beq (foldUp len (fun d c =>
      strictN (Nat.add lo d) (fun h => gstepQ M q gens n T E (lenN gens) h c)) c₀) c₁ := by
    rw [levelSlQ, MatL.strictB_eq]
    rfl
  rw [e, Nat.beq_eq, foldUp_eq]
  simp only [MatL.strictN_eq, Nat.add_eq]

section Level

variable {M : Nat → Nat} {q : Nat} {gens : List Nat} {n : Nat} {T E : Nat → Nat} {G : Nat}

private theorem gstepQ_eq (h c : Nat) : gstepQ M q gens n T E G h c =
    if c < failC then (if h < n then (if h < c then
      (if canonK q (ptK T h) = ptK T h then lvlGensQ M T E q G h (ptK T h) gens 0 c else failC)
      else failC) else c) else failC := by
  simp only [gstepQ, MatL.nIf_eq, Nat.blt_eq, Nat.beq_eq, MatL.strictN_eq]

private theorem gstepQ_ok {h c : Nat} (hr : gstepQ M q gens n T E G h c < failC) : c < failC ∧
    ((h < n ∧ h < c ∧ canonK q (ptK T h) = ptK T h ∧
        lvlGensQ M T E q G h (ptK T h) gens 0 c = gstepQ M q gens n T E G h c) ∨
      (n ≤ h ∧ gstepQ M q gens n T E G h c = c)) := by
  have e := gstepQ_eq (M := M) (q := q) (gens := gens) (n := n) (T := T) (E := E) (G := G) h c
  by_cases h1 : c < failC
  · rw [ite_eq_left h1] at e
    refine ⟨h1, ?_⟩
    by_cases h2 : h < n
    · rw [ite_eq_left h2] at e
      by_cases h3 : h < c
      · rw [ite_eq_left h3] at e
        by_cases h4 : canonK q (ptK T h) = ptK T h
        · rw [ite_eq_left h4] at e
          exact Or.inl ⟨h2, h3, h4, e.symm⟩
        · rw [ite_eq_right h4] at e
          omega
      · rw [ite_eq_right h3] at e
        omega
    · rw [ite_eq_right h2] at e
      exact Or.inr ⟨by omega, e⟩
  · rw [ite_eq_right h1] at e
    omega

private theorem gstepQ_mono {h c : Nat} (hr : gstepQ M q gens n T E G h c < failC) :
    c ≤ gstepQ M q gens n T E G h c ∧ c < failC := by
  obtain ⟨h1, ⟨-, -, -, h2⟩ | ⟨-, h2⟩⟩ := gstepQ_ok hr
  · exact ⟨lvlQ_mono gens 0 c _ h2 hr, h1⟩
  · omega

private theorem fold_mono : ∀ (L : List Nat) (c : Nat),
    L.foldl (fun c h => gstepQ M q gens n T E G h c) c < failC →
      c ≤ L.foldl (fun c h => gstepQ M q gens n T E G h c) c ∧ c < failC
  | [], c, hr => by
    simp only [List.foldl_nil] at hr ⊢
    omega
  | h :: L, c, hr => by
    simp only [List.foldl_cons] at hr ⊢
    have h1 := fold_mono L _ hr
    have h2 := gstepQ_mono h1.2
    omega

private theorem fold_canon : ∀ (L : List Nat) (c : Nat),
    L.foldl (fun c h => gstepQ M q gens n T E G h c) c < failC →
      ∀ h ∈ L, h < n → canonK q (ptK T h) = ptK T h
  | [], _, _ => by simp
  | h :: L, c, hr => by
    simp only [List.foldl_cons] at hr
    intro x hx hxn
    rcases List.mem_cons.1 hx with rfl | hx
    · have h1 := (fold_mono L _ hr).2
      obtain ⟨-, ⟨-, -, hc, -⟩ | ⟨hn, -⟩⟩ := gstepQ_ok h1
      · exact hc
      · omega
    · exact fold_canon L _ hr x hx hxn

private theorem fold_tail : ∀ (L : List Nat), (∀ h ∈ L, n ≤ h) → ∀ c : Nat,
    L.foldl (fun c h => gstepQ M q gens n T E G h c) c < failC →
      L.foldl (fun c h => gstepQ M q gens n T E G h c) c = c
  | [], _, c, _ => rfl
  | h :: L, hL, c, hr => by
    simp only [List.foldl_cons] at hr ⊢
    have h1 := fold_tail L (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ hr
    rw [h1] at hr ⊢
    obtain ⟨-, ⟨hh, -⟩ | ⟨-, he⟩⟩ := gstepQ_ok hr
    · have := hL h (List.mem_cons_self ..)
      omega
    · exact he

private theorem fold_slices {C : Nat → Nat} {L NS : Nat}
    (hsl : ∀ s < NS, (List.range L).foldl (fun c d => gstepQ M q gens n T E G (s * L + d) c)
      (C s) = C (s + 1)) :
    ∀ s ≤ NS, (List.range (s * L)).foldl (fun c h => gstepQ M q gens n T E G h c) (C 0) = C s
  | 0, _ => by simp
  | s + 1, hs => by
    rw [Nat.succ_mul, List.range_add, List.foldl_append, fold_slices hsl s (by omega),
      List.foldl_map]
    exact hsl s (by omega)

private noncomputable def entT (T : Nat → Nat) (k : Nat) : Nat × Nat × Nat :=
  (ptK T k, if k = 0 then 0 else VOrb.parK T k, if k = 0 then 0 else genK T k)

private structure Rel (M : Nat → Nat) (q : Nat) (gens : List Nat) (T : Nat → Nat) (c : Nat)
    (s : St) : Prop where
  size : s.2.size = c
  ent : ∀ k < c, s.2[k]? = some (entT T k)
  tree : ∀ k < c, 0 < k → VOrb.parK T k < k ∧ genK T k ∈ gens ∧
    ptK T k = canonK q (actK (M (genK T k)) (ptK T (VOrb.parK T k)))
  seen : ∀ w, s.1.contains w = true ↔ ∃ k < c, ptK T k = w

private theorem Rel.get {c : Nat} {s : St} (hs : Rel M q gens T c s) {k : Nat} (hk : k < c) :
    s.2[k]'(hs.size ▸ hk) = entT T k := by
  have := hs.ent k hk
  rw [Array.getElem?_eq_getElem (hs.size ▸ hk)] at this
  exact Option.some.inj this

private theorem rel_init {root : Nat} (hroot : ptK T 0 = root) :
    Rel M q gens T 1 ((Std.HashSet.emptyWithCapacity 200000).insert root, #[(root, 0, 0)]) where
  size := rfl
  ent k hk := by
    have : k = 0 := by omega
    subst this
    simp [entT, hroot]
  tree k hk h0 := by omega
  seen w := by
    rw [Std.HashSet.contains_insert, Std.HashSet.contains_emptyWithCapacity, Bool.or_false,
      beq_iff_eq]
    constructor
    · intro h
      exact ⟨0, by omega, hroot.trans h⟩
    · rintro ⟨k, hk, hk'⟩
      have : k = 0 := by omega
      subst this
      exact hroot.symm.trans hk'

private theorem rel_push {c h g : Nat} {s : St} (hs : Rel M q gens T c s) (hhc : h < c)
    (hpar : VOrb.parK T c = h) (hgen : genK T c = g) (hg : g ∈ gens)
    (hpt : ptK T c = canonK q (actK (M g) (ptK T h))) :
    Rel M q gens T (c + 1) (s.1.insert (ptK T c), s.2.push (ptK T c, h, g)) where
  size := by simp [hs.size]
  ent k hk := by
    simp only [Array.getElem?_push, hs.size]
    by_cases hkc : k = c
    · subst hkc
      have hk0 : k ≠ 0 := by omega
      simp [entT, hpar, hgen, hk0]
    · rw [ite_eq_right hkc]
      exact hs.ent k (by omega)
  tree k hk h0 := by
    by_cases hkc : k = c
    · subst hkc
      rw [hpar, hgen]
      exact ⟨hhc, hg, hpt⟩
    · exact hs.tree k (by omega) h0
  seen w := by
    rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hs.seen]
    constructor
    · rintro (h | ⟨k, hk, hk'⟩)
      · exact ⟨c, by omega, h⟩
      · exact ⟨k, by omega, hk'⟩
    · rintro ⟨k, hk, hk'⟩
      by_cases hkc : k = c
      · subst hkc
        exact Or.inl hk'
      · exact Or.inr ⟨k, by omega, hk'⟩

private theorem inner_sim {cols : Array Rows}
    (hcols : ∀ g ∈ gens, ∀ v, stepVP cols q g v = canonK q (actK (M g) v))
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) {h v : Nat} (hv : v = ptK T h)
    (gs : List Nat) (hgs : ∀ g ∈ gs, g ∈ gens) :
    ∀ (p c : Nat) (s : St), Rel M q gens T c s → h < c → lvlGensQ M T E q G h v gs p c < failC →
      lvlGensQ M T E q G h v gs p c ≤ n →
        Rel M q gens T (lvlGensQ M T E q G h v gs p c) (gs.foldl (innerQ cols q h v) s) := by
  induction gs with
  | nil =>
    intro p c s hs _ _ _
    exact hs
  | cons g gs ih =>
    intro p c s hs hhc hr hrn
    have hg : g ∈ gens := hgs g (List.mem_cons_self ..)
    have ih' := ih fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    obtain ⟨-, e, he, hpe, ⟨hec, hpar, hgen, H'⟩ | ⟨hec, H'⟩⟩ := lvlQ_cons_ok rfl hr
    · subst hec
      rw [← H'] at hr hrn ⊢
      have hcr := lvlQ_mono gs _ _ _ rfl hr
      have hw : stepVP cols q g v = ptK T e := by rw [hcols g hg, hpe]
      have hnot : s.1.contains (ptK T e) = false := by
        rcases hcs : s.1.contains (ptK T e) with _ | _
        · rfl
        · obtain ⟨k, hk, hk'⟩ := (hs.seen _).1 hcs
          have := hdist k (by omega) e (by omega) hk'
          omega
      rw [List.foldl_cons]
      have hstep : innerQ cols q h v s g = (s.1.insert (ptK T e), s.2.push (ptK T e, h, g)) := by
        simp only [innerQ, hw, hnot, Bool.not_false, ↓reduceIte]
      rw [hstep]
      refine ih' (p + 1) (e + 1) _ ?_ (by omega) hr hrn
      exact rel_push hs hhc hpar hgen hg (by rw [hpe, hv])
    · rw [← H'] at hr hrn ⊢
      have hw : stepVP cols q g v = ptK T e := by rw [hcols g hg, hpe]
      have hyes : s.1.contains (ptK T e) = true := (hs.seen _).2 ⟨e, hec, rfl⟩
      rw [List.foldl_cons]
      have hstep : innerQ cols q h v s g = (s.1, s.2) := by
        simp only [innerQ, hw, hyes, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [hstep]
      exact ih' (p + 1) c _ hs hhc hr hrn

private theorem outer_sim {cols : Array Rows} {root : Nat}
    (hcols : ∀ g ∈ gens, ∀ v, stepVP cols q g v = canonK q (actK (M g) v))
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) (hroot : ptK T 0 = root)
    (hn : n < failC)
    (hcnt : (List.range n).foldl (fun c h => gstepQ M q gens n T E G h c) 1 = n) :
    ∀ i ≤ n, Rel M q gens T ((List.range i).foldl (fun c h => gstepQ M q gens n T E G h c) 1)
      ((List.range i).foldl (outerQ cols q gens)
        ((Std.HashSet.emptyWithCapacity 200000).insert root, #[(root, 0, 0)]))
  | 0, _ => rel_init hroot
  | i + 1, hi => by
    have ih := outer_sim hcols hdist hroot hn hcnt i (by omega)
    have hsplit : (List.range n).foldl (fun c h => gstepQ M q gens n T E G h c) 1 =
        ((List.range (n - (i + 1))).map (i + 1 + ·)).foldl
          (fun c h => gstepQ M q gens n T E G h c)
          ((List.range (i + 1)).foldl (fun c h => gstepQ M q gens n T E G h c) 1) := by
      rw [← List.foldl_append, ← List.range_add, Nat.add_sub_cancel' hi]
    have hlt : ((List.range (n - (i + 1))).map (i + 1 + ·)).foldl
        (fun c h => gstepQ M q gens n T E G h c)
          ((List.range (i + 1)).foldl (fun c h => gstepQ M q gens n T E G h c) 1) < failC := by
      rw [← hsplit, hcnt]
      exact hn
    have hle := fold_mono _ _ hlt
    rw [← hsplit, hcnt] at hle
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hle ⊢
    generalize (List.range i).foldl (fun c h => gstepQ M q gens n T E G h c) 1 = C at ih hle ⊢
    generalize (List.range i).foldl (outerQ cols q gens)
      ((Std.HashSet.emptyWithCapacity 200000).insert root, #[(root, 0, 0)]) = s at ih ⊢
    obtain ⟨-, ⟨-, hic, -, hlv⟩ | ⟨hni, -⟩⟩ := gstepQ_ok hle.2
    · have hsz : i < s.2.size := by
        rw [ih.size]
        exact hic
      have hv : s.2[i].1 = ptK T i := by
        rw [ih.get hic]
        rfl
      simp only [outerQ, hsz, ↓reduceDIte, hv]
      rw [← hlv] at hle ⊢
      exact inner_sim hcols hdist rfl gens (fun g hg => hg) 0 C s ih hic hle.2 hle.1
    · omega

end Level

private theorem perm_pos {S T : Nat → Nat} {n NS L : Nat} (hNL : n ≤ NS * L)
    (hps : ∀ s < NS, permSl S T n (s * L) L = true) : ∀ k < n,
      msK S k < n ∧ invK S k < n ∧ invK S (msK S k) = k ∧ msK S (invK S k) = k ∧
        (k + 1 < n → ptK T (msK S k) < ptK T (msK S (k + 1))) := by
  intro k hk
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.mul_zero] at hNL
      omega
    · exact h
  have hs : k / L < NS := (Nat.div_lt_iff_lt_mul hL).2 (by omega)
  have H0 := hps (k / L) hs
  rw [permSl, MatL.allN_iff] at H0
  have H := H0 (k % L) (Nat.mod_lt k hL)
  have e : Nat.add (k / L * L) (k % L) = k := Nat.div_add_mod' k L
  simp only [MatL.strictB_eq, e] at H
  simp only [MatL.bAnd_eq] at H
  simp only [bIf_eq] at H
  simp only [Nat.blt_eq, Nat.beq_eq, hk, ↓reduceIte, Bool.and_eq_true, Nat.succ_eq_add_one] at H
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, h2, h3, h4, fun hk1 => ?_⟩
  simpa [hk1] using h5

private theorem perm_dist {S T : Nat → Nat} {n : Nat}
    (hP : ∀ k < n, msK S k < n ∧ invK S k < n ∧ invK S (msK S k) = k ∧ msK S (invK S k) = k ∧
      (k + 1 < n → ptK T (msK S k) < ptK T (msK S (k + 1)))) :
    ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b := by
  have hinc : ∀ j, j < n → ∀ i, i < j → ptK T (msK S i) < ptK T (msK S j) := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hij
      have h5 := (hP j (by omega)).2.2.2.2 hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with h | h
      · exact Nat.lt_trans (ih (by omega) i h) h5
      · subst h
        exact h5
  intro a ha b hb hab
  obtain ⟨-, hra, -, hma, -⟩ := hP a ha
  obtain ⟨-, hrb, -, hmb, -⟩ := hP b hb
  rcases Nat.lt_trichotomy (invK S a) (invK S b) with h | h | h
  · have := hinc _ hrb _ h
    rw [hma, hmb] at this
    omega
  · rw [← hma, ← hmb, h]
  · have := hinc _ hra _ h
    rw [hma, hmb] at this
    omega

private theorem strictSorted_of : ∀ l : List Nat, l.Pairwise (· < ·) → strictSorted l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
    rw [strictSorted]
    rw [List.pairwise_cons] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.1 b (List.mem_cons_self ..), strictSorted_of (b :: r) h.2⟩

private theorem mergeSort_lt {l : List Nat} (hl : l.Nodup) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· < ·) := by
  have h1 := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have h2 : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.2 hl
  exact (h1.and h2).imp fun ⟨h3, h4⟩ => Nat.lt_of_le_of_ne (by simpa using h3) h4

private theorem qtree_of_rel {M : Nat → Nat} {q : Nat} {gens : List Nat} {n : Nat}
    {T : Nat → Nat} {cols : Array Rows} {root : Nat} {s : St}
    (hcols : ∀ g ∈ gens, ∀ v, stepVP cols q g v = canonK q (actK (M g) v))
    (hdist : ∀ a < n, ∀ b < n, ptK T a = ptK T b → a = b) (hroot : ptK T 0 = root) (hn0 : 0 < n)
    (hcan : ∀ m < n, canonK q (ptK T m) = ptK T m)
    (hs : Rel M q gens T n s) : treeOKP cols q gens root n s.2 = true := by
  have hget : ∀ k < n, s.2.getD k (0, 0, 0) = entT T k := fun k hk => by
    rw [Array.getD_eq_getD_getElem?, hs.ent k hk]
    rfl
  have hmap : s.2.toList.map (·.1) = (List.range n).map (ptK T) := by
    apply List.ext_getElem
    · simp [hs.size]
    · intro k h1 h2
      have hk : k < n := by simpa using h2
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
      rw [hs.get hk]
      rfl
  have hnd : ((List.range n).map (ptK T)).Nodup :=
    List.pairwise_map.2 (List.nodup_range.imp_of_mem fun ha hb hab heq =>
      hab (hdist _ (List.mem_range.1 ha) _ (List.mem_range.1 hb) heq))
  simp only [treeOKP, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hs.size, ?_⟩, ?_⟩, ?_⟩
  · rw [hget 0 hn0]
    exact hroot
  · intro m hm
    have hc : canon q (ptK T m) = ptK T m := by rw [← canonK_eq, hcan m hm]
    rw [hget m hm]
    by_cases hm0 : m = 0
    · subst hm0
      simp [entT, ptK_lt', hc]
    · obtain ⟨hp, hg, hpt⟩ := hs.tree m hm (by omega)
      simp only [entT, hm0, ↓reduceIte]
      rw [hget _ (by omega)]
      simp [entT, ptK_lt', hc, hp, hg, hcols _ hg, ← hpt, -Array.getD_eq_getD_getElem?]
  · rw [hmap]
    exact strictSorted_of _ (mergeSort_lt hnd)

private theorem level_okQ {M : Nat → Nat} {q : Nat} {gens : List Nat} {cols : Array Rows}
    {root n : Nat} {T E S C : Nat → Nat} {NS L : Nat}
    (hcols : ∀ g ∈ gens, ∀ v, vecMulN 24 (cols.getD g #[]) v = actK (M g) v)
    (hn0 : 0 < n) (hn : n ≤ 100000) (hroot : ptK T 0 = root) (hC0 : C 0 = 1) (hCN : C NS = n)
    (hNL : n ≤ NS * L)
    (hsl : ∀ s < NS, levelSlQ M q gens n T E (s * L) L (C s) (C (s + 1)) = true)
    (hps : ∀ s < NS, permSl S T n (s * L) L = true) :
    treeOKP cols q gens root n (bfsP cols q gens root 100000) = true := by
  have hcolsQ : ∀ g ∈ gens, ∀ v, stepVP cols q g v = canonK q (actK (M g) v) := by
    intro g hg v
    unfold stepVP
    rw [hcols g hg, canonK_eq]
  have hdist := perm_dist (perm_pos hNL hps)
  have hfail : n < failC := by
    change n < 1048576
    omega
  have hsl' := fun s hs =>
    (levelSlQ_iff M q gens n T E (s * L) L (C s) (C (s + 1))).1 (hsl s hs)
  have hall := fold_slices hsl' NS (Nat.le_refl _)
  have eNL : NS * L = n + (NS * L - n) := by omega
  rw [hC0, hCN, eNL, List.range_add, List.foldl_append] at hall
  have hcnt : (List.range n).foldl (fun c h => gstepQ M q gens n T E (lenN gens) h c) 1 = n := by
    have ht := fold_tail (M := M) (q := q) (gens := gens) (n := n) (T := T) (E := E)
      (G := lenN gens) ((List.range (NS * L - n)).map (n + ·)) (by simp) _
      (by rw [hall]; exact hfail)
    rw [← ht]
    exact hall
  have hcan : ∀ m < n, canonK q (ptK T m) = ptK T m := fun m hm =>
    fold_canon (M := M) (q := q) (gens := gens) (n := n) (T := T) (E := E) (G := lenN gens)
      (List.range n) 1 (by rw [hcnt]; exact hfail) m (List.mem_range.2 hm) hm
  have hrel := outer_sim (cols := cols) hcolsQ hdist hroot hfail hcnt n (Nat.le_refl _)
  rw [hcnt] at hrel
  have e100 : (100000 : Nat) = n + (100000 - n) := by omega
  rw [bfsP_eq, e100, List.range_add, List.foldl_append,
    fold_outer_ge cols q gens _ _ (fun i hi => by
      rw [hrel.size]
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hi
      omega)]
  exact qtree_of_rel hcolsQ hdist hroot hn0 hcan hrel

end GenL

open GenL in
theorem cK_sound {A B AI BI R : Nat} (hA : CFSG.KS.SporSch.M24.invOKK A AI = true)
    (hB : CFSG.KS.SporSch.M24.invOKK B BI = true)
    (h : Nat.beq (CFSG.KS.SporSch.M24.mulK (CFSG.KS.SporSch.M24.powK
      (CFSG.KS.SporSch.M24.mulK (CFSG.KS.SporSch.M24.mulK (CFSG.KS.SporSch.M24.mulK A B) AI) BI) 2)
      B) R = true) :
    mul (pow (mul (mul (mul (unpack 24 24 A) (unpack 24 24 B)) (inv (unpack 24 24 A)))
      (inv (unpack 24 24 B))) 2) (unpack 24 24 B) = unpack 24 24 R := by
  rw [(CFSG.KS.SporSch.M24.MatL.invOK_of hA).2, (CFSG.KS.SporSch.M24.MatL.invOK_of hB).2,
    ← Nat.eq_of_beq_eq_true h, CFSG.KS.SporSch.M24.MatL.unpack_mulK, unpack_powK,
    CFSG.KS.SporSch.M24.MatL.unpack_mulK, CFSG.KS.SporSch.M24.MatL.unpack_mulK,
    CFSG.KS.SporSch.M24.MatL.unpack_mulK]

theorem gen_sound {M : Nat → Nat} {qs bs ns : List Nat} {gs : List (List Nat)}
    (hl : ∀ i < 7, ∃ (T E S C : Nat → Nat) (NS L : Nat),
      levelHd 93 (gs.getD i []) (bs.getD i 0) T = true ∧ C 0 = 1 ∧ C NS = ns.getD i 0 ∧
        ns.getD i 0 ≤ NS * L ∧ 0 < ns.getD i 0 ∧ ns.getD i 0 ≤ 100000 ∧
        (∀ s < NS, levelSlQ M (qs.getD i 0) (gs.getD i []) (ns.getD i 0) T E (s * L) L (C s)
          (C (s + 1)) = true) ∧
        (∀ s < NS, permSl S T (ns.getD i 0) (s * L) L = true) ∧
        fixQK M (gs.getD i []) qs bs i = true ∧ bs.getD i 0 < 2 ^ 24 ∧ qs.getD i 0 < 2 ^ 24) :
    genP (Array.ofFn (n := 93) fun j => transposeRows 24 (unpack 24 24 (M j.val))) qs bs gs ns =
      true := by
  have hcols : ∀ g < 93, ∀ v, vecMulN 24 ((Array.ofFn (n := 93) fun j =>
      transposeRows 24 (unpack 24 24 (M j.val))).getD g #[]) v = CFSG.KS.SporSch.M24.actK (M g) v := by
    intro g hg v
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp only [hg, ↓reduceDIte, Option.getD_some]
    exact CFSG.KS.SporSch.M24.ActL.vecMulN_unpack (M g) v
  unfold genP
  rw [List.all_eq_true]
  intro i hi
  obtain ⟨T, E, S, C, NS, L, hhd, hC0, hCN, hNL, hn0, hn, hsl, hps, hfix, hb, hq⟩ :=
    hl i (List.mem_range.1 hi)
  have hhd' : (∀ x ∈ gs.getD i [], x < 93) ∧ ptK T 0 = bs.getD i 0 := by
    have e : levelHd 93 (gs.getD i []) (bs.getD i 0) T =
        (CFSG.KS.Mathieu.allLtN 93 (gs.getD i []) && Nat.beq (ptK T 0) (bs.getD i 0)) :=
      CFSG.KS.SporSch.M24.MatL.bAnd_eq _ _
    rw [e, Bool.and_eq_true, GenL.allLtN_iff, Nat.beq_eq] at hhd
    exact hhd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hb, hq⟩, ?_⟩, ?_⟩
  · unfold fixOKP
    rw [List.all_eq_true]
    intro j hj
    have hj93 := hhd'.1 j hj
    obtain ⟨h1, h2⟩ := GenL.fixQK_spec hfix j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, hcols j hj93, beq_iff_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true]
    exact ⟨⟨hj93, h1⟩, fun l hl => ⟨(h2 l hl).1, (h2 l hl).2⟩⟩
  · exact GenL.level_okQ (fun g hg => hcols g (hhd'.1 g hg)) hn0 hn hhd'.2 hC0 hCN hNL hsl hps

end CFSG.KS.SporSch.VOrb

end

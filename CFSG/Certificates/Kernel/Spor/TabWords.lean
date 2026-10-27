module

public import Certificates.Data.Kernel.Spor.ONK
public import Certificates.Data.Kernel.Spor.WordsTxt
public import Certificates.Data.CFSGNative.Perm.Chain
import Aesop.BuiltinRules
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

public section

namespace CFSG.KS.TW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.Words CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] noncomputable def GZ (TT UU : Nat → Nat → Nat) (z : Int) (y : Nat) : Nat :=
  if 0 < z then TT (z.toNat - 1) y else UU ((-z).toNat - 1) y

@[expose] def decFrom (W k : Nat) : Nat → List Int
  | 0 => []
  | L + 1 => letterOfCode ((W >>> (4 * (k + L))) % 16) :: decFrom W k L

theorem decFrom_succ (W : Nat) : ∀ (L k : Nat),
    decFrom W k (L + 1) = decFrom W (k + 1) L ++ [letterOfCode ((W >>> (4 * k)) % 16)]
  | 0, k => by simp [decFrom]
  | L + 1, k => by
    rw [decFrom, decFrom_succ W L k, decFrom]
    simp only [List.cons_append]
    rw [show k + 1 + L = k + (L + 1) by omega]

theorem decW_eq (W : Nat) : ∀ L, decW W L = decFrom W 0 L
  | 0 => rfl
  | L + 1 => by rw [decW, decW_eq W L, decFrom, Nat.zero_add]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem step_eq (TT UU : Nat → Nat → Nat) (c v : Nat) :
    nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), TT (Nat.shiftRight c (nat_lit 1)) v,
      UU (Nat.shiftRight c (nat_lit 1)) v) = GZ TT UU (letterOfCode c) v := by
  have h1 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  have h2 : Nat.shiftRight c 1 = c / 2 := by simp [Nat.shiftRight_eq_div_pow]
  unfold GZ letterOfCode
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h]
    have hp : (0 : Int) < ((c / 2 + 1 : Nat) : Int) := by omega
    have e : (((c / 2 + 1 : Nat) : Int)).toNat - 1 = c / 2 := by omega
    simp only [ite_true, hp, e]
    rfl
  · rw [h]
    have hn : ¬ (0 : Int) < -((c / 2 + 1 : Nat) : Int) := by omega
    have e : (-(-((c / 2 + 1 : Nat) : Int))).toNat - 1 = c / 2 := by omega
    simp only [Nat.one_ne_zero, ite_false, hn, e]
    rfl

theorem trace_gen (TT UU : Nat → Nat → Nat) (W : Nat) : ∀ (L k v : Nat),
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
      (fun _ ih k v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
        strictN (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), TT (Nat.shiftRight c (nat_lit 1)) v,
          UU (Nat.shiftRight c (nat_lit 1)) v)) fun v' => ih (Nat.succ k) v') L k v =
    (decFrom W k L).foldr (fun z y => GZ TT UU z y) v
  | 0, k, v => rfl
  | L + 1, k, v => by
    simp only []
    rw [strictN_eq', strictN_eq', trace_gen TT UU W L (k + 1), decFrom_succ, List.foldr_append,
      List.foldr_cons, List.foldr_nil, step_eq]
    congr 3
    have h15 : (15 : Nat) = 2 ^ 4 - 1 := rfl
    rw [show Nat.land (Nat.shiftRight W (Nat.mul 4 k)) 15 = (W >>> (4 * k)) % 16 from by
      rw [h15]
      exact Nat.and_two_pow_sub_one_eq_mod _ 4]

theorem trace_eq (TT UU : Nat → Nat → Nat) (W L x : Nat) :
    trace TT UU W L x = (decW W L).foldr (fun z y => GZ TT UU z y) x := by
  rw [decW_eq]
  exact trace_gen TT UU W L 0 x

theorem foldr_inv {n : Nat} {G : Int → Nat → Nat} :
    ∀ (w : List Int), (∀ z ∈ w, ∀ y < n, G z y < n ∧ G (-z) (G z y) = y) →
      ∀ x < n, w.foldr G x < n ∧ (w.reverse.map fun z => -z).foldr G (w.foldr G x) = x
  | [], _, x, hx => ⟨hx, rfl⟩
  | a :: t, h, x, hx => by
    obtain ⟨ht, hinv⟩ := foldr_inv t (fun z hz => h z (List.mem_cons_of_mem a hz)) x hx
    obtain ⟨ha1, ha2⟩ := h a (List.mem_cons_self) _ ht
    refine ⟨by simpa using ha1, ?_⟩
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.foldr_append,
      List.foldr_cons, List.foldr_nil, List.foldr_cons]
    rw [ha2, hinv]

@[expose] def TR (n : Nat) (t : Table) (f : Nat → Nat) : Prop :=
  t.size = n ∧ ∀ i < n, ap t i = f i ∧ f i < n

theorem idT_TR {n : Nat} (hn : n < 2 ^ 32) : TR n (idT n) fun i => i := by
  refine ⟨by simp [idT], fun i hi => ⟨?_, hi⟩⟩
  unfold ap idT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  simp only [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem wordT_TR {n : Nat} (hn : n < 2 ^ 32) {gens : Int → Table} {G : Int → Nat → Nat} :
    ∀ (w : List Int), (∀ z ∈ w, TR n (gens z) (G z)) →
      TR n (wordT n gens w) fun x => w.foldr G x
  | [], _ => by
    unfold wordT
    exact idT_TR hn
  | l :: w, h => by
    obtain ⟨hs, hv⟩ := wordT_TR hn w (fun z hz => h z (List.mem_cons_of_mem l hz))
    obtain ⟨ls, lv⟩ := h l List.mem_cons_self
    have e : wordT n gens (l :: w) = (wordT n gens w).map fun t => (gens l)[t.toNat]! := by
      unfold wordT
      rfl
    rw [e]
    refine ⟨by simp [hs], fun i hi => ?_⟩
    obtain ⟨a1, a2⟩ := hv i hi
    obtain ⟨b1, b2⟩ := lv _ a2
    refine ⟨?_, by simpa using b2⟩
    unfold ap at a1 b1 ⊢
    rw [getElem!_pos _ i (by simp [hs]; omega), Array.getElem_map,
      ← getElem!_pos (wordT n gens w) i (by omega), a1, b1]
    rfl

theorem set_loopV {α : Type} [Inhabited α] {N : Nat} {v0 : α} {D : Nat → Nat} {v : Nat → α} :
    ∀ {m : Nat}, (∀ i < m, D i < N) → (∀ i < m, ∀ j < i, D j ≠ D i) →
      ((List.range' 0 m).foldl (fun p i => p.set! (D i) (v i)) (Array.replicate N v0)).size = N ∧
      ∀ i < m, ((List.range' 0 m).foldl (fun p i => p.set! (D i) (v i)) (Array.replicate N v0))[D i]! = v i
  | 0, _, _ => ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | m + 1, hD, hd => by
    obtain ⟨hs, hv⟩ := set_loopV (N := N) (v0 := v0) (D := D) (v := v) (m := m)
      (fun i hi => hD i (by omega)) (fun i hi j hj => hd i (by omega) j hj)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun p i => p.set! (D i) (v i)) (Array.replicate N v0) = q at hs hv
    have hm : D m < N := hD m (by omega)
    have hsz : (q.set! (D m) (v m)).size = N := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    refine ⟨hsz, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i m with h | h
    · have hne : D i ≠ D m := fun e => hd m (by omega) i h e
      have hi' : D i < N := hD i (by omega)
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp [hs]; omega),
        Array.getElem_setIfInBounds_ne (by rw [hs]; exact hi') (Ne.symm hne),
        ← getElem!_pos q _ (by rw [hs]; exact hi')]
      exact hv i h
    · have e : i = m := by omega
      subst e
      rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp [hs]; omega),
        Array.getElem_setIfInBounds_self]

theorem invT_TR {n : Nat} (hn : n < 2 ^ 32) {P : Table} {f g : Nat → Nat} (hP : TR n P f)
    (hg : ∀ i < n, g i < n ∧ f (g i) = i ∧ g (f i) = i) : TR n (invT n P) g := by
  obtain ⟨hs, hv⟩ := hP
  have hget : ∀ i < n, (P[i]!).toNat = f i := fun i hi => (hv i hi).1
  have hD : ∀ i < n, (P[i]!).toNat < n := fun i hi => by
    rw [hget i hi]
    exact (hv i hi).2
  have hd : ∀ i < n, ∀ j < i, (P[j]!).toNat ≠ (P[i]!).toNat := fun i hi j hj e => by
    rw [hget i hi, hget j (by omega)] at e
    have := congrArg g e
    rw [(hg j (by omega)).2.2, (hg i hi).2.2] at this
    omega
  have heq : invT n P = (List.range' 0 n).foldl
      (fun p i => p.set! (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
    unfold invT
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  have hl := set_loopV (D := fun i => (P[i]!).toNat) (v := fun i => UInt32.ofNat i)
    (v0 := (0 : UInt32)) hD hd
  refine ⟨by rw [heq]; exact hl.1, fun y hy => ⟨?_, (hg y hy).1⟩⟩
  obtain ⟨h1, h2, -⟩ := hg y hy
  unfold ap
  rw [heq, ← h2, ← hget (g y) h1, hl.2 (g y) h1, hget (g y) h1, h2]
  simp only [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem allIn_iff {n : Nat} {p : Nat → Bool} : allIn 0 n p = true ↔ ∀ i < n, p i = true := by
  unfold allIn
  rw [Nat.sub_zero, Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h ⟨i, hi⟩ _
    simpa using h i hi

theorem invOK_of {n : Nat} {P R : Table} {f g : Nat → Nat} (hP : TR n P f) (hR : TR n R g)
    (hgf : ∀ i < n, g (f i) = i) : invOK n P R = true := by
  unfold invOK
  rw [allIn_iff]
  intro i hi
  rw [(hP.2 i hi).1, (hR.2 _ (hP.2 i hi).2).1, hgf i hi, beq_self_eq_true]

theorem apT_loop (t : Table) (q : Array Nat) : ∀ j ≤ q.size,
    ((List.range' 0 j).foldl (fun r k => r.set! k (ap t r[k]!)) q).size = q.size ∧
      ∀ i < q.size, ((List.range' 0 j).foldl (fun r k => r.set! k (ap t r[k]!)) q)[i]! =
        if i < j then ap t q[i]! else q[i]!
  | 0, _ => ⟨rfl, fun i _ => by simp⟩
  | j + 1, hj => by
    obtain ⟨hs, hv⟩ := apT_loop t q j (by omega)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 j).foldl (fun r k => r.set! k (ap t r[k]!)) q = r at hs hv
    have hsz : (r.set! j (ap t r[j]!)).size = q.size := by
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs]
    refine ⟨hsz, fun i hi => ?_⟩
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simp [hs]; omega)]
    by_cases e : i = j
    · subst e
      rw [Array.getElem_setIfInBounds_self, hv i (by omega)]
      simp
    · rw [Array.getElem_setIfInBounds_ne (by omega) (Ne.symm e), ← getElem!_pos r i (by omega),
        hv i hi]
      by_cases h : i < j
      · simp [h, show i < j + 1 by omega]
      · simp [h, show ¬ i < j + 1 by omega]

theorem apT_map (t : Table) (q : Array Nat) : apT t q = q.map (ap t) := by
  have heq : apT t q = (List.range' 0 q.size).foldl (fun r k => r.set! k (ap t r[k]!)) q := by
    unfold apT
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  obtain ⟨hs, hv⟩ := apT_loop t q q.size (Nat.le_refl _)
  rw [heq]
  apply Array.ext (by rw [Array.size_map]; exact hs)
  intro i h1 h2
  have hi2 : i < q.size := by simpa using h2
  rw [Array.getElem_map, ← getElem!_pos _ i h1, hv i hi2]
  simp only [hi2, ite_true, getElem!_pos q i hi2]

theorem tupleEq_iff {a b : Array Nat} :
    tupleEq a b = true ↔ a.size = b.size ∧ ∀ t < b.size, a[t]! = b[t]! := by
  unfold tupleEq
  rw [Bool.and_eq_true, beq_iff_eq, allIn_iff]
  simp only [beq_iff_eq]

end CFSG.KS.TW

end

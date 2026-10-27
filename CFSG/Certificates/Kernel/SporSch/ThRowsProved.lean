
module

public import CFSG.Certificates.Kernel.SporSch.ThRowsDefs
public import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Data.CFSGNative.Th.Base
public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch.Pf

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open Finset
open scoped Matrix

theorem blt_land_two_pow (v j : Nat) :
    Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 j)) = v.testBit j := by
  have e : Nat.land v (Nat.shiftLeft 1 j) = v &&& 2 ^ j := by
    change v &&& (1 <<< j) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Bool.eq_iff_iff, Nat.blt_eq, e, Nat.and_two_pow]
  cases v.testBit j <;> simp

theorem rowOfNat_xor (a b : Nat) : rowOfNat (Nat.xor a b) = rowOfNat a + rowOfNat b := by
  funext k
  simp only [rowOfNat, Pi.add_apply]
  change (if (a ^^^ b).testBit k.val then (1 : ZMod 2) else 0) = _
  rw [Nat.testBit_xor]
  cases a.testBit k.val <;> cases b.testBit k.val <;> decide

@[expose] def vmStep (Y : Nat → Nat) (v : Nat) (j acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (Y j)) (v.testBit j)

theorem vmT_eq (Y : Nat → Nat) (v : Nat) : vmT Y v = (List.range 248).foldr (vmStep Y v) 0 := by
  rw [vmT, CFSG.KC.Pack.foldN_eq]
  congr 1
  funext j acc
  rw [blt_land_two_pow]
  rfl

theorem rowOfNat_foldr (Y : Nat → Nat) (v : Nat) : ∀ l : List Nat,
    rowOfNat (l.foldr (vmStep Y v) 0) = (l.map fun j => if v.testBit j then rowOfNat (Y j) else 0).sum
  | [] => by
    funext k
    simp [rowOfNat]
  | j :: l => by
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← rowOfNat_foldr Y v l, vmStep]
    cases v.testBit j
    · simp
    · change rowOfNat (Nat.xor _ (Y j)) = _
      rw [rowOfNat_xor, add_comm]
      simp

theorem foldr_lt (Y : Nat → Nat) (v : Nat) (hY : ∀ j < 248, Y j < 2 ^ 248) : ∀ l : List Nat,
    (∀ j ∈ l, j < 248) → l.foldr (vmStep Y v) 0 < 2 ^ 248
  | [], _ => by simp
  | j :: l, hl => by
    rw [List.foldr_cons, vmStep]
    have ih := foldr_lt Y v hY l fun i hi => hl i (List.mem_cons_of_mem _ hi)
    cases v.testBit j
    · exact ih
    · exact Nat.xor_lt_two_pow ih (hY j (hl j (List.mem_cons_self ..)))

theorem vmT_lt {Y : Nat → Nat} (hY : ∀ j < 248, Y j < 2 ^ 248) (v : Nat) : vmT Y v < 2 ^ 248 := by
  rw [vmT_eq]
  exact foldr_lt Y v hY _ fun j hj => List.mem_range.1 hj

theorem list_sum_range {M : Type} [AddCommMonoid M] (f : Nat → M) : ∀ n : Nat,
    ((List.range n).map f).sum = ∑ j ∈ range n, f j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, sum_range_succ]
    simp

theorem getD_rowsV (R : Nat → Nat) {j : Nat} (hj : j < 248) :
    (rowsV R)[j]?.getD V4.zero = v4OfNat (R j) := by
  rw [rowsV, Array.getElem?_ofFn]
  simp [hj]

theorem rowsV_size (R : Nat → Nat) : (rowsV R).size = 248 := by
  rw [rowsV, Array.size_ofFn]

theorem rowsV_wf {R : Nat → Nat} (hR : ∀ i < 248, R i < 2 ^ 248) : ∀ x ∈ rowsV R, x.wf = true := by
  intro x hx
  rw [rowsV, Array.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact v4OfNat_wf (hR i.val i.isLt)

theorem frApply_rowsV {Y : Nat → Nat} (v : Nat) :
    (frApply (frTable (rowsV Y)) (v4OfNat v)).toVec = (v4OfNat (vmT Y v)).toVec := by
  rw [frApply_frTable_toVec_eq_sum, toVec_v4OfNat, vmT_eq, rowOfNat_foldr, list_sum_range]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  rw [v4OfNat_testBit v (by omega), getD_rowsV Y hj', toVec_v4OfNat]

theorem getElem_rowsV (R : Nat → Nat) {j : Nat} (hj : j < (rowsV R).size) :
    (rowsV R)[j] = v4OfNat (R j) := by
  simp [rowsV]

@[expose] def pivotOf (m : Array V4) (c : Nat) : Nat :=
  (List.range' c (248 - c)).foldl
    (fun p i => if (p == 248 && (m[i]!).testBit c) = true then i else p) 248

@[expose] def elimRow (c : Nat) (mc rc : V4) (s : Array V4 × Array V4) (i : Nat) :
    Array V4 × Array V4 :=
  if (i != c && (s.1[i]!).testBit c) = true then
    (s.1.set! i ((s.1[i]!).xor mc), s.2.set! i ((s.2[i]!).xor rc))
  else s

@[expose] def stepCol (s : Array V4 × Array V4) (c : Nat) : Array V4 × Array V4 :=
  if pivotOf s.1 c < 248 then
    (List.range' 0 248).foldl (fun t i => elimRow c s.1[pivotOf s.1 c]! s.2[pivotOf s.1 c]! t i)
      ((s.1.set! (pivotOf s.1 c) s.1[c]!).set! c s.1[pivotOf s.1 c]!,
        (s.2.set! (pivotOf s.1 c) s.2[c]!).set! c s.2[pivotOf s.1 c]!)
  else s

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem invRows_eq_run (X : Array V4) :
    invRows X = Id.run (pure ((List.range' 0 248).foldl (fun s c => stepCol s c)
      (X, idRows ())).2) := by
  simp only [invRows, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, Prod.mk.eta, stepCol, elimRow, pivotOf]
  rfl

theorem run_pure_eq {α : Type} (a : α) : Id.run (pure a : Id α) = a := rfl

theorem eta_stepCol : (fun s c => stepCol s c) = stepCol := rfl

theorem invRows_eq_model (X : Array V4) :
    invRows X = ((List.range' 0 248).foldl stepCol (X, idRows ())).2 := by
  rw [invRows_eq_run, run_pure_eq, eta_stepCol]

theorem get!_getD (M : Array V4) (i : Nat) : M[i]! = M[i]?.getD V4.zero := by
  by_cases h : i < M.size
  · rw [getElem!_pos M i h, getElem?_pos M i h, Option.getD_some]
  · rw [getElem!_neg M i h, getElem?_neg M i h, Option.getD_none]
    rfl

theorem get_set {M : Array V4} (hM : M.size = 248) {i j : Nat} (hj : j < 248) (v : V4) :
    (M.set! i v)[j]! = if i = j then v else M[j]! := by
  have hj' : j < M.size := by omega
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (M.setIfInBounds i v) j (by simp [hj']),
    Array.getElem_setIfInBounds hj', getElem!_pos M j hj']

theorem size_set (M : Array V4) (i : Nat) (v : V4) : (M.set! i v).size = M.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem rowsMatrix_row (M : Array V4) (i : Fin 248) : rowsMatrix M i = (M[i.val]!).toVec := by
  funext j
  rw [rowsMatrix_apply, get!_getD]

theorem mulVec_apply' (A : Matrix (Fin 248) (Fin 248) (ZMod 2)) (v : Fin 248 → ZMod 2)
    (i : Fin 248) : (A *ᵥ v) i = ∑ j, A i j * v j := by
  simp only [Matrix.mulVec, dotProduct]

@[expose] def Good (X : Array V4) (s : Array V4 × Array V4) : Prop :=
  s.1.size = 248 ∧ s.2.size = 248 ∧ (∀ i < 248, (s.1[i]!).wf = true ∧ (s.2[i]!).wf = true) ∧
    rowsMatrix s.1 = rowsMatrix s.2 * rowsMatrix X ∧
    ∀ v : Fin 248 → ZMod 2, rowsMatrix s.2 *ᵥ v = 0 → v = 0

@[expose] def Col (m : Array V4) (c : Nat) : Prop :=
  ∀ c' < c, ∀ i < 248, (m[i]!).testBit c' = decide (i = c')

theorem good_perm {X : Array V4} {s : Array V4 × Array V4} (hG : Good X s)
    {t : Array V4 × Array V4} (σ : Nat → Nat) (hσ : ∀ i < 248, σ i < 248)
    (hσσ : ∀ i < 248, σ (σ i) = i) (ht1 : t.1.size = 248) (ht2 : t.2.size = 248)
    (hr1 : ∀ i < 248, t.1[i]! = s.1[σ i]!) (hr2 : ∀ i < 248, t.2[i]! = s.2[σ i]!) : Good X t := by
  obtain ⟨hs1, hs2, hwf, hL, hker⟩ := hG
  have hrow : ∀ (M N : Array V4), (∀ i < 248, N[i]! = M[σ i]!) →
      ∀ i : Fin 248, rowsMatrix N i = rowsMatrix M ⟨σ i.val, hσ i.val i.isLt⟩ := by
    intro M N h i
    rw [rowsMatrix_row, rowsMatrix_row, h i.val i.isLt]
  refine ⟨ht1, ht2, fun i hi => by rw [hr1 i hi, hr2 i hi]; exact hwf _ (hσ i hi), ?_,
    fun v hv => hker v ?_⟩
  · ext i k
    rw [Matrix.mul_apply, hrow s.1 t.1 hr1 i, hL, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hrow s.2 t.2 hr2 i]
  · funext i
    have := congrFun hv ⟨σ i.val, hσ i.val i.isLt⟩
    rw [mulVec_apply', hrow s.2 t.2 hr2] at this
    rw [mulVec_apply']
    have e : (⟨σ (σ i.val), hσ _ (hσ i.val i.isLt)⟩ : Fin 248) = i := Fin.ext (hσσ i.val i.isLt)
    rw [e] at this
    exact this

theorem good_xor {X : Array V4} {s : Array V4 × Array V4} (hG : Good X s) {r c : Nat}
    (hr : r < 248) (hc : c < 248) (hrc : r ≠ c) :
    Good X (s.1.set! r ((s.1[r]!).xor s.1[c]!), s.2.set! r ((s.2[r]!).xor s.2[c]!)) := by
  obtain ⟨hs1, hs2, hwf, hL, hker⟩ := hG
  have hrow : ∀ (M : Array V4), M.size = 248 → ∀ i : Fin 248,
      rowsMatrix (M.set! r ((M[r]!).xor M[c]!)) i =
        if r = i.val then rowsMatrix M ⟨r, hr⟩ + rowsMatrix M ⟨c, hc⟩ else rowsMatrix M i := by
    intro M hM i
    rw [rowsMatrix_row, get_set hM i.isLt]
    split
    · rw [V4.toVec_xor, rowsMatrix_row, rowsMatrix_row]
    · rw [rowsMatrix_row]
  refine ⟨by rw [size_set, hs1], by rw [size_set, hs2], fun t ht => ?_, ?_, fun v hv => hker v ?_⟩
  · dsimp only
    rw [get_set hs1 ht, get_set hs2 ht]
    by_cases e : r = t
    · rw [ite_eq_left e, ite_eq_left e]
      exact ⟨V4.xor_wf (hwf r hr).1 (hwf c hc).1, V4.xor_wf (hwf r hr).2 (hwf c hc).2⟩
    · rw [ite_eq_right e, ite_eq_right e]
      exact hwf t ht
  · ext i k
    dsimp only
    rw [Matrix.mul_apply, hrow s.1 hs1 i]
    simp only [hrow s.2 hs2 i]
    by_cases e : r = i.val
    · rw [ite_eq_left e, ite_eq_left e, hL]
      simp only [Pi.add_apply, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
    · rw [ite_eq_right e, ite_eq_right e, hL, Matrix.mul_apply]
  · have hv' : ∀ i : Fin 248, (rowsMatrix (s.2.set! r ((s.2[r]!).xor s.2[c]!)) *ᵥ v) i = 0 :=
      fun i => congrFun hv i
    have hc0 : (rowsMatrix s.2 *ᵥ v) ⟨c, hc⟩ = 0 := by
      have := hv' ⟨c, hc⟩
      rw [mulVec_apply', hrow s.2 hs2, ite_eq_right hrc] at this
      exact this
    funext i
    have := hv' i
    rw [mulVec_apply', hrow s.2 hs2] at this
    rw [mulVec_apply', Pi.zero_apply]
    by_cases e : r = i.val
    · rw [ite_eq_left e] at this
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib] at this
      rw [mulVec_apply'] at hc0
      rw [hc0, add_zero] at this
      have ei : (⟨r, hr⟩ : Fin 248) = i := Fin.ext e
      rw [ei] at this
      exact this
    · rw [ite_eq_right e] at this
      exact this

theorem good_swap {X : Array V4} {s : Array V4 × Array V4} (hG : Good X s) {p c : Nat}
    (hp : p < 248) (hc : c < 248) :
    Good X ((s.1.set! p s.1[c]!).set! c s.1[p]!, (s.2.set! p s.2[c]!).set! c s.2[p]!) := by
  have hs1 := hG.1
  have hs2 := hG.2.1
  have hget : ∀ (M : Array V4), M.size = 248 → ∀ t < 248, ((M.set! p M[c]!).set! c M[p]!)[t]! =
      M[if c = t then p else if p = t then c else t]! := fun M hM t ht => by
    have hM1 : (M.set! p M[c]!).size = 248 := by rw [size_set, hM]
    rw [get_set hM1 ht, get_set hM ht]
    split
    · rfl
    · split <;> rfl
  apply good_perm hG (fun t => if c = t then p else if p = t then c else t)
  · intro i hi
    split
    · exact hp
    · split
      · exact hc
      · exact hi
  · intro i hi
    by_cases h1 : c = i
    · subst h1
      by_cases h2 : c = p
      · subst h2
        simp
      · simp [h2]
    · by_cases h2 : p = i
      · subst h2
        simp [h1]
      · simp [h1, h2]
  · rw [size_set, size_set, hs1]
  · rw [size_set, size_set, hs2]
  · exact hget s.1 hs1
  · exact hget s.2 hs2

theorem pivot_spec (M : Array V4) (c : Nat) :
    (pivotOf M c < 248 → c ≤ pivotOf M c ∧ (M[pivotOf M c]!).testBit c = true) ∧
      (¬ pivotOf M c < 248 → ∀ r, c ≤ r → r < 248 → (M[r]!).testBit c = false) := by
  have key : ∀ (L : List Nat) (q : Nat),
      (q = 248 ∨ (c ≤ q ∧ q < 248 ∧ (M[q]!).testBit c = true)) → (∀ x ∈ L, c ≤ x ∧ x < 248) →
      ((L.foldl (fun p r => if (p == 248 && (M[r]!).testBit c) = true then r else p) q = 248 ∨
        (c ≤ L.foldl (fun p r => if (p == 248 && (M[r]!).testBit c) = true then r else p) q ∧
          L.foldl (fun p r => if (p == 248 && (M[r]!).testBit c) = true then r else p) q < 248 ∧
          (M[L.foldl (fun p r => if (p == 248 && (M[r]!).testBit c) = true then r else p)
            q]!).testBit c = true)) ∧
        (L.foldl (fun p r => if (p == 248 && (M[r]!).testBit c) = true then r else p) q = 248 →
          q = 248 ∧ ∀ x ∈ L, (M[x]!).testBit c = false)) := by
    intro L
    induction L with
    | nil => intro q hq _; exact ⟨hq, fun h => ⟨h, fun _ hx => absurd hx List.not_mem_nil⟩⟩
    | cons x L ih =>
      intro q hq hL
      rw [List.foldl_cons]
      have hx := hL x List.mem_cons_self
      have hL' : ∀ y ∈ L, c ≤ y ∧ y < 248 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
      by_cases hb : (q == 248 && (M[x]!).testBit c) = true
      · rw [ite_eq_left hb]
        have hb' := Bool.and_eq_true_iff.1 hb
        obtain ⟨h1, h2⟩ := ih x (Or.inr ⟨hx.1, hx.2, hb'.2⟩) hL'
        refine ⟨h1, fun h => ?_⟩
        have := (h2 h).1
        omega
      · rw [ite_eq_right hb]
        obtain ⟨h1, h2⟩ := ih q hq hL'
        refine ⟨h1, fun h => ⟨(h2 h).1, fun y hy => ?_⟩⟩
        rcases List.mem_cons.1 hy with rfl | hy'
        · have hq248 := (h2 h).1
          subst hq248
          simpa using hb
        · exact (h2 h).2 y hy'
  have hL : ∀ x ∈ List.range' c (248 - c), c ≤ x ∧ x < 248 := fun x hx => by
    rw [List.mem_range'_1] at hx
    omega
  obtain ⟨h1, h2⟩ := key (List.range' c (248 - c)) 248 (Or.inl rfl) hL
  refine ⟨fun hp => ?_, fun hp r hr1 hr2 => ?_⟩
  · rcases h1 with h | h
    · rw [pivotOf] at hp
      omega
    · exact ⟨h.1, h.2.2⟩
  · have h248 : pivotOf M c = 248 := by
      rcases h1 with h | h
      · exact h
      · exact absurd h.2.1 hp
    exact (h2 h248).2 r (by rw [List.mem_range'_1]; omega)

theorem elim_spec {X : Array V4} {c : Nat} {mc rc : V4} (hc : c < 248)
    (hmc : mc.testBit c = true) (hrl : ∀ c' < c, mc.testBit c' = false) :
    ∀ n ≤ 248, ∀ s : Array V4 × Array V4, Good X s → s.1[c]! = mc → s.2[c]! = rc → Col s.1 c →
      Good X ((List.range' 0 n).foldl (elimRow c mc rc) s) ∧
      ((List.range' 0 n).foldl (elimRow c mc rc) s).1[c]! = mc ∧
      ((List.range' 0 n).foldl (elimRow c mc rc) s).2[c]! = rc ∧
      Col ((List.range' 0 n).foldl (elimRow c mc rc) s).1 c ∧
      ∀ r < n, r ≠ c → (((List.range' 0 n).foldl (elimRow c mc rc) s).1[r]!).testBit c = false := by
  intro n
  induction n with
  | zero =>
    intro _ s hG h1 h2 hC
    exact ⟨hG, h1, h2, hC, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ n ih =>
    intro hn s hG h1 h2 hC
    obtain ⟨hG1, hc1, hd1, hC1, hz1⟩ := ih (by omega) s hG h1 h2 hC
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    generalize (List.range' 0 n).foldl (elimRow c mc rc) s = t at hG1 hc1 hd1 hC1 hz1
    have hs1 := hG1.1
    have hs2 := hG1.2.1
    have hn248 : n < 248 := by omega
    rw [elimRow]
    by_cases hb : (n != c && (t.1[n]!).testBit c) = true
    · rw [ite_eq_left hb]
      have hb' := Bool.and_eq_true_iff.1 hb
      have hnc : n ≠ c := by simpa using hb'.1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := good_xor hG1 hn248 hc hnc
        rwa [hc1, hd1] at this
      · dsimp only
        rw [get_set hs1 hc, ite_eq_right hnc, hc1]
      · dsimp only
        rw [get_set hs2 hc, ite_eq_right hnc, hd1]
      · intro c' hc' r hr
        dsimp only
        rw [get_set hs1 hr]
        by_cases e : n = r
        · subst e
          rw [ite_eq_left rfl, V4.testBit_xor, hC1 c' hc' n hr, hrl c' hc', Bool.xor_false]
        · rw [ite_eq_right e]
          exact hC1 c' hc' r hr
      · intro r hr hrc'
        dsimp only
        by_cases hrn : r = n
        · subst hrn
          rw [get_set hs1 hn248, ite_eq_left rfl, V4.testBit_xor, hb'.2, hmc]
          rfl
        · rw [get_set hs1 (by omega), ite_eq_right (Ne.symm hrn)]
          exact hz1 r (by omega) hrc'
    · rw [ite_eq_right hb]
      refine ⟨hG1, hc1, hd1, hC1, fun r hr hrc' => ?_⟩
      by_cases hrn : r = n
      · subst hrn
        simpa [hrc'] using hb
      · exact hz1 r (by omega) hrc'

theorem toVec_bit (a : V4) (j : Fin 248) : a.toVec j = if a.testBit j.val then 1 else 0 := rfl

theorem no_pivot_false {X : Array V4} (hXinj : ∀ v, rowsMatrix X *ᵥ v = 0 → v = 0)
    {s : Array V4 × Array V4} (hG : Good X s) {c : Nat} (hc : c < 248) (hC : Col s.1 c)
    (hn : ∀ r, c ≤ r → r < 248 → (s.1[r]!).testBit c = false) : False := by
  obtain ⟨_, _, _, hL, hker⟩ := hG
  set v : Fin 248 → ZMod 2 := fun k =>
    if k.val = c then 1 else if k.val < c then (s.1[k.val]!).toVec ⟨c, hc⟩ else 0 with hvdef
  have hzero : rowsMatrix s.1 *ᵥ v = 0 := by
    funext i
    rw [mulVec_apply', Pi.zero_apply]
    have hterm : ∀ k : Fin 248, rowsMatrix s.1 i k * v k =
        (if k = ⟨c, hc⟩ then rowsMatrix s.1 i ⟨c, hc⟩ else 0) +
          (if k = i ∧ i.val < c then rowsMatrix s.1 i ⟨c, hc⟩ else 0) := by
      intro k
      simp only [hvdef]
      by_cases hk : k.val = c
      · have hk' : k = ⟨c, hc⟩ := Fin.ext hk
        subst hk'
        have : ¬ ((⟨c, hc⟩ : Fin 248) = i ∧ i.val < c) := fun h => by
          rw [← h.1] at h
          exact absurd h.2 (Nat.lt_irrefl _)
        simp [this]
      · have hk' : k ≠ ⟨c, hc⟩ := fun e => hk (by rw [e])
        rw [ite_eq_right hk, ite_eq_right hk']
        by_cases hkc : k.val < c
        · rw [ite_eq_left hkc, rowsMatrix_row, toVec_bit, hC k.val hkc i.val i.isLt]
          by_cases hik : i = k
          · subst hik
            simp [hkc]
          · have : ¬ (k = i ∧ i.val < c) := fun h => hik h.1.symm
            have hik' : ¬ i.val = k.val := fun e => hik (Fin.ext e)
            simp [hik', this]
        · rw [ite_eq_right hkc]
          have : ¬ (k = i ∧ i.val < c) := fun h => hkc (by rw [h.1]; exact h.2)
          simp [this]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ _)]
    by_cases hic : i.val < c
    · have : ∀ k : Fin 248, (k = i ∧ i.val < c) ↔ k = i := fun k => ⟨fun h => h.1, fun h => ⟨h, hic⟩⟩
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      generalize rowsMatrix s.1 i ⟨c, hc⟩ = a
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;> decide
    · have : ∀ k : Fin 248, ¬ (k = i ∧ i.val < c) := fun k h => hic h.2
      simp only [this, ite_false, Finset.sum_const_zero, add_zero]
      rw [rowsMatrix_row, toVec_bit, hn i.val (by omega) i.isLt]
      rfl
  have h1 : rowsMatrix s.2 *ᵥ (rowsMatrix X *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hL, hzero]
  have h2 := hXinj v (hker _ h1)
  have := congrFun h2 ⟨c, hc⟩
  simp [hvdef] at this

theorem col_zero (m : Array V4) : Col m 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem step_spec {X : Array V4} (hXinj : ∀ v, rowsMatrix X *ᵥ v = 0 → v = 0)
    {s : Array V4 × Array V4} (hG : Good X s) {c : Nat} (hc : c < 248) (hC : Col s.1 c) :
    Good X (stepCol s c) ∧ Col (stepCol s c).1 (c + 1) := by
  obtain ⟨hp1, hp2⟩ := pivot_spec s.1 c
  rw [stepCol]
  by_cases hp : pivotOf s.1 c < 248
  · rw [ite_eq_left hp]
    obtain ⟨hcp, hbit⟩ := hp1 hp
    generalize pivotOf s.1 c = p at hp hcp hbit
    have hs1 := hG.1
    have hs2 := hG.2.1
    have hget : ∀ (M : Array V4), M.size = 248 → ∀ t < 248, ((M.set! p M[c]!).set! c M[p]!)[t]! =
        if c = t then M[p]! else if p = t then M[c]! else M[t]! := fun M hM t ht => by
      have hM1 : (M.set! p M[c]!).size = 248 := by rw [size_set, hM]
      rw [get_set hM1 ht, get_set hM ht]
    have hrl : ∀ c' < c, (s.1[p]!).testBit c' = false := fun c' hc' => by
      rw [hC c' hc' p hp]
      simp only [decide_eq_false_iff_not]
      omega
    have hC1 : Col ((s.1.set! p s.1[c]!).set! c s.1[p]!) c := by
      intro c' hc' r hr
      rw [hget s.1 hs1 r hr]
      by_cases e1 : c = r
      · rw [ite_eq_left e1, hrl c' hc']
        simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega
      · rw [ite_eq_right e1]
        by_cases e2 : p = r
        · rw [ite_eq_left e2, hC c' hc' c hc]
          simp only [decide_eq_decide]
          omega
        · rw [ite_eq_right e2]
          exact hC c' hc' r hr
    obtain ⟨hG2, hc2, _, hC2, hz2⟩ := elim_spec (rc := s.2[p]!) hc hbit hrl 248 le_rfl _
      (good_swap hG hp hc) (by dsimp only; rw [hget s.1 hs1 c hc, ite_eq_left rfl])
      (by dsimp only; rw [hget s.2 hs2 c hc, ite_eq_left rfl]) hC1
    refine ⟨hG2, fun c' hc' r hr => ?_⟩
    by_cases hcc : c' = c
    · subst hcc
      by_cases hrc : r = c'
      · subst hrc
        rw [hc2, hbit]
        simp
      · rw [hz2 r hr hrc]
        simp [hrc]
    · exact hC2 c' (by omega) r hr
  · exact (no_pivot_false hXinj hG hc hC fun r h1 h2 => hp2 hp r h1 h2).elim

theorem good_start {X : Array V4} (hs : X.size = 248) (hwf : ∀ i < 248, (X[i]!).wf = true) :
    Good X (X, idRows ()) := by
  have h1 : (idRows ()).size = 248 := idRows_size
  have h2 : ∀ x ∈ idRows (), x.wf = true := idRows_wf
  have h3 : rowsMatrix (idRows ()) = 1 := rowsMatrix_idRows
  generalize idRows () = I at h1 h2 h3
  refine ⟨hs, h1, fun i hi => ⟨hwf i hi, ?_⟩, ?_, fun v hv => ?_⟩
  · have hi' : i < I.size := by rw [h1]; exact hi
    rw [getElem!_pos _ i hi']
    exact h2 _ (Array.getElem_mem hi')
  · rw [h3, Matrix.one_mul]
  · rwa [h3, Matrix.one_mulVec] at hv

theorem fold_spec {X : Array V4} (hs : X.size = 248) (hwf : ∀ i < 248, (X[i]!).wf = true)
    (hXinj : ∀ v, rowsMatrix X *ᵥ v = 0 → v = 0) : ∀ n ≤ 248,
    Good X ((List.range' 0 n).foldl stepCol (X, idRows ())) ∧
      Col ((List.range' 0 n).foldl stepCol (X, idRows ())).1 n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨good_start hs hwf, col_zero _⟩
  | succ n ih =>
    intro hn
    obtain ⟨hG, hC⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    exact step_spec hXinj hG (by omega) hC

end CFSG.KS.SporSch.Pf

end

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open CFSG.KS.SporSch.Pf
open scoped Matrix

theorem mulRows_sound_proved {X Y Z : Nat → Nat} (_hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248) (h : ∀ i < 248, vmT Y (X i) = Z i) :
    mulRows (rowsV X) (rowsV Y) = rowsV Z := by
  apply Array.ext (by rw [mulRows_size, rowsV_size, rowsV_size])
  intro i h1 h2
  have hi : i < 248 := by rw [rowsV_size] at h2; exact h2
  have hXi : i < (rowsV X).size := by rw [rowsV_size]; exact hi
  rw [getElem_rowsV Z h2]
  change (Array.map (fun x => frApply (frTable (rowsV Y)) x) (rowsV X))[i]'(by
    rw [Array.size_map]; exact hXi) = _
  rw [Array.getElem_map, getElem_rowsV X hXi]
  apply V4.eq_of_toVec_eq (frApply_frTable_wf (rowsV_wf hY) _) (v4OfNat_wf (by
    rw [← h i hi]
    exact vmT_lt hY _))
  rw [frApply_rowsV, h i hi]

theorem mulId_sound_proved {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248) (h : ∀ i < 248, vmT Y (X i) = 2 ^ i) :
    eqRows (mulRows (rowsV X) (rowsV Y)) (idRows ()) = true := by
  rw [mulRows_sound_proved hX hY h, eqRows_iff]
  apply Array.ext (by rw [rowsV_size, idRows_size])
  intro i h1 h2
  have hi : i < 248 := by rw [rowsV_size] at h1; exact h1
  rw [getElem_rowsV _ h1]
  apply V4.eq_of_toVec_eq (v4OfNat_wf (Nat.pow_lt_pow_right (by norm_num) hi))
    (idRows_wf _ (Array.getElem_mem h2))
  funext j
  rw [toVec_v4OfNat, rowOfNat]
  have e := congrFun (congrFun rowsMatrix_idRows ⟨i, hi⟩) j
  rw [rowsMatrix_apply, Array.getElem?_eq_getElem h2, Option.getD_some, Matrix.one_apply] at e
  rw [e, Nat.testBit_two_pow]
  by_cases hij : i = j.val
  · subst hij
    simp
  · have : (⟨i, hi⟩ : Fin 248) ≠ j := fun e' => hij (by rw [← e'])
    simp [hij, this]

theorem invRows_sound_proved {X Y : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248)
    (hY : ∀ i < 248, Y i < 2 ^ 248) (h : ∀ i < 248, vmT Y (X i) = 2 ^ i) :
    invRows (rowsV X) = rowsV Y := by
  have hXY : rowsMatrix (rowsV X) * rowsMatrix (rowsV Y) = 1 := by
    rw [← rowsMatrix_mulRows, eqRows_iff.1 (mulId_sound_proved hX hY h), rowsMatrix_idRows]
  have hYX : rowsMatrix (rowsV Y) * rowsMatrix (rowsV X) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin 248))).1 hXY
  have hXinj : ∀ v, rowsMatrix (rowsV X) *ᵥ v = 0 → v = 0 := by
    intro v hv
    calc v = (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = rowsMatrix (rowsV Y) *ᵥ (rowsMatrix (rowsV X) *ᵥ v) := by
        rw [← hYX, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  have hsX := rowsV_size X
  have hwX := rowsV_wf hX
  have hsY := rowsV_size Y
  have hgY : ∀ j (hj : j < (rowsV Y).size), (rowsV Y)[j] = v4OfNat (Y j) :=
    fun j hj => getElem_rowsV Y hj
  rw [invRows_eq_model]
  generalize rowsV X = A at hsX hwX hXY hXinj ⊢
  generalize rowsV Y = B at hsY hgY hXY ⊢
  have hwfX : ∀ i < 248, (A[i]!).wf = true := by
    intro i hi
    have hi' : i < A.size := by rw [hsX]; exact hi
    rw [getElem!_pos A i hi']
    exact hwX _ (Array.getElem_mem hi')
  obtain ⟨⟨_, hs2, hwf, hL, _⟩, hC⟩ := fold_spec hsX hwfX hXinj 248 le_rfl
  generalize (List.range' 0 248).foldl stepCol (A, idRows ()) = s at hs2 hwf hL hC ⊢
  have hone : rowsMatrix s.1 = 1 := by
    ext i j
    rw [rowsMatrix_row, toVec_bit, hC j.val j.isLt i.val i.isLt, Matrix.one_apply]
    by_cases e : i = j
    · subst e
      simp
    · have e' : ¬ i.val = j.val := fun h' => e (Fin.ext h')
      simp [e, e']
  have hR : rowsMatrix s.2 = rowsMatrix B := by
    calc rowsMatrix s.2 = rowsMatrix s.2 * (rowsMatrix A * rowsMatrix B) := by
          rw [hXY, Matrix.mul_one]
      _ = rowsMatrix s.1 * rowsMatrix B := by rw [← Matrix.mul_assoc, hL]
      _ = rowsMatrix B := by rw [hone, Matrix.one_mul]
  apply Array.ext (by rw [hs2, hsY])
  intro i h1 h2
  have hi : i < 248 := by rw [hs2] at h1; exact h1
  rw [hgY i h2]
  have hw1 := (hwf i hi).2
  rw [getElem!_pos s.2 i h1] at hw1
  apply V4.eq_of_toVec_eq hw1 (v4OfNat_wf (hY i hi))
  have := congrFun hR ⟨i, hi⟩
  rw [rowsMatrix_row, rowsMatrix_row, getElem!_pos s.2 i h1, getElem!_pos B i h2, hgY i h2] at this
  exact this

end CFSG.KS.SporSch

end

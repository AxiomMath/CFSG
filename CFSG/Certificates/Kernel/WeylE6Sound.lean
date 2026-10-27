module

public import Certificates.Data.Kernel.WeylE6
public import CFSG.Monster.Existence.StdOdd.P5Inputs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.KC.WeylE6

open CFSG.Monster.Existence.StdOdd.P5

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem ifB_eq (c t e : Bool) : ifB c t e = if c = true then t else e := by cases c <;> rfl

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by cases y <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allR_iff (lo n : Nat) (f : Nat → Bool) :
    allR lo n f = true ↔ ∀ i, lo ≤ i → i < lo + n → f i = true := by
  unfold allR
  rw [allN_iff]
  constructor
  · intro h i h1 h2
    have := h (i - lo) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this
  · intro h i hi
    exact h _ (Nat.le_add_right lo i) (by rw [Nat.add_eq]; omega)

theorem all_of_allR {f : Nat → Bool} {lo n : Nat} (h1 : ∀ i < lo, f i = true)
    (h2 : allR lo n f = true) : ∀ i < lo + n, f i = true := by
  intro i hi
  by_cases h : i < lo
  · exact h1 i h
  · exact (allR_iff lo n f).1 h2 i (by omega) hi

theorem all_of_chunks {f : Nat → Bool} {c K : Nat} (h : ∀ k < K, allR (c * k) c f = true) :
    ∀ i < c * K, f i = true := by
  intro i hi
  have hc : 0 < c := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hk : i / c < K := (Nat.div_lt_iff_lt_mul hc).2 (by rw [Nat.mul_comm]; exact hi)
  refine (allR_iff _ _ _).1 (h (i / c) hk) i (Nat.mul_div_le i c) ?_
  have := Nat.lt_mul_div_succ i hc
  rw [Nat.left_distrib, Nat.mul_one] at this
  exact this

theorem f8_eq (X i : Nat) : f8 X i = X / 256 ^ i % 256 := by
  change X >>> (i * 8) &&& 2 ^ 8 - 1 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul']

theorem f8_lt (X i : Nat) : f8 X i < 256 := by
  rw [f8_eq]
  exact Nat.mod_lt _ (by decide)

theorem keyOf_lt (w : Nat) : keyOf w < 2 ^ 40 :=
  Nat.and_lt_two_pow _ (by decide)

theorem eq_of_f8 {v w : Nat} (hv : v < 2 ^ 40) (hw : w < 2 ^ 40) (h : ∀ r < 5, f8 v r = f8 w r) :
    v = w := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  simp only [f8_eq] at h0 h1 h2 h3 h4
  norm_num at h0 h1 h2 h3 h4 hv hw
  omega

theorem shl_eq (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem f8_pack {a0 a1 a2 a3 a4 : Nat} (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256)
    (h3 : a3 < 256) (h4 : a4 < 256) :
    let X := Nat.add a0 <| Nat.add (Nat.shiftLeft a1 8) <| Nat.add (Nat.shiftLeft a2 16) <|
      Nat.add (Nat.shiftLeft a3 24) (Nat.shiftLeft a4 32)
    f8 X 0 = a0 ∧ f8 X 1 = a1 ∧ f8 X 2 = a2 ∧ f8 X 3 = a3 ∧ f8 X 4 = a4 := by
  simp only [f8_eq, Nat.add_eq, shl_eq]
  norm_num
  omega

theorem f8_mulT (T t v : Nat) {r : Nat} (hr : r < 5) :
    f8 (mulT T t v) r = rowT T t (f8 v r) := by
  have h := f8_pack (f8_lt T (Nat.add (Nat.mul t 256) (f8 v 0)))
    (f8_lt T (Nat.add (Nat.mul t 256) (f8 v 1))) (f8_lt T (Nat.add (Nat.mul t 256) (f8 v 2)))
    (f8_lt T (Nat.add (Nat.mul t 256) (f8 v 3))) (f8_lt T (Nat.add (Nat.mul t 256) (f8 v 4)))
  interval_cases r
  exacts [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

theorem encV_lt (x : E5) : encV x < 243 := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3)
  have h4 := ZMod.val_lt (x 4)
  unfold encV
  omega

theorem decV_val (n : Nat) (k : Fin 5) : (decV n k).val = n / 3 ^ k.val % 3 := by
  fin_cases k <;> simp [decV, ZMod.val_natCast]

theorem decV_encV (x : E5) : decV (encV x) = x := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3)
  have h4 := ZMod.val_lt (x 4)
  funext k
  apply ZMod.val_injective
  rw [decV_val]
  unfold encV
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> norm_num <;>
    omega

theorem encV_decV {n : Nat} (hn : n < 243) : encV (decV n) = n := by
  unfold encV
  rw [decV_val, decV_val, decV_val, decV_val, decV_val]
  norm_num
  omega

@[expose] noncomputable def rowsOf (v : Nat) : M5 := Matrix.of fun r c => decV (f8 v r.val) c

abbrev TabOK (T : Nat) : Prop :=
  ∀ t : Fin 6, ∀ x : Fin 243, f8 T (256 * t.val + x.val) = encV (Matrix.vecMul (decV x) (refl t))

theorem rowT_eq {T : Nat} (hT : TabOK T) (t : Fin 6) {x : Nat} (hx : x < 243) :
    rowT T t.val x = encV (Matrix.vecMul (decV x) (refl t)) := by
  have := hT t ⟨x, hx⟩
  unfold rowT
  rw [Nat.add_eq, Nat.mul_eq, Nat.mul_comm]
  exact this

abbrev Valid (v : Nat) : Prop := ∀ r < 5, f8 v r < 243

theorem valid_of_validK {v : Nat} (h : validK v = true) : Valid v := by
  unfold validK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  intro r hr
  interval_cases r <;> omega

theorem valid_mulT {T : Nat} (hT : TabOK T) (t : Fin 6) {v : Nat} (hv : Valid v) :
    Valid (mulT T t.val v) := by
  intro r hr
  rw [f8_mulT T t.val v hr, rowT_eq hT t (hv r hr)]
  exact encV_lt _

theorem rowsOf_mulT {T : Nat} (hT : TabOK T) (t : Fin 6) {v : Nat} (hv : Valid v) :
    rowsOf (mulT T t.val v) = rowsOf v * refl t := by
  ext r c
  simp only [rowsOf, Matrix.of_apply, Matrix.mul_apply]
  rw [f8_mulT T t.val v (by omega), rowT_eq hT t (hv r r.isLt), decV_encV]
  rfl

theorem rowsOf_inj {v w : Nat} (hv : Valid v) (hw : Valid w) (hv' : v < 2 ^ 40) (hw' : w < 2 ^ 40)
    (h : rowsOf v = rowsOf w) : v = w := by
  refine eq_of_f8 hv' hw' fun r hr => ?_
  have hrow : decV (f8 v r) = decV (f8 w r) := funext fun c => by
    have := congrFun (congrFun h ⟨r, hr⟩) c
    simpa [rowsOf] using this
  rw [← encV_decV (hv r hr), ← encV_decV (hw r hr), hrow]

theorem rowsOf_idKey : rowsOf idKey = 1 := by
  decide +kernel

theorem wPt_spec {T P E N i : Nat} (h : wPt T P E N i = true) :
    Valid (keyOf (f48 P i)) ∧
    (∀ t < 6, r16 (f112 E i) t < N ∧
      keyOf (f48 P (r16 (f112 E i) t)) = mulT T t (keyOf (f48 P i))) ∧
    (i + 1 < N → keyOf (f48 P i) < keyOf (f48 P (i + 1))) ∧
    (levOf (f48 P i) = 0 → keyOf (f48 P i) = idKey) ∧
    (levOf (f48 P i) ≠ 0 → r16 (f112 E i) 6 < 6 ∧
      levOf (f48 P (r16 (f112 E i) (r16 (f112 E i) 6))) < levOf (f48 P i)) := by
  unfold wPt at h
  simp only [letB_eq, andB_eq, ifB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨valid_of_validK h0, fun t ht => ?_, fun hi => ?_, fun hz => ?_, fun hz => ?_⟩
  · have := (allN_iff _ _).1 h1 t ht
    simpa only [letB_eq, andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using this
  · simpa [Nat.succ_eq_add_one, hi] using h2
  · simpa [hz] using h3
  · simpa [hz] using h3

theorem card_closure_of_wOK {T P E N s : Nat} (hT : TabOK T) (h : wOK T P E N s = true)
    (gens : Fin 6 → Matrix.GeneralLinearGroup (Fin 5) (ZMod 3))
    (hgens : ∀ i, (gens i : M5) = refl i) :
    Nat.card (Subgroup.closure (Set.range gens)) = N := by
  unfold wOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hs, hsid, hall⟩ := h
  have hpt := fun i hi => wPt_spec ((allN_iff _ _).1 hall i hi)
  set key : Nat → Nat := fun i => keyOf (f48 P i) with hkey
  set lev : Nat → Nat := fun i => levOf (f48 P i) with hlev
  set nx : Nat → Nat → Nat := fun i t => r16 (f112 E i) t with hnx
  set mats : Nat → M5 := fun i => rowsOf (key i) with hmats
  have hrefl : ∀ i : Fin 6, refl i * refl i = 1 := fun i => by
    fin_cases i <;> decide +kernel
  have hinv : ∀ i : Fin 6, (gens i)⁻¹ = gens i := fun i =>
    inv_eq_of_mul_eq_one_right (Units.ext (by rw [Units.val_mul, hgens i, Units.val_one, hrefl i]))
  have hnext : ∀ i < N, ∀ t : Fin 6, nx i t < N ∧ mats (nx i t) = mats i * refl t := by
    intro i hi t
    obtain ⟨hk, hv⟩ := (hpt i hi).2.1 t t.isLt
    refine ⟨hk, ?_⟩
    simp only [hmats, hkey, hnx] at hv ⊢
    rw [hv, rowsOf_mulT hT t (hpt i hi).1]
  have hW : ∀ n, ∀ i < N, lev i = n →
      ∃ g ∈ Subgroup.closure (Set.range gens), (g : M5) = mats i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hi hn
      by_cases hz : lev i = 0
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [Units.val_one]
        simp only [hmats, hkey]
        rw [(hpt i hi).2.2.2.1 hz, rowsOf_idKey]
      · obtain ⟨hg, hl⟩ := (hpt i hi).2.2.2.2 hz
        set g : Fin 6 := ⟨r16 (f112 E i) 6, hg⟩
        obtain ⟨hk, hm⟩ := hnext i hi g
        obtain ⟨x, hx, hxv⟩ := ih (lev (nx i g)) (by rw [← hn]; exact hl) (nx i g) hk rfl
        refine ⟨x * gens g, Subgroup.mul_mem _ hx (Subgroup.subset_closure ⟨g, rfl⟩), ?_⟩
        rw [Units.val_mul, hxv, hm, hgens, Matrix.mul_assoc, hrefl, Matrix.mul_one]
  have hW' : ∀ g ∈ Subgroup.closure (Set.range gens), ∃ i < N, (g : M5) = mats i := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one =>
      refine ⟨s, hs, ?_⟩
      rw [Units.val_one]
      simp only [hmats, hkey]
      rw [hsid, rowsOf_idKey]
    | mul_right x hx y hy ih =>
      obtain ⟨j, hj, hxj⟩ := ih
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hk, hm⟩ := hnext j hj i
      exact ⟨_, hk, by rw [Units.val_mul, hxj, hgens, hm]⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨j, hj, hxj⟩ := ih
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨hk, hm⟩ := hnext j hj i
      exact ⟨_, hk, by rw [hinv, Units.val_mul, hxj, hgens, hm]⟩
  have hmono : ∀ i j, i < j → j < N → key i < key j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := (hpt j (by omega)).2.2.1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact (ih h (by omega)).trans hs
      · exact hs
  have hinj : ∀ i < N, ∀ j < N, mats i = mats j → i = j := by
    intro i hi j hj hij
    have := rowsOf_inj (hpt i hi).1 (hpt j hj).1 (keyOf_lt _) (keyOf_lt _) hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd this (Nat.ne_of_lt (hmono i j h hj))
    · exact h
    · exact absurd this (Nat.ne_of_gt (hmono j i h hi))
  choose! g hgW hgv using fun i hi => hW (lev i) i hi rfl
  have hfinj : Function.Injective
      (fun i : Fin N => (⟨g i.val, hgW i.val i.2⟩ : Subgroup.closure (Set.range gens))) := by
    intro i j hij
    have h1 : g i.val = g j.val := congrArg Subtype.val hij
    apply Fin.ext
    apply hinj i.val i.2 j.val j.2
    rw [← hgv i.val i.2, ← hgv j.val j.2, h1]
  have hfsurj : Function.Surjective
      (fun i : Fin N => (⟨g i.val, hgW i.val i.2⟩ : Subgroup.closure (Set.range gens))) := by
    rintro ⟨x, hx⟩
    obtain ⟨j, hj, hxj⟩ := hW' x hx
    refine ⟨⟨j, hj⟩, Subtype.ext (Units.ext ?_)⟩
    change ((g j : Matrix.GeneralLinearGroup (Fin 5) (ZMod 3)) : M5) = (x : M5)
    rw [hgv j hj, hxj]
  have := Nat.card_congr (Equiv.ofBijective _ ⟨hfinj, hfsurj⟩)
  simpa using this.symm

end CFSG.KC.WeylE6

end

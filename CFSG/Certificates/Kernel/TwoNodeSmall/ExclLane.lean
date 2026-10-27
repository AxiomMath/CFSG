module

public import CFSG.Certificates.Kernel.TwoNodeSmall.LaneSound
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.TwoNodeSmall.LaneSound

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK

@[expose] noncomputable def packR (p D : Nat) (r : Refl) : Nat × Nat := (pkP p D r.h, pkrP p D r.f)

@[expose] def dualWord (P : Pt) (w : Word) (f : Vec) : Vec :=
  w.foldr (fun i acc => match P.gens[i]? with
    | some r => P.applyRefl ⟨r.h, r.f⟩ acc
    | none => acc) f

theorem nthK_eq {α : Type} (d : α) (l : List α) (k : Nat) : nthK d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem pkP_nil (p D : Nat) : pkP p D [] = 0 := by
  rw [pkP_fw]
  exact fw_eq_zero D _ (fun j _ => by simp [lnp])

theorem pkrP_nil (p D : Nat) : pkrP p D [] = 0 := by
  rw [pkrP_rv]
  unfold rv
  have h : ∀ l : List Nat, enc (l.map (lnp p [])) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simp [enc_cons, ih, lnp]
  exact h _

theorem packR_nil (p D : Nat) : packR p D ⟨[], []⟩ = (0, 0) := by
  simp only [packR, pkP_nil, pkrP_nil]

theorem getD_map_packR (p D : Nat) (l : List Refl) (k : Nat) :
    (l.map (packR p D)).getD k (0, 0) = packR p D (l.getD k ⟨[], []⟩) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? with
  | none => exact (packR_nil p D).symm
  | some r => rfl

theorem getD_of_lt {α : Type} (l : List α) (d : α) {n : Nat} (hn : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rfl

theorem applyWord_nil (P : Pt) (v : Vec) : P.applyWord [] v = v := rfl

theorem applyWord_cons_some {P : Pt} {j : Nat} {r : Refl} (hj : P.gens[j]? = some r) (w : Word)
    (v : Vec) : P.applyWord (j :: w) v = P.applyRefl r (P.applyWord w v) := by
  simp only [Pt.applyWord, List.foldr_cons, hj]

theorem applyWord_cons_none {P : Pt} {j : Nat} (hj : P.gens[j]? = none) (w : Word) (v : Vec) :
    P.applyWord (j :: w) v = P.applyWord w v := by
  simp only [Pt.applyWord, List.foldr_cons, hj]

theorem dualWord_cons_some {P : Pt} {j : Nat} {r : Refl} (hj : P.gens[j]? = some r) (w : Word)
    (f : Vec) : dualWord P (j :: w) f = P.applyRefl ⟨r.h, r.f⟩ (dualWord P w f) := by
  simp only [dualWord, List.foldr_cons, hj]

theorem dualWord_cons_none {P : Pt} {j : Nat} (hj : P.gens[j]? = none) (w : Word) (f : Vec) :
    dualWord P (j :: w) f = dualWord P w f := by
  simp only [dualWord, List.foldr_cons, hj]

theorem chainK_pk {P : Pt} {p : Nat} (hp : P.p = p) (hp57 : p = 5 ∨ p = 7) (hD : P.D ≤ 10)
    (k : Nat) (w : List Nat) (hw : ∀ j ∈ w, j < P.gens.length) :
    chainK (fdOf p P.D) (P.gens.map (packR p P.D)) k w =
      packR p P.D ⟨dualWord P w (P.gens.getD k ⟨[], []⟩).f, P.applyWord w (P.hK k)⟩ := by
  induction w with
  | nil =>
    change nthK (0, 0) (P.gens.map (packR p P.D)) k = _
    rw [nthK_eq, getD_map_packR]
    rfl
  | cons j w ih =>
    change conjK (fdOf p P.D) (nthK (0, 0) (P.gens.map (packR p P.D)) j)
      (chainK (fdOf p P.D) (P.gens.map (packR p P.D)) k w) = _
    have hj : j < P.gens.length := hw j (List.mem_cons_self ..)
    have hj' : P.gens[j]? = some P.gens[j] := List.getElem?_eq_getElem hj
    rw [ih (fun i hi => hw i (List.mem_cons_of_mem _ hi)), nthK_eq, getD_map_packR,
      getD_of_lt _ _ hj]
    unfold packR
    rw [conjKP_pk hp hp57 hD, dualWord_cons_some hj', applyWord_cons_some hj'] <;> rfl

@[expose] def zdot (P : Pt) (f v : Vec) : ZMod P.p :=
  ((List.range P.D).map fun i => (f.getD i 0 : ZMod P.p) * v.getD i 0).sum

@[expose] def veq (P : Pt) (v w : Vec) : Prop :=
  ∀ i < P.D, (v.getD i 0 : ZMod P.p) = w.getD i 0

theorem veq_refl (P : Pt) (v : Vec) : veq P v v := fun _ _ => rfl

theorem veq_trans {P : Pt} {u v w : Vec} (h1 : veq P u v) (h2 : veq P v w) : veq P u w :=
  fun i hi => (h1 i hi).trans (h2 i hi)

theorem veq_symm {P : Pt} {v w : Vec} (h : veq P v w) : veq P w v := fun i hi => (h i hi).symm

theorem vecEq_iff (P : Pt) (v w : Vec) : P.vecEq v w = true ↔ veq P v w := by
  simp only [Pt.vecEq, List.all_eq_true, List.mem_range, beq_iff_eq, Pt.ent, veq,
    ZMod.natCast_eq_natCast_iff']

theorem cast_dotv (P : Pt) (f v : Vec) : ((P.dotv f v : Nat) : ZMod P.p) = zdot P f v := by
  rw [Pt.dotv, ZMod.natCast_mod, foldl_add, Nat.zero_add, zdot]
  induction List.range P.D with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih]

theorem zdot_comm (P : Pt) (f v : Vec) : zdot P f v = zdot P v f := by
  unfold zdot
  congr 1
  apply List.map_congr_left
  intro i _
  ring

theorem cast_applyRefl {P : Pt} (hp0 : 0 < P.p) (f h v : Vec) {i : Nat} (hi : i < P.D) :
    (((P.applyRefl ⟨f, h⟩ v).getD i 0 : Nat) : ZMod P.p) = v.getD i 0 - zdot P f v * h.getD i 0 := by
  rw [applyRefl_getD P _ v hi, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hp0)), ZMod.natCast_self, ZMod.natCast_mod,
    Nat.cast_mul, cast_dotv]
  ring

theorem zdot_congr {P : Pt} (f : Vec) {v w : Vec} (h : veq P v w) : zdot P f v = zdot P f w := by
  unfold zdot
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem applyRefl_congr {P : Pt} (hp0 : 0 < P.p) (r : Refl) {v w : Vec} (h : veq P v w) :
    veq P (P.applyRefl r v) (P.applyRefl r w) := by
  obtain ⟨f, g⟩ := r
  intro i hi
  rw [cast_applyRefl hp0 f g v hi, cast_applyRefl hp0 f g w hi, h i hi, zdot_congr f h]

theorem sum_map_sub_mul {R : Type} [CommRing R] (l : List Nat) (f v b : Nat → R) (c : R) :
    (l.map fun i => f i * (v i - c * b i)).sum =
      (l.map fun i => f i * v i).sum - c * (l.map fun i => f i * b i).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem zdot_applyRefl {P : Pt} (hp0 : 0 < P.p) (f a b v : Vec) :
    zdot P f (P.applyRefl ⟨a, b⟩ v) = zdot P f v - zdot P a v * zdot P f b := by
  have e : ((List.range P.D).map fun i =>
      (f.getD i 0 : ZMod P.p) * (((P.applyRefl ⟨a, b⟩ v).getD i 0 : Nat) : ZMod P.p)) =
      (List.range P.D).map fun i =>
        (f.getD i 0 : ZMod P.p) * ((v.getD i 0 : ZMod P.p) - zdot P a v * b.getD i 0) :=
    List.map_congr_left (fun i hi => by rw [cast_applyRefl hp0 a b v (List.mem_range.mp hi)])
  rw [zdot, e, sum_map_sub_mul]
  rfl

theorem zdot_applyRefl_left {P : Pt} (hp0 : 0 < P.p) (f a b v : Vec) :
    zdot P (P.applyRefl ⟨b, a⟩ f) v = zdot P f v - zdot P b f * zdot P a v := by
  rw [zdot_comm, zdot_applyRefl hp0, zdot_comm P v f, zdot_comm P v a]

theorem applyWord_append (P : Pt) (u w : Word) (v : Vec) :
    P.applyWord (u ++ w) v = P.applyWord u (P.applyWord w v) := by
  simp only [Pt.applyWord, List.foldr_append]

theorem applyWord_congr {P : Pt} (hp0 : 0 < P.p) (u : Word) {v w : Vec} (h : veq P v w) :
    veq P (P.applyWord u v) (P.applyWord u w) := by
  induction u with
  | nil => exact h
  | cons j u ih =>
    cases hj : P.gens[j]? with
    | none =>
      rw [applyWord_cons_none hj, applyWord_cons_none hj]
      exact ih
    | some r =>
      rw [applyWord_cons_some hj, applyWord_cons_some hj]
      exact applyRefl_congr hp0 r ih

theorem two_of_dotv {P : Pt} {a b : Vec} (h : P.dotv a b = 2 % P.p) : zdot P a b = 2 := by
  rw [← cast_dotv, h, ZMod.natCast_mod]
  exact Nat.cast_ofNat

theorem applyRefl_invol {P : Pt} (hp0 : 0 < P.p) (f h : Vec) (hr : P.dotv f h = 2 % P.p)
    (v : Vec) : veq P (P.applyRefl ⟨f, h⟩ (P.applyRefl ⟨f, h⟩ v)) v := by
  have h2 := two_of_dotv hr
  intro i hi
  rw [cast_applyRefl hp0 _ _ _ hi, cast_applyRefl hp0 _ _ _ hi, zdot_applyRefl hp0]
  linear_combination (zdot P f v * h.getD i 0) * h2

theorem zdot_dual (P : Pt) (hp0 : 0 < P.p) (a b f v : Vec) :
    zdot P (P.applyRefl ⟨b, a⟩ f) v = zdot P f (P.applyRefl ⟨a, b⟩ v) := by
  rw [zdot_applyRefl_left hp0, zdot_applyRefl hp0, zdot_comm P b f]
  ring

theorem zdot_dualWord (P : Pt) (hp0 : 0 < P.p) (w : Word) (f v : Vec) :
    zdot P (dualWord P w f) v = zdot P f (P.applyWord w.reverse v) := by
  induction w generalizing v with
  | nil => rfl
  | cons j w ih =>
    rw [List.reverse_cons, applyWord_append]
    cases hj : P.gens[j]? with
    | none =>
      rw [dualWord_cons_none hj, applyWord_cons_none hj, applyWord_nil]
      exact ih v
    | some r =>
      obtain ⟨a, b⟩ := r
      rw [dualWord_cons_some hj, applyWord_cons_some hj, applyWord_nil]
      rw [zdot_dual P hp0 a b]
      exact ih _

theorem dotv_dualWord (P : Pt) (hp0 : 0 < P.p) (w : Word) (f v : Vec) :
    P.dotv (dualWord P w f) v = P.dotv f (P.applyWord w.reverse v) := by
  have h := zdot_dualWord P hp0 w f v
  rw [← cast_dotv, ← cast_dotv, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (dotv_ltP rfl hp0 _ _), Nat.mod_eq_of_lt (dotv_ltP rfl hp0 _ _)] at h
  exact h

theorem applyRefl_conj {P : Pt} (hp0 : 0 < P.p) (a b f h : Vec) (hg : P.dotv a b = 2 % P.p)
    (v : Vec) :
    veq P (P.applyRefl ⟨P.applyRefl ⟨b, a⟩ f, P.applyRefl ⟨a, b⟩ h⟩ v)
      (P.applyRefl ⟨a, b⟩ (P.applyRefl ⟨f, h⟩ (P.applyRefl ⟨a, b⟩ v))) := by
  have h2 := two_of_dotv hg
  intro i hi
  simp only [cast_applyRefl hp0 _ _ _ hi, zdot_applyRefl_left hp0, zdot_applyRefl hp0]
  rw [zdot_comm P b f]
  linear_combination (-(zdot P a v * b.getD i 0)) * h2

theorem applyWord_rev_cancel {P : Pt} (hp0 : 0 < P.p)
    (hwf : ∀ r ∈ P.gens, P.dotv r.f r.h = 2 % P.p) (w : Word) (v : Vec) :
    veq P (P.applyWord w (P.applyWord w.reverse v)) v := by
  induction w generalizing v with
  | nil => exact veq_refl P v
  | cons j w ih =>
    rw [List.reverse_cons, applyWord_append]
    cases hj : P.gens[j]? with
    | none =>
      rw [applyWord_cons_none hj, applyWord_cons_none hj, applyWord_nil]
      exact ih v
    | some r =>
      have hr := hwf r (List.mem_of_getElem? hj)
      obtain ⟨a, b⟩ := r
      rw [applyWord_cons_some hj, applyWord_cons_some hj, applyWord_nil]
      exact veq_trans (applyRefl_congr hp0 _ (ih _)) (applyRefl_invol hp0 a b hr v)

theorem applyRefl_chain {P : Pt} (hp0 : 0 < P.p) (hwf : ∀ r ∈ P.gens, P.dotv r.f r.h = 2 % P.p)
    {k : Nat} (hk : k < P.gens.length) (w : Word) (v : Vec) :
    veq P (P.applyRefl ⟨dualWord P w (P.gens.getD k ⟨[], []⟩).f, P.applyWord w (P.hK k)⟩ v)
      (P.applyWord (w ++ [k] ++ w.reverse) v) := by
  induction w generalizing v with
  | nil =>
    have hk' : P.gens[k]? = some P.gens[k] := List.getElem?_eq_getElem hk
    have hg : P.gens.getD k ⟨[], []⟩ = P.gens[k] := getD_of_lt _ _ hk
    have e : ([] : Word) ++ [k] ++ ([] : Word).reverse = [k] := rfl
    rw [e, applyWord_cons_some hk', applyWord_nil]
    simp only [Pt.hK, hg]
    exact veq_refl P _
  | cons j w ih =>
    have e : j :: w ++ [k] ++ (j :: w).reverse = [j] ++ (w ++ [k] ++ w.reverse) ++ [j] := by simp
    rw [e, applyWord_append, applyWord_append]
    cases hj : P.gens[j]? with
    | none =>
      simp only [dualWord_cons_none hj, applyWord_cons_none hj, applyWord_nil]
      exact ih v
    | some r =>
      have hr := hwf r (List.mem_of_getElem? hj)
      obtain ⟨a, b⟩ := r
      simp only [dualWord_cons_some hj, applyWord_cons_some hj, applyWord_nil]
      exact veq_trans (applyRefl_conj hp0 a b _ _ hr v) (applyRefl_congr hp0 _ (ih _))

@[expose] def frameRefl (lift : Bool) (p N : Nat) : List Refl :=
  (List.range (N - 1)).map fun k =>
    ⟨extOf lift (cartanRowP p N k) (if k = 0 then 1 else 0), unitP (dimOf lift N) k⟩

theorem frameK_eq (lift : Bool) (p N : Nat) :
    frameK lift p N = (frameRefl lift p N).map (packR p (dimOf lift N)) := by
  rw [frameRefl, List.map_map]
  rfl

theorem length_frameRefl (lift : Bool) (p N : Nat) : (frameRefl lift p N).length = N - 1 := by
  simp [frameRefl]

theorem getD_append_single {α : Type} (l : List α) (x d : α) (n : Nat) (hl : l.length = n) :
    (l ++ [x]).getD n d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl, Nat.sub_self]
  rfl

@[expose] def vvOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (fr : Vec) : Vec :=
  extOf lift ((List.range (N - 1)).map fun k =>
    if inJ N s k then (if k - s = o.1 then o.2.2 else 0)
    else if (outsOf N s).head? = some k then fr.getD 0 0 else fr.getD 1 0) 0

@[expose] def ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) : Pt :=
  { p := p, D := dimOf lift N, nFrame := N - 1,
    gens := frameRefl lift p N ++ [⟨vvOf lift p N s o fr, extOf lift c 0⟩],
    x := extOf lift ((List.range (N - 1)).map (· + 1)) 0, bound := posBound p N }

theorem lastRefl_ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    (ptOf lift p N s o c fr).lastRefl = ⟨vvOf lift p N s o fr, extOf lift c 0⟩ :=
  getD_append_single _ _ _ _ (length_frameRefl lift p N)

theorem gens_ptOf (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    (ptOf lift p N s o c fr).gens = frameRefl lift p N ++ [(ptOf lift p N s o c fr).lastRefl] := by
  rw [lastRefl_ptOf]
  rfl

theorem xK_eq (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    xK lift p N = pkP p (ptOf lift p N s o c fr).D (ptOf lift p N s o c fr).x := rfl

theorem frameK_append (lift : Bool) (p N s : Nat) (o : Nat × Nat × Nat) (c fr : Vec) :
    frameK lift p N ++ [packR p (dimOf lift N) (ptOf lift p N s o c fr).lastRefl] =
      (ptOf lift p N s o c fr).gens.map (packR p (ptOf lift p N s o c fr).D) := by
  rw [gens_ptOf, frameK_eq, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem mem_allVecsP_two {p : Nat} {fr : Vec} (h : fr ∈ allVecsP p 2) :
    ∃ a b, fr = [a, b] ∧ a < p ∧ b < p := by
  simp only [allVecsP, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap,
    List.mem_map, List.mem_range] at h
  obtain ⟨v, ⟨b, hb, rfl⟩, a, ha, rfl⟩ := h
  exact ⟨a, b, rfl, ha, hb⟩

theorem rv_congr (D : Nat) {x y : Nat → Nat} (h : ∀ i < D, x i = y i) : rv D x = rv D y := by
  unfold rv
  exact enc_map_congr (fun i hi => h i (List.mem_range.mp (List.mem_reverse.mp hi)))

theorem rv_add (D : Nat) (x y : Nat → Nat) : rv D (fun i => x i + y i) = rv D x + rv D y := by
  unfold rv
  have h := enc_map_add ((List.range D).reverse) x y 1
  simp only [Nat.one_mul] at h
  exact h

theorem rv_eq_zero (D : Nat) (x : Nat → Nat) (hx : ∀ j < D, x j = 0) : rv D x = 0 := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [rv_succ_last, ih (fun j hj => hx j (by omega)), hx D (by omega)]

theorem rv_unit (D o a : Nat) (ho : o < D) :
    rv D (fun i => if i = o then a else 0) = a * 65536 ^ (D - 1 - o) := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [rv_succ_last]
    rcases Nat.lt_or_ge o D with h | h
    · rw [ih h, if_neg (by omega)]
      have e : D + 1 - 1 - o = (D - 1 - o) + 1 := by omega
      rw [e, pow_succ]
      ring
    · have hoD : o = D := by omega
      subst hoD
      rw [rv_eq_zero o _ (fun j hj => if_neg (by omega)), if_pos rfl]
      simp

theorem rv_two (D o0 o1 a b : Nat) (h0 : o0 < D) (h1 : o1 < D) (x y : Nat → Nat)
    (h : ∀ i < D, y i = x i + (if i = o0 then a else 0) + (if i = o1 then b else 0)) :
    rv D y = rv D x + a * laneR D o0 + b * laneR D o1 := by
  rw [rv_congr D h, rv_add, rv_add, rv_unit D o0 a h0, rv_unit D o1 b h1, laneR, laneR, pow_mul,
    pow_mul]
  rfl

theorem outsOf_eq {p N s : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) (hs : s < 3) :
    ∃ o0 o1, outsOf N s = [o0, o1] ∧ o0 ≠ o1 := by
  rcases hpN with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> interval_cases s
  · exact ⟨2, 3, by decide, by decide⟩
  · exact ⟨0, 3, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide⟩
  · exact ⟨4, 5, by decide, by decide⟩
  · exact ⟨0, 5, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide⟩

theorem mem_outsOf (N s i : Nat) : i ∈ outsOf N s ↔ i < N - 1 ∧ inJ N s i = false := by
  simp [outsOf, List.mem_filter]

theorem getD_extOf {N : Nat} (lift : Bool) (g : Nat → Nat) (i : Nat) (hi : i < dimOf lift N) :
    (extOf lift ((List.range (N - 1)).map g) 0).getD i 0 = if i < N - 1 then g i else 0 := by
  have hL : ((List.range (N - 1)).map g).length = N - 1 := by simp
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have e : ((List.range (N - 1)).map g)[i]? = some (g i) := by
      rw [List.getElem?_map, List.getElem?_range h]
      rfl
    cases lift with
    | false => simp only [extOf, Bool.false_eq_true, if_false, e, Option.getD_some]
    | true => simp only [extOf, if_true, List.getElem?_append_left (hL ▸ h), e, Option.getD_some]
  · rename_i h
    cases lift with
    | false =>
      simp only [dimOf, Bool.false_eq_true, if_false] at hi
      omega
    | true =>
      simp only [dimOf, if_true] at hi
      simp only [extOf, if_true]
      rw [List.getElem?_append_right (by omega), hL]
      have e : i - (N - 1) = 0 := by omega
      rw [e]
      rfl

theorem vbK_add {lift : Bool} {p N s oi : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    (hs : s < 3) (a b : Nat) (ha : a < p) (hb : b < p) :
    vbK lift p N s oi + a * laneR (dimOf lift N) ((outsOf N s).getD 0 0) +
        b * laneR (dimOf lift N) ((outsOf N s).getD 1 0) =
      pkrP p (dimOf lift N) (vvOf lift p N s (optOf p N oi) [a, b]) := by
  simp only [vvOf, List.getD_cons_zero, List.getD_cons_succ]
  obtain ⟨o0, o1, ho, hne⟩ := outsOf_eq hpN hs
  have hm0 := (mem_outsOf N s o0).mp (by rw [ho]; simp)
  have hm1 := (mem_outsOf N s o1).mp (by rw [ho]; simp)
  have hND : N - 1 ≤ dimOf lift N := by cases lift <;> simp [dimOf]
  simp only [vbK, ho, pkrP_rv, List.getD_cons_zero, List.getD_cons_succ, List.head?_cons]
  symm
  refine rv_two _ o0 o1 a b (by omega) (by omega) _ _ (fun i hi => ?_)
  simp only [lnp]
  rw [getD_extOf lift _ i hi, getD_extOf lift _ i hi]
  split
  · rename_i hiN
    cases hJ : inJ N s i with
    | true =>
      have h0 : i ≠ o0 := by
        rintro rfl
        simp [hJ] at hm0
      have h1 : i ≠ o1 := by
        rintro rfl
        simp [hJ] at hm1
      simp [h0, h1]
    | false =>
      have hio : i ∈ outsOf N s := (mem_outsOf N s i).mpr ⟨hiN, hJ⟩
      rw [ho] at hio
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hio
      rcases hio with rfl | rfl
      · simp [hne, Nat.mod_eq_of_lt ha]
      · simp [hne, Ne.symm hne, Nat.mod_eq_of_lt hb]
  · rename_i hiN
    have h0 : i ≠ o0 := by omega
    have h1 : i ≠ o1 := by omega
    simp [h0, h1]

theorem ptsK_eq {lift : Bool} {p N s oi : Nat} (hpN : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7))
    (hs : s < 3) (cs : List Vec) :
    ptsK lift p N s oi cs = cs.flatMap fun c => (allVecsP p 2).map fun fr =>
      packR p (dimOf lift N) (ptOf lift p N s (optOf p N oi) c fr).lastRefl := by
  unfold ptsK
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih]
    congr 1
    apply List.map_congr_left
    intro fr hfr
    obtain ⟨a, b, rfl, ha, hb⟩ := mem_allVecsP_two hfr
    rw [lastRefl_ptOf]
    refine Prod.ext rfl ?_
    exact vbK_add hpN hs a b ha hb

end CFSG.TwoNodeSmall.LaneSound

end

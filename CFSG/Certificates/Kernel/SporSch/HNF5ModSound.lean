module

public import Certificates.Data.Kernel.SporSch.HNF5Mod
public import Certificates.Data.Kernel.SporSch.HNF5Dig
public import CFSG.Certificates.Kernel.SporSch.HNF5Sound
public import CFSG.Sporadic.HNSchreier.ModuleCheckInputs
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

set_option exponentiation.threshold 2200

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def vec5 (x : Nat) : Array Nat := Array.ofFn (n := 133) fun j => lane5 x j.val

theorem vec5_get (x : Nat) {j : Nat} (hj : j < 133) : (vec5 x)[j]! = lane5 x j := by
  unfold vec5
  rw [LyM.ofFn_get! _ hj]

theorem dig5_sound {x : Nat} {cs : List Char} (h : dig5K x cs = true) :
    digitVec (String.ofList cs) = vec5 x := by
  obtain ⟨hl, hd⟩ := F5Lane.dig5K_spec h
  unfold digitVec vec5
  rw [String.toList_ofList]
  apply Array.ext
  · simp [hl]
  · intro t h1 h2
    have ht : t < 133 := by simpa using h2
    have e := hd t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at e
    simp only [List.getElem_toArray, List.getElem_map, Array.getElem_ofFn]
    exact e

theorem vec5_all {x : Nat} (hx : canon5 x = true) : (vec5 x).all (· < 5) = true :=
  F5Lane.all_ofFn_lt fun j => F5Lane.canon5_lane hx j.isLt

theorem mulM5_idR {X : Nat → Nat} (hX : Canon5 X) : mulM 5 133 (rows5 X) (idM 133) = rows5 X := by
  unfold mulM
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum]
  have e : ∀ j ∈ Finset.range 133, ((rows5 X)[i.val]!)[j]! * (col 133 (idM 133) k.val)[j]! =
      if j = k.val then lane5 (X i.val) j else 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [F5Lane.col_get _ hj', F5Lane.idM_get hj' k.isLt, rows5_get _ i.isLt hj']
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 k.isLt),
    Nat.mod_eq_of_lt (F5Lane.canon5_lane (hX i i.isLt) k.isLt)]

theorem invM5_eq {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) : invM 5 133 (rows5 X) = rows5 Y := by
  refine (LyM.invM_spec (d := 133) Nat.prime_five (y := fun i j => lane5 (Y i) j)
    (fun i hi j hj => F5Lane.canon5_lane (hY i hi) hj) fun i hi j hj => ?_).trans rfl
  have e := F5Lane.vm5_lane hY (hX i hi) hj
  rw [h i hi, F5Lane.lane5_idRow5] at e
  have e2 := congrArg (fun n : Nat => (n : ZMod 5)) e
  simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e2
  rw [Finset.sum_congr rfl fun k hk => by rw [rows5_get _ hi (Finset.mem_range.1 hk)], ← e2]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij.symm, Nat.cast_one]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), Nat.cast_zero]

theorem trans5_sound {T Tt : Nat → Nat} (h : ∀ i < 133, trRow5 T i = Tt i) :
    colsMat 133 (rows5 T) = rows5 Tt ∧ colsMat 133 (rows5 Tt) = rows5 T := by
  constructor
  · unfold colsMat
    conv_rhs => unfold rows5
    refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun t => ?_))
    rw [rows5_get _ t.isLt i.isLt, ← h i i.isLt, F5Lane.lane5_trRow5 _ _ t.isLt]
  · unfold colsMat
    conv_rhs => unfold rows5
    refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun t => ?_))
    rw [rows5_get _ t.isLt i.isLt, ← h t t.isLt, F5Lane.lane5_trRow5 _ _ i.isLt]

theorem mulVec5_sound {M : Nat → Nat} {x : Nat} (hM : Canon5 M) (hx : canon5 x = true) :
    mulVec 5 133 (colsMat 133 (rows5 M)) (vec5 x) = vec5 (vm5 M x) := by
  unfold mulVec
  conv_rhs => unfold vec5
  refine congrArg Array.ofFn (funext fun i => ?_)
  unfold dot
  rw [LyM.fold_sum, F5Lane.vm5_lane hM hx i.isLt]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  rw [F5Lane.colsMat_get _ i.isLt hj', rows5_get _ hj' i.isLt, vec5_get _ hj', Nat.mul_comm]

theorem lin5_sound {A B : Array (Array Nat)} {T1 T2 T3 T4 T5 C : Nat → Nat}
    (h1 : Canon5 T1) (h2 : Canon5 T2) (h3 : Canon5 T3) (h4 : Canon5 T4) (h5 : Canon5 T5)
    (e1 : wordM (seedSel A B) [2, 1, 2, 1] = rows5 T1) (e2 : wordM (seedSel A B) [2, 1] = rows5 T2)
    (e3 : B = rows5 T3) (e4 : wordM (seedSel A B) [1, 2, 2, 1] = rows5 T4)
    (e5 : wordM (seedSel A B) [2, 2] = rows5 T5)
    (h : ∀ i < 133, C i = red5 (Nat.add (T1 i) (Nat.add (Nat.mul 3 (T2 i))
      (Nat.add (Nat.mul 2 (T3 i)) (Nat.add (Nat.mul 4 (T4 i)) (T5 i)))))) :
    cRows A B = rows5 C := by
  unfold cRows
  simp only [e1, e2, e4, e5]
  rw [e3]
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  simp only [Fin.getElem!_fin]
  rw [rows5_get _ i.isLt j.isLt, rows5_get _ i.isLt j.isLt, rows5_get _ i.isLt j.isLt,
    rows5_get _ i.isLt j.isLt, rows5_get _ i.isLt j.isLt, h i i.isLt, F5Lane.lane5_red5 _ j.isLt]
  have r1 := F5Lane.row_expand (F5Lane.canon5_lt (h1 i i.isLt))
  have r2 := F5Lane.row_expand (F5Lane.canon5_lt (h2 i i.isLt))
  have r3 := F5Lane.row_expand (F5Lane.canon5_lt (h3 i i.isLt))
  have r4 := F5Lane.row_expand (F5Lane.canon5_lt (h4 i i.isLt))
  have r5 := F5Lane.row_expand (F5Lane.canon5_lt (h5 i i.isLt))
  have e : Nat.add (T1 i.val) (Nat.add (Nat.mul 3 (T2 i.val))
      (Nat.add (Nat.mul 2 (T3 i.val)) (Nat.add (Nat.mul 4 (T4 i.val)) (T5 i.val)))) =
      ∑ k ∈ Finset.range 133, (lane5 (T1 i.val) k + 3 * lane5 (T2 i.val) k +
        2 * lane5 (T3 i.val) k + 4 * lane5 (T4 i.val) k + lane5 (T5 i.val) k) * 2 ^ (16 * k) := by
    change T1 i.val + (3 * T2 i.val + (2 * T3 i.val + (4 * T4 i.val + T5 i.val))) = _
    conv_lhs => rw [r1, r2, r3, r4, r5]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hb : ∀ k < 133, lane5 (T1 i.val) k + 3 * lane5 (T2 i.val) k + 2 * lane5 (T3 i.val) k +
      4 * lane5 (T4 i.val) k + lane5 (T5 i.val) k < 2 ^ 16 := fun k hk => by
    have a1 := F5Lane.canon5_lane (h1 i i.isLt) hk
    have a2 := F5Lane.canon5_lane (h2 i i.isLt) hk
    have a3 := F5Lane.canon5_lane (h3 i i.isLt) hk
    have a4 := F5Lane.canon5_lane (h4 i i.isLt) hk
    have a5 := F5Lane.canon5_lane (h5 i i.isLt) hk
    omega
  rw [e, F5Lane.lane_sum5 hb j.isLt]

private theorem rows5_row (V : Nat → Nat) {t : Nat} (ht : t < 133) : (rows5 V)[t]! = vec5 (V t) := by
  unfold rows5
  rw [LyM.ofFn_get! _ ht]
  rfl

private theorem canon5_of {x : Nat} (hx : x < 2 ^ 2128) (hl : ∀ j < 133, lane5 x j < 5) :
    canon5 x = true := by
  unfold canon5
  refine (CFSG.KS.bAnd_iff _ _).2 ⟨?_, CFSG.KS.Raw.allN_of_forall fun j hj => ?_⟩
  · have e : x >>> 2128 = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hx
    exact Nat.beq_eq_true_eq _ _ ▸ e
  · exact Eq.mpr Nat.blt_eq (hl j hj)

private theorem xy_cast {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) (i : Nat) (hi : i < 133) (j : Nat) (hj : j < 133) :
    ∑ k ∈ Finset.range 133, ((lane5 (X i) k : Nat) : ZMod 5) * ((lane5 (Y k) j : Nat) : ZMod 5) =
      if i = j then 1 else 0 := by
  have e := F5Lane.vm5_lane hY (hX i hi) hj
  rw [h i hi, F5Lane.lane5_idRow5] at e
  have e2 := congrArg (fun n : Nat => (n : ZMod 5)) e
  simp only [ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul] at e2
  rw [← e2]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij.symm, Nat.cast_one]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij), Nat.cast_zero]

private theorem comm_cast {d : Nat} {x y : Nat → Nat → ZMod 5}
    (h : ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, x i k * y k j = if i = j then 1 else 0) :
    ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, y i k * x k j = if i = j then 1 else 0 := by
  let Mx : Matrix (Fin d) (Fin d) (ZMod 5) := fun a b => x a.val b.val
  let My : Matrix (Fin d) (Fin d) (ZMod 5) := fun a b => y a.val b.val
  have h1 : Mx * My = 1 := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_eq_sum_range (fun k => x a.val k * y k b.val),
      h a.val a.isLt b.val b.isLt, Matrix.one_apply]
    simp [Fin.ext_iff]
  have h2 : My * Mx = 1 := mul_eq_one_comm.1 h1
  intro i hi j hj
  have e := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
  rw [Matrix.mul_apply, Fin.sum_univ_eq_sum_range (fun k => y i k * x k j), Matrix.one_apply] at e
  rw [e]
  simp [Fin.ext_iff]

private theorem mulM_idM_of {p d : Nat} (hp : 1 < p) {P Q : Array (Array Nat)}
    (h : ∀ i < d, ∀ k < d, ∑ j ∈ Finset.range d,
      (((P[i]!)[j]! : Nat) : ZMod p) * (((Q[j]!)[k]! : Nat) : ZMod p) = if i = k then 1 else 0) :
    mulM p d P Q = idM d := by
  unfold mulM idM
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum]
  have hd : (if i.val = k.val then 1 else 0) < p := by split_ifs <;> omega
  refine (LyM.mod_of_cast hd ?_).symm
  rw [Nat.cast_sum, Finset.sum_congr rfl fun j hj => by
    rw [F5Lane.col_get _ (Finset.mem_range.1 hj), Nat.cast_mul], h i i.isLt k k.isLt]
  split_ifs <;> simp

theorem inv5_sound {X Y : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = idRow5 i) :
    (mulM 5 133 (rows5 X) (invM 5 133 (rows5 X)) == idM 133) = true ∧
      (mulM 5 133 (colsMat 133 (rows5 X)) (invM 5 133 (colsMat 133 (rows5 X))) == idM 133) =
        true := by
  constructor
  · rw [invM5_eq hX hY h, mulM5_sound hX hY h, rows5_eq_idM fun i _ => rfl]
    exact beq_self_eq_true _
  · have hYX := comm_cast (d := 133) (x := fun i k => ((lane5 (X i) k : Nat) : ZMod 5))
      (y := fun k j => ((lane5 (Y k) j : Nat) : ZMod 5)) (xy_cast hX hY h)
    have hT : ∀ i < 133, ∀ k < 133, ∑ j ∈ Finset.range 133,
        ((lane5 (X j) i : Nat) : ZMod 5) * ((lane5 (Y k) j : Nat) : ZMod 5) =
          if i = k then 1 else 0 := by
      intro i hi k hk
      rw [Finset.sum_congr rfl fun j _ => mul_comm _ _, hYX k hk i hi]
      by_cases hik : i = k
      · rw [ite_eq_left hik, ite_eq_left hik.symm]
      · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]
    have hP : ∀ i < 133, ∀ j < 133, ((colsMat 133 (rows5 X))[i]!)[j]! = lane5 (X j) i :=
      fun i hi j hj => by rw [F5Lane.colsMat_get _ hi hj, rows5_get _ hj hi]
    have hinv := LyM.invM_spec (d := 133) Nat.prime_five (X := colsMat 133 (rows5 X))
      (y := fun i j => lane5 (Y j) i) (fun i _ j hj => F5Lane.canon5_lane (hY j hj) (by omega))
      fun i hi j hj => by
        rw [← hT i hi j hj]
        exact Finset.sum_congr rfl fun k hk => by rw [hP i hi k (Finset.mem_range.1 hk)]
    rw [hinv, mulM_idM_of (by norm_num) fun i hi k hk => ?_]
    · exact beq_self_eq_true _
    · rw [← hT i hi k hk]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      rw [hP i hi j hj', LyM.ofFn_get! _ hj', LyM.ofFn_get! _ hk]

private theorem skipOne_lt {b : Nat} (hb : b < 132) : skipOne b < 133 := by
  unfold skipOne
  split_ifs <;> omega

private theorem skipOne_ne {b : Nat} : skipOne b ≠ 1 := by
  unfold skipOne
  split_ifs <;> omega

private theorem skipOne_inj {a b : Nat} : skipOne a = skipOne b ↔ a = b := by
  unfold skipOne
  split_ifs <;> omega

private theorem sum_skipOne (g : Nat → ZMod 5) :
    ∑ j ∈ Finset.range 133, g j = g 1 + ∑ b ∈ Finset.range 132, g (skipOne b) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ' (fun b => g (skipOne b))]
  have e : ∀ b, skipOne (b + 1) = b + 1 + 1 := fun b => by
    unfold skipOne
    split_ifs <;> omega
  simp only [e]
  have e0 : skipOne 0 = 0 := rfl
  rw [e0]
  ring

private theorem minorRows_get (X : Array (Array Nat)) {a b : Nat} (ha : a < 132) (hb : b < 132) :
    ((minorRows X)[a]!)[b]! = (X[skipOne a]!)[skipOne b]! := by
  unfold minorRows
  rw [LyM.ofFn_get! _ ha, LyM.ofFn_get! _ hb]

private theorem fixRow5_one (C : Nat → Nat) : fixRow5 C 1 = idRow5 1 := rfl

private theorem fixRow5_eq {C : Nat → Nat} (hC : Canon5 C) {i : Nat} (hi : i < 133) (h1 : i ≠ 1) :
    fixRow5 C i = ∑ j ∈ Finset.range 133, (if j = 1 then 0 else lane5 (C i) j) * 2 ^ (16 * j) := by
  unfold fixRow5
  have hb : ¬ Nat.beq i 1 = true := fun hc => h1 (Nat.eq_of_beq_eq_true hc)
  rw [LyM.nIf_eqL, ite_eq_right hb]
  change C i - lane5 (C i) 1 <<< 16 = _
  rw [Nat.shiftLeft_eq]
  have e : ∀ j, lane5 (C i) j * 2 ^ (16 * j) = (if j = 1 then 0 else lane5 (C i) j) * 2 ^ (16 * j) +
      if j = 1 then lane5 (C i) 1 * 2 ^ 16 else 0 := fun j => by
    by_cases hj : j = 1
    · subst hj
      simp
    · simp [hj]
  have hCi : C i = ∑ j ∈ Finset.range 133, (if j = 1 then 0 else lane5 (C i) j) * 2 ^ (16 * j) +
      lane5 (C i) 1 * 2 ^ 16 := by
    conv_lhs => rw [F5Lane.row_expand (F5Lane.canon5_lt (hC i hi))]
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq',
      ite_eq_left (by simp)]
  exact Nat.sub_eq_of_eq_add hCi

private theorem fix_lt {C : Nat → Nat} (hC : Canon5 C) {i : Nat} (hi : i < 133) :
    ∀ t < 133, (if t = 1 then 0 else lane5 (C i) t) < 2 ^ 16 := fun t ht => by
  have := F5Lane.canon5_lane (hC i hi) ht
  split_ifs <;> omega

private theorem lane5_fixRow5 {C : Nat → Nat} (hC : Canon5 C) {i : Nat} (hi : i < 133) {j : Nat}
    (hj : j < 133) : lane5 (fixRow5 C i) j =
      if i = 1 then (if j = 1 then 1 else 0) else if j = 1 then 0 else lane5 (C i) j := by
  by_cases h1 : i = 1
  · subst h1
    rw [ite_eq_left rfl, fixRow5_one, F5Lane.lane5_idRow5]
  · rw [ite_eq_right h1, fixRow5_eq hC hi h1, F5Lane.lane_sum5 (fix_lt hC hi) hj]

private theorem canon5_fixRow5 {C : Nat → Nat} (hC : Canon5 C) : Canon5 (fixRow5 C) := by
  intro i hi
  by_cases h1 : i = 1
  · subst h1
    rw [fixRow5_one]
    exact canon5_of (F5Lane.idRow5_lt (by omega)) fun j _ => by
      rw [F5Lane.lane5_idRow5]
      split_ifs <;> omega
  · refine canon5_of ?_ fun j hj => ?_
    · rw [fixRow5_eq hC hi h1]
      have h := F5Lane.sum_lt _ 133 (fix_lt hC hi)
      have e : 16 * 133 = 2128 := rfl
      rwa [e] at h
    · rw [lane5_fixRow5 hC hi hj, ite_eq_right h1]
      have := F5Lane.canon5_lane (hC i hi) hj
      split_ifs <;> omega

theorem minor5_sound {C C' Y : Nat → Nat} (hC : Canon5 C) (hY : Canon5 Y)
    (hfix : ∀ i < 133, C' i = fixRow5 C i) (h : ∀ i < 133, vm5 Y (C' i) = idRow5 i) :
    (mulM 5 132 (minorRows (rows5 C)) (invM 5 132 (minorRows (rows5 C))) == idM 132) = true := by
  have hC' : Canon5 C' := fun i hi => by
    rw [hfix i hi]
    exact canon5_fixRow5 hC i hi
  have hM : ∀ a < 132, ∀ c < 132, ∑ b ∈ Finset.range 132,
      ((lane5 (C (skipOne a)) (skipOne b) : Nat) : ZMod 5) *
        ((lane5 (Y (skipOne b)) (skipOne c) : Nat) : ZMod 5) = if a = c then 1 else 0 := by
    intro a ha c hc
    have e := xy_cast hC' hY h (skipOne a) (skipOne_lt ha) (skipOne c) (skipOne_lt hc)
    rw [sum_skipOne, hfix _ (skipOne_lt ha), lane5_fixRow5 hC (skipOne_lt ha) (by norm_num),
      ite_eq_right skipOne_ne, ite_eq_left rfl, Nat.cast_zero, zero_mul, zero_add] at e
    have e' : ∑ b ∈ Finset.range 132, ((lane5 (C (skipOne a)) (skipOne b) : Nat) : ZMod 5) *
        ((lane5 (Y (skipOne b)) (skipOne c) : Nat) : ZMod 5) =
        ∑ b ∈ Finset.range 132, ((lane5 (fixRow5 C (skipOne a)) (skipOne b) : Nat) : ZMod 5) *
        ((lane5 (Y (skipOne b)) (skipOne c) : Nat) : ZMod 5) :=
      Finset.sum_congr rfl fun b hb => by
        rw [lane5_fixRow5 hC (skipOne_lt ha) (skipOne_lt (Finset.mem_range.1 hb)),
          ite_eq_right skipOne_ne, ite_eq_right skipOne_ne]
    rw [e', e]
    by_cases hac : a = c
    · rw [ite_eq_left hac, ite_eq_left (skipOne_inj.2 hac)]
    · rw [ite_eq_right hac, ite_eq_right fun hc => hac (skipOne_inj.1 hc)]
  have hP : ∀ a < 132, ∀ b < 132, ((minorRows (rows5 C))[a]!)[b]! =
      lane5 (C (skipOne a)) (skipOne b) := fun a ha b hb => by
    rw [minorRows_get _ ha hb, rows5_get _ (skipOne_lt ha) (skipOne_lt hb)]
  have hinv := LyM.invM_spec (d := 132) Nat.prime_five (X := minorRows (rows5 C))
    (y := fun b c => lane5 (Y (skipOne b)) (skipOne c))
    (fun b hb c hc => F5Lane.canon5_lane (hY _ (skipOne_lt hb)) (skipOne_lt hc))
    fun a ha c hc => by
      rw [← hM a ha c hc]
      exact Finset.sum_congr rfl fun b hb => by rw [hP a ha b (Finset.mem_range.1 hb)]
  rw [hinv, mulM_idM_of (by norm_num) fun a ha c hc => ?_]
  · exact beq_self_eq_true _
  · rw [← hM a ha c hc]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    rw [hP a ha b hb', LyM.ofFn_get! _ hb', LyM.ofFn_get! _ hc]

private theorem arr_ext5 {a b : Array (Array Nat)} (hs : a.size = b.size)
    (h : ∀ i < a.size, a[i]! = b[i]!) : a = b :=
  Array.ext hs fun i h1 h2 => by
    rw [← getElem!_pos a i h1, ← getElem!_pos b i h2]
    exact h i h1

theorem rec5_sound {w : Array Nat} {step : Nat → Array Nat → Array Nat} {recs : List (Nat × Nat)}
    {V : Nat → Nat} (hlen : recs.length = 133) (h0 : vec5 (V 0) = w)
    (hs : ∀ i, 1 ≤ i → i < 133 → (recs.getD i (0, 0)).1 < i ∧
      ((recs.getD i (0, 0)).2 = 1 ∨ (recs.getD i (0, 0)).2 = 2) ∧
      step (recs.getD i (0, 0)).2 (vec5 (V (recs.getD i (0, 0)).1)) = vec5 (V i)) :
    recVecs w step recs = rows5 V ∧ recOK w step recs (rows5 V) = true := by
  have push_lt : ∀ (acc : Array (Array Nat)) (v : Array Nat) {t : Nat}, t < acc.size →
      (acc.push v)[t]! = acc[t]! := fun acc v t ht => by
    rw [getElem!_pos (acc.push v) t (by rw [Array.size_push]; omega), getElem!_pos acc t ht,
      Array.getElem_push_lt]
  have push_eq : ∀ (acc : Array (Array Nat)) (v : Array Nat), (acc.push v)[acc.size]! = v :=
    fun acc v => by
      rw [getElem!_pos (acc.push v) acc.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]
  have inv : ∀ m, m ≤ 132 →
      (((recs.drop 1).take m).foldl (fun acc r => acc.push (step r.2 acc[r.1]!)) #[w]).size =
        m + 1 ∧
      ∀ t < m + 1, (((recs.drop 1).take m).foldl
        (fun acc r => acc.push (step r.2 acc[r.1]!)) #[w])[t]! = vec5 (V t) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨rfl, fun t ht => ?_⟩
      obtain rfl : t = 0 := by omega
      exact h0.symm
    | succ m ih =>
      intro hm
      obtain ⟨ihs, ihg⟩ := ih (by omega)
      have hr : (recs.drop 1)[m]? = some (recs.getD (m + 1) (0, 0)) := by
        rw [List.getElem?_drop, List.getD_eq_getElem?_getD, Nat.add_comm 1 m,
          List.getElem?_eq_getElem (by omega : m + 1 < recs.length), Option.getD_some]
      rw [List.take_add_one, hr, Option.toList_some, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      generalize ((recs.drop 1).take m).foldl
        (fun acc r => acc.push (step r.2 acc[r.1]!)) #[w] = acc at ihs ihg
      obtain ⟨hlt, -, he⟩ := hs (m + 1) (by omega) (by omega)
      refine ⟨by rw [Array.size_push, ihs], fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (m + 1) with htm | htm
      · rw [push_lt _ _ (by omega), ihg t htm]
      · obtain rfl : t = m + 1 := by omega
        rw [← ihs, push_eq, ihs, ihg _ hlt, he]
  have hL : (recs.drop 1).take 132 = recs.drop 1 :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  obtain ⟨hsz, hget⟩ := inv 132 le_rfl
  rw [hL] at hsz hget
  have hsz' : (recVecs w step recs).size = 133 := hsz
  have hget' : ∀ i < 133, (recVecs w step recs)[i]! = vec5 (V i) := hget
  have hrs : (rows5 V).size = 133 := by
    unfold rows5
    exact Array.size_ofFn
  have hR : recVecs w step recs = rows5 V := by
    generalize recVecs w step recs = R at hsz' hget'
    generalize hRV : rows5 V = S at hrs
    have hS : ∀ i < 133, S[i]! = vec5 (V i) := fun i hi => by rw [← hRV, rows5_row V hi]
    exact arr_ext5 (by rw [hsz', hrs]) fun i hi => by rw [hget' i (by omega), hS i (by omega)]
  refine ⟨hR, ?_⟩
  unfold recOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨hlen, hrs⟩, ?_⟩, fun i hi => ?_⟩
  · rw [rows5_row V (by norm_num), h0]
  · by_cases i0 : i = 0
    · subst i0
      exact Bool.or_eq_true_iff.2 (Or.inl rfl)
    · have hr : recs[i]! = recs.getD i (0, 0) := by
        rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        rfl
      obtain ⟨hlt, hl, he⟩ := hs i (by omega) hi
      rw [hr, rows5_row V hi, rows5_row V (by omega), he]
      refine Bool.or_eq_true_iff.2 (Or.inr ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
      exact ⟨⟨hlt, hl⟩, trivial⟩

theorem entry2_rows {MT OP L R : Nat → Nat} {k o l r : Nat}
    (h : ∀ b < 7, entryOK2 MT OP L R k b = true) (ho : OP k = o) (hl : L k = l) (hr : R k = r) :
    ∀ i < 133, specRow MT o l r k i = true := by
  refine rows_of_blocks fun b hb => ?_
  have := h b hb
  unfold entryOK2 at this
  rw [ho, hl, hr, CFSG.KS.Raw.strictB_eq, CFSG.KS.Raw.strictB_eq, CFSG.KS.Raw.strictB_eq] at this
  exact this

theorem entry2_mul {MT OP L R : Nat → Nat} {k l r : Nat}
    (h : ∀ b < 7, entryOK2 MT OP L R k b = true) (ho : OP k = 0) (hl : L k = l) (hr : R k = r) :
    ∀ i < 133, vm5 (slice5 MT r) (slice5 MT l i) = slice5 MT k i := fun i hi =>
  Nat.eq_of_beq_eq_true (entry2_rows h ho hl hr i hi)

theorem entry2_copy {MT OP L R : Nat → Nat} {k l : Nat}
    (h : ∀ b < 7, entryOK2 MT OP L R k b = true) (ho : OP k = 1) (hl : L k = l) :
    ∀ i < 133, slice5 MT l i = slice5 MT k i := fun i hi =>
  Nat.eq_of_beq_eq_true (entry2_rows h ho hl rfl i hi)

theorem entry2_tr {MT OP L R : Nat → Nat} {k l : Nat}
    (h : ∀ b < 7, entryOK2 MT OP L R k b = true) (ho : OP k = 3) (hl : L k = l) :
    ∀ i < 133, trRow5 (slice5 MT l) i = slice5 MT k i := fun i hi =>
  Nat.eq_of_beq_eq_true (entry2_rows h ho hl rfl i hi)

end CFSG.KS.SporSch

end

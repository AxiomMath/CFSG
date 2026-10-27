module

public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public import CFSG.Certificates.Kernel.SporSch.J3F80.Tri
public import CFSG.Certificates.Kernel.SporSch.InvRowsF2Sound
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch.J3F.SepPf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS CFSG.KS.SporSch CFSG.KS.Raw CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.Schreier.PairJ3
open CFSG.Sporadic.SmallF2.Native
open CFSG.KS.SporSch.J3F.Pad CFSG.KS.SporSch.J3F.Tri
open scoped Matrix

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem arr_ext {X Y : Array Nat} (hs : X.size = Y.size)
    (h : ∀ r < X.size, X[r]?.getD 0 = Y[r]?.getD 0) : X = Y := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  rwa [getElem?_pos X i h1, getElem?_pos Y i h2, Option.getD_some, Option.getD_some] at this

private theorem mulRows_get {X Y : Array Nat} {r : Nat} (hr : r < X.size) :
    (mulRows 80 X Y)[r]?.getD 0 = vecMulN 80 Y (X[r]?.getD 0) := by
  simp [mulRows, hr]

private theorem idRows_size : (idRows 80).size = 80 := by simp [idRows]

private theorem fold_congr (Y : Array Nat) {x y : Nat} : ∀ (l : List Nat) (acc : Nat),
    (∀ j ∈ l, x.testBit j = y.testBit j) →
    l.foldl (fun acc j => if x.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc =
      l.foldl (fun acc j => if y.testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc
  | [], _, _ => rfl
  | j :: l, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, h j List.mem_cons_self]
    exact fold_congr Y l _ fun i hi => h i (List.mem_cons_of_mem _ hi)

private theorem vec_congr (Y : Array Nat) {x y : Nat} (h : CFSG.Sporadic.SmallF2.toVecD 80 x =
    CFSG.Sporadic.SmallF2.toVecD 80 y) : vecMulN 80 Y x = vecMulN 80 Y y := by
  unfold vecMulN
  refine fold_congr Y _ 0 fun j hj => ?_
  have hj' := List.mem_range.1 hj
  have := congrFun h ⟨j, hj'⟩
  simp only [CFSG.Sporadic.SmallF2.toVecD_apply] at this
  cases hxj : x.testBit j <;> cases hyj : y.testBit j <;> simp_all

private theorem fold_zero (Y : Array Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun acc j => if (0 : Nat).testBit j then acc ^^^ (Y[j]?.getD 0) else acc) acc = acc
  | [], _ => rfl
  | j :: l, acc => by
    rw [List.foldl_cons]
    have e : (if (0 : Nat).testBit j = true then acc ^^^ (Y[j]?.getD 0) else acc) = acc := by
      simp
    rw [e]
    exact fold_zero Y l acc

private theorem vec_zero (Y : Array Nat) : vecMulN 80 Y 0 = 0 := by
  unfold vecMulN
  exact fold_zero Y _ 0

private theorem comm_of {d : Nat} {L Y : Array Nat} (hL : mulRows d L Y = idRows d) :
    CFSG.Sporadic.SmallF2.rowsMatrix d Y * CFSG.Sporadic.SmallF2.rowsMatrix d L = 1 := by
  have h2 := congrArg (CFSG.Sporadic.SmallF2.rowsMatrix d) hL
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_mulRows, CFSG.Sporadic.SmallF2.rowsMatrix_idRows] at h2
  exact mul_eq_one_comm.1 h2

private theorem inv_unique {d : Nat} {G L Y : Array Nat} (hG : mulRows d G Y = idRows d)
    (hL : mulRows d L Y = idRows d) :
    CFSG.Sporadic.SmallF2.rowsMatrix d G = CFSG.Sporadic.SmallF2.rowsMatrix d L := by
  have h1 := congrArg (CFSG.Sporadic.SmallF2.rowsMatrix d) hG
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_mulRows, CFSG.Sporadic.SmallF2.rowsMatrix_idRows] at h1
  calc CFSG.Sporadic.SmallF2.rowsMatrix d G
      = CFSG.Sporadic.SmallF2.rowsMatrix d G * (CFSG.Sporadic.SmallF2.rowsMatrix d Y *
          CFSG.Sporadic.SmallF2.rowsMatrix d L) := by rw [comm_of hL, mul_one]
    _ = CFSG.Sporadic.SmallF2.rowsMatrix d L := by rw [← mul_assoc, h1, one_mul]

private theorem left_inv (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {A : Nat}
    {Y : Array Nat} (hY : Wf80 Y) (h : mulJ c rm A (enc80 Y) = dgK) :
    (∀ r < 112, vecMulN 80 Y (row80 A r) = (idRows 80)[r]?.getD 0) ∧
      ∃ L : Array Nat, mulRows 80 L Y = idRows 80 ∧ ∀ r < 80, L[r]?.getD 0 = row80 A r := by
  rw [mulJ_enc80 hK A hY, id80.2] at h
  have hW : CFSG.KS.SporSch.J4B.WfN
      (Array.ofFn (n := 112) fun r => vecMulN 80 Y (row80 A r.val)) := by
    refine ⟨Array.size_ofFn, fun i hi => ?_⟩
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
    exact Nat.lt_of_lt_of_le (CFSG.Sporadic.J4Schreier.vecMulN_lt hY.2 _)
      (Nat.pow_le_pow_right (by omega) (by omega))
  have he := CFSG.KS.SporSch.J4B.enc_inj hW (wf_pad id80.1) h
  have hrow : ∀ r < 112, vecMulN 80 Y (row80 A r) = (idRows 80)[r]?.getD 0 := by
    intro r hr
    have := congrArg (fun X : Array Nat => X[r]?.getD 0) he
    simp only [pad112, Array.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some] at this
    exact this
  refine ⟨hrow, Array.ofFn (n := 80) fun r => row80 A r.val, ?_, fun r hr => by
    simp only [Array.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]⟩
  refine arr_ext (by rw [size_mulRows, Array.size_ofFn, idRows_size]) fun r hr => ?_
  have hr' : r < 80 := by rw [size_mulRows, Array.size_ofFn] at hr; exact hr
  rw [mulRows_get (by rw [Array.size_ofFn]; exact hr'), ← hrow r (by omega)]
  simp only [Array.getElem?_ofFn, hr', ↓reduceDIte, Option.getD_some]

private theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by
    rw [List.getD_nil]
    rfl
  | _ :: _, 0 => rfl
  | m :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact getN_eq d l i

private theorem getN_arr (S : List Nat) (k : Nat) : getN (nat_lit 0) S k = S.toArray[k]! := by
  rw [getN_eq, List.getD_eq_getElem?_getD]
  by_cases hk : k < S.length
  · rw [getElem?_pos S k hk, Option.getD_some, getElem!_pos S.toArray k (by simpa using hk),
      List.getElem_toArray]
  · rw [getElem?_neg S k hk, Option.getD_none, getElem!_neg S.toArray k (by simpa using hk)]
    rfl

private theorem mats_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {zB RB : Nat}
    {zs : List Nat} (hzs : zs.length = 4)
    (hB : mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 zB) = dgK) :
    ∀ i < 4, Wf80 (Array.ofFn fun r : Fin 4 =>
        mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD r.val 0)))[i]! ∧
      getN (nat_lit 0) (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) i =
        enc80 (Array.ofFn fun r : Fin 4 =>
          mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD r.val 0)))[i]! := by
  intro i hi
  obtain ⟨hBw, hBe⟩ := polarK_eq hK zB
  rw [hBe] at hB
  obtain ⟨hrow, L, hL, hLr⟩ := left_inv hK hBw hB
  have hGB := CFSG.KS.SporSch.InvF2.invRowsF2_mul_of_mul hBw.1 hBw.2 hL
  have hGs : (invRowsF2 80 (polarRowsZ 80 zB)).size = 80 := by
    have := congrArg Array.size hGB
    rwa [size_mulRows, idRows_size] at this
  have hGL := inv_unique hGB hL
  have hBL : CFSG.Sporadic.SmallF2.rowsMatrix 80 (polarRowsZ 80 zB) *
      CFSG.Sporadic.SmallF2.rowsMatrix 80 L = 1 := comm_of hL
  obtain ⟨hCw, hCe⟩ := polarK_eq hK (zs.getD i 0)
  have hTi : (Array.ofFn fun r : Fin 4 =>
      mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD r.val 0)))[i]! =
      mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD i 0)) := by
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]
  rw [hTi]
  have hget : getN (nat_lit 0) (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) i =
      mulJ c rm RB (enc80 (polarRowsZ 80 (zs.getD i 0))) := by
    rw [getN_eq, List.getD_eq_getElem?_getD, List.getElem?_map, ← hCe,
      List.getD_eq_getElem?_getD, getElem?_pos zs i (by omega), Option.map_some, Option.getD_some,
      Option.getD_some]
  rw [hget, mulJ_enc80 hK RB hCw]
  have hW : Wf80 (mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD i 0))) :=
    ⟨by rw [size_mulRows, hGs], fun r hr => by
      rw [mulRows_get (by rw [hGs]; exact hr)]
      exact CFSG.Sporadic.J4Schreier.vecMulN_lt hCw.2 _⟩
  refine ⟨hW, ?_⟩
  unfold enc80
  apply congrArg CFSG.KS.SporSch.J4B.encN
  refine arr_ext (by rw [Array.size_ofFn, pad112, Array.size_ofFn]) fun r hr => ?_
  have hr112 : r < 112 := by rw [Array.size_ofFn] at hr; exact hr
  simp only [pad112, Array.getElem?_ofFn, hr112, ↓reduceDIte, Option.getD_some]
  by_cases hr80 : r < 80
  · rw [mulRows_get (by rw [hGs]; exact hr80)]
    apply vec_congr
    funext j
    have := congrFun (congrFun hGL ⟨r, hr80⟩) j
    change CFSG.Sporadic.SmallF2.toVecD 80 ((invRowsF2 80 (polarRowsZ 80 zB))[r]?.getD 0) j =
      CFSG.Sporadic.SmallF2.toVecD 80 (L[r]?.getD 0) j at this
    rw [hLr r hr80] at this
    exact this.symm
  · rw [getElem?_neg _ r (by rw [size_mulRows, hGs]; exact hr80), Option.getD_none]
    have hx0 := hrow r hr112
    rw [getElem?_neg (idRows 80) r (by rw [idRows_size]; exact hr80), Option.getD_none] at hx0
    have hz : CFSG.Sporadic.SmallF2.toVecD 80 (row80 RB r) = 0 := by
      have e := CFSG.Sporadic.SmallF2.toVecD_vecMulN 80 (polarRowsZ 80 zB) (row80 RB r)
      rw [hx0, CFSG.Sporadic.SmallF2.toVecD_zero] at e
      calc CFSG.Sporadic.SmallF2.toVecD 80 (row80 RB r)
          = CFSG.Sporadic.SmallF2.toVecD 80 (row80 RB r) ᵥ*
              (CFSG.Sporadic.SmallF2.rowsMatrix 80 (polarRowsZ 80 zB) *
                CFSG.Sporadic.SmallF2.rowsMatrix 80 L) := by rw [hBL, Matrix.vecMul_one]
        _ = 0 := by rw [← Matrix.vecMul_vecMul, ← e, Matrix.zero_vecMul]
    rw [vec_congr _ (hz.trans (CFSG.Sporadic.SmallF2.toVecD_zero 80).symm), vec_zero]

private theorem prod_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Ts : Array (Array Nat)}
    {ms : List Nat} (hT : ∀ i < 4, Wf80 Ts[i]! ∧ getN (nat_lit 0) ms i = enc80 Ts[i]!) :
    ∀ (w : List Nat), (∀ x ∈ w, x < 4) → ∀ (M : Nat) (X : Array Nat), Wf80 X → M = enc80 X →
      Wf80 (w.foldl (fun M x => mulRows 80 M Ts[x]!) X) ∧
        w.foldl (fun M x => mulJ c rm M (getN (nat_lit 0) ms x)) M =
          enc80 (w.foldl (fun M x => mulRows 80 M Ts[x]!) X)
  | [], _, _, _, hX, hM => ⟨hX, hM⟩
  | x :: w, hw, M, X, hX, hM => by
    obtain ⟨hTx, hgx⟩ := hT x (hw x List.mem_cons_self)
    obtain ⟨hW, hE⟩ := mul80 hK hX hTx
    rw [List.foldl_cons, List.foldl_cons]
    exact prod_eq hK hT w (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ _ hW
      (by rw [hM, hgx, hE])

private theorem add_get {X Y : Array Nat} (hX : X.size = 80) (hY : Y.size = 80) (i : Nat) :
    (addRows X Y)[i]?.getD 0 = X[i]?.getD 0 ^^^ Y[i]?.getD 0 := by
  by_cases hi : i < 80
  · rw [getElem?_pos (addRows X Y) i (by simp [addRows, hX, hY, hi]),
      getElem?_pos X i (by omega), getElem?_pos Y i (by omega)]
    simp [addRows]
  · rw [getElem?_neg _ i (by simp [addRows, hX, hY]; omega), getElem?_neg X i (by omega),
      getElem?_neg Y i (by omega)]
    rfl

private theorem xor_enc {X Y : Array Nat} (hX : Wf80 X) (hY : Wf80 Y) :
    Wf80 (addRows X Y) ∧ Nat.xor (enc80 X) (enc80 Y) = enc80 (addRows X Y) := by
  have hW : Wf80 (addRows X Y) := ⟨by simp [addRows, hX.1, hY.1], fun i hi => by
    rw [add_get hX.1 hY.1]
    exact Nat.xor_lt_two_pow (hX.2 i hi) (hY.2 i hi)⟩
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  change (enc80 X ^^^ enc80 Y).testBit p = _
  rw [Nat.testBit_xor, enc80_bit hX, enc80_bit hY, enc80_bit hW, add_get hX.1 hY.1,
    Nat.testBit_xor]
  cases decide (p / 128 < 80) <;> simp

private theorem zero_get (i : Nat) : (zeroRows 80)[i]?.getD 0 = 0 := by
  unfold zeroRows
  rw [Array.getElem?_replicate]
  split <;> rfl

private theorem zero_enc : Wf80 (zeroRows 80) ∧ (nat_lit 0) = enc80 (zeroRows 80) := by
  have hW : Wf80 (zeroRows 80) := ⟨by simp [zeroRows], fun i _ => by
    rw [zero_get]
    exact Nat.two_pow_pos _⟩
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  change (0 : Nat).testBit p = _
  rw [enc80_bit hW, zero_get]
  simp

private theorem comb_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Ts : Array (Array Nat)}
    {ms : List Nat} (hT : ∀ i < 4, Wf80 Ts[i]! ∧ getN (nat_lit 0) ms i = enc80 Ts[i]!) :
    ∀ (terms : List (List Nat)), (∀ w ∈ terms, ∀ x ∈ w, x < 4) → ∀ (a : Nat) (X : Array Nat),
      Wf80 X → a = enc80 X →
      Wf80 (terms.foldl (fun acc w => addRows acc (prodRows 80 Ts w)) X) ∧
        terms.foldl (fun acc w => Nat.xor acc (prodK c rm dgK ms w)) a =
          enc80 (terms.foldl (fun acc w => addRows acc (prodRows 80 Ts w)) X)
  | [], _, _, _, hX, ha => ⟨hX, ha⟩
  | w :: ts, hw, a, X, hX, ha => by
    obtain ⟨hPw, hPe⟩ := prod_eq hK hT w (hw w List.mem_cons_self) dgK (idRows 80) id80.1 id80.2
    have hPe' : prodK c rm dgK ms w = enc80 (prodRows 80 Ts w) := hPe
    have hPw' : Wf80 (prodRows 80 Ts w) := hPw
    obtain ⟨hA, hAe⟩ := xor_enc hX hPw'
    rw [List.foldl_cons, List.foldl_cons]
    exact comb_eq hK hT ts (fun u hu => hw u (List.mem_cons_of_mem _ hu)) _ _ hA
      (by rw [ha, hPe', hAe])

private theorem spin_list (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Ts : Array (Array Nat)}
    {ms : List Nat} (hT : ∀ i < 4, Wf80 Ts[i]! ∧ getN (nat_lit 0) ms i = enc80 Ts[i]!) :
    ∀ (tree : List (Nat × Nat)), (∀ t ∈ tree, t.2 < 4) → ∀ S : List Nat,
      (tree.foldl (fun S t => S ++ [colK rm t0 t1 t2 t3 t4 t5 t6 (getN (nat_lit 0) ms t.2)
        (getN (nat_lit 0) S t.1)]) S).toArray =
      tree.foldl (fun S t => S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) S.toArray
  | [], _, _ => rfl
  | t :: tr, ht, S => by
    obtain ⟨hTw, hTe⟩ := hT t.2 (ht t List.mem_cons_self)
    simp only [List.foldl_cons]
    rw [spin_list hK hT tr (fun u hu => ht u (List.mem_cons_of_mem _ hu)), hTe, colK_eq hK hTw,
      getN_arr, List.push_toArray]

private theorem sp_size (Ts : Array (Array Nat)) : ∀ (tree : List (Nat × Nat)) (S : Array Nat),
    (tree.foldl (fun S t => S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) S).size =
      S.size + tree.length
  | [], S => by simp
  | t :: tr, S => by
    simp only [List.foldl_cons]
    rw [sp_size Ts tr, Array.size_push, List.length_cons]
    omega

private theorem sp_prefix (Ts : Array (Array Nat)) : ∀ (tree : List (Nat × Nat)) (S : Array Nat),
    ∀ j < S.size, (tree.foldl (fun S t => S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) S)[j]! = S[j]!
  | [], _, _, _ => rfl
  | t :: tr, S, j, hj => by
    simp only [List.foldl_cons]
    rw [sp_prefix Ts tr _ j (by rw [Array.size_push]; omega),
      getElem!_pos _ j (by rw [Array.size_push]; omega), getElem!_pos S j hj,
      Array.getElem_push_lt hj]

private theorem sp_entry (Ts : Array (Array Nat)) : ∀ (tree : List (Nat × Nat)) (S : Array Nat),
    ∀ i (hi : i < tree.length), tree[i].1 < S.size + i →
      (tree.foldl (fun S t => S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) S)[S.size + i]! =
        mulVecRows 80 Ts[tree[i].2]!
          (tree.foldl (fun S t => S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) S)[tree[i].1]!
  | [], _, i, hi, _ => absurd hi (by simp)
  | t :: tr, S, 0, _, hp => by
    simp only [List.getElem_cons_zero, Nat.add_zero] at hp ⊢
    simp only [List.foldl_cons]
    have hpl : ∀ (x : Nat), ∀ j < S.size, (S.push x)[j]! = S[j]! := fun x j hj => by
      rw [getElem!_pos _ j (by rw [Array.size_push]; omega), getElem!_pos S j hj,
        Array.getElem_push_lt hj]
    rw [sp_prefix Ts tr _ S.size (by rw [Array.size_push]; omega),
      sp_prefix Ts tr _ t.1 (by rw [Array.size_push]; omega),
      getElem!_pos _ S.size (by rw [Array.size_push]; omega), Array.getElem_push_eq, hpl _ _ hp]
  | t :: tr, S, i + 1, hi, hp => by
    simp only [List.getElem_cons_succ] at hp ⊢
    simp only [List.foldl_cons]
    have := sp_entry Ts tr (S.push (mulVecRows 80 Ts[t.2]! S[t.1]!)) i
      (by simp only [List.length_cons] at hi; omega) (by rw [Array.size_push]; omega)
    rw [Array.size_push] at this
    rw [show S.size + (i + 1) = S.size + 1 + i by omega]
    exact this

private theorem mvr_lt (M : Array Nat) (x : Nat) : mulVecRows 80 M x < 2 ^ 80 := by
  unfold mulVecRows
  exact CFSG.Sporadic.J4Schreier.vecMulN_lt (fun j hj => by
    simp only [transposeRows, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    exact CFSG.Sporadic.SmallF2.ofBits_lt _ _) x

private theorem rows80K_of {L : List Nat} (hl : L.length = 80) (hlt : ∀ x ∈ L, x < 2 ^ 80) :
    rows80K L = true := by
  have hrec : ∀ L' : List Nat, (∀ x ∈ L', x < 2 ^ 80) → List.rec (motive := fun _ => Bool) true
      (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 80)))) L' = true := by
    intro L' h'
    induction L' with
    | nil => rfl
    | cons x L' ih =>
      have hx : Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 80)) = true := by
        apply Nat.blt_eq.mpr
        change x < 1 <<< 80
        rw [Nat.one_shiftLeft]
        exact h' x List.mem_cons_self
      show Bool.rec (motive := fun _ => Bool) false _
        (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 80))) = true
      rw [hx]
      exact ih fun y hy => h' y (List.mem_cons_of_mem _ hy)
  have h1 : Nat.beq L.length (nat_lit 80) = true := by
    rw [hl]
    rfl
  unfold rows80K
  rw [h1]
  exact hrec L hlt

private theorem core (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {SI v k : Nat}
    {T : Array (Array Nat)} {mats : List Nat} {terms : List (List Nat)} {P : Array Nat}
    {tree : List (Nat × Nat)} (hTs : T.size = 4)
    (hT : ∀ i < 4, Wf80 T[i]! ∧ getN (nat_lit 0) mats i = enc80 T[i]!)
    (hterms : ∀ w ∈ terms, ∀ x ∈ w, x < 4) (hv : v < 2 ^ 80)
    (hP : rows80K P.toList = true) (hk : k < 80) (hvk : v.testBit k = true)
    (hcol : colK rm t0 t1 t2 t3 t4 t5 t6 (combK c rm dgK mats terms) v = 0)
    (hPK : mulJ c rm (packRowsK P.toList) (combK c rm dgK mats terms) = projK dgK v k)
    (htl : tree.length = 79)
    (hall : ∀ i < 79, (tree.getD i (0, 0)).1 ≤ i ∧ (tree.getD i (0, 0)).2 < 4)
    (hSI : mulJ c rm SI (packRowsK (spinK rm t0 t1 t2 t3 t4 t5 t6 mats v tree)) = dgK) :
    sepF2OK 80 T terms v k P (invRowsF2 80 (spinVecs 80 T v tree)) tree
      (spinVecs 80 T v tree) = true := by
  have htr : ∀ i (hi : i < tree.length), tree[i]!.1 ≤ i ∧ tree[i]!.2 < 4 ∧
      tree[i]! = tree[i] := by
    intro i hi
    have e : tree.getD i (0, 0) = tree[i] := by
      rw [List.getD_eq_getElem?_getD, getElem?_pos tree i hi, Option.getD_some]
    have e' : tree[i]! = tree[i] := getElem!_pos tree i hi
    obtain ⟨h1, h2⟩ := hall i (by omega)
    rw [e] at h1 h2
    rw [e']
    exact ⟨h1, h2, rfl⟩
  have htr2 : ∀ t ∈ tree, t.2 < 4 := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
    have := (htr i hi).2.1
    rwa [(htr i hi).2.2] at this
  have hC : Wf80 (combRows 80 T terms) ∧
      combK c rm dgK mats terms = enc80 (combRows 80 T terms) :=
    comb_eq hK hT terms hterms (nat_lit 0) (zeroRows 80) zero_enc.1 zero_enc.2
  obtain ⟨hPw, hPp⟩ := rows80K_sound hP
  rw [Array.toArray_toList] at hPw hPp
  have hSL : (spinK rm t0 t1 t2 t3 t4 t5 t6 mats v tree).toArray = spinVecs 80 T v tree := by
    unfold spinK spinVecs
    exact spin_list hK hT tree htr2 [v]
  have hSsize : (spinVecs 80 T v tree).size = 80 := by
    unfold spinVecs
    rw [sp_size, htl]
    rfl
  have hS0 : (spinVecs 80 T v tree)[0]! = v := by
    unfold spinVecs
    rw [sp_prefix T tree _ 0 (by simp)]
    rfl
  have hSe : ∀ i (hi : i < tree.length), (spinVecs 80 T v tree)[i + 1]! =
      mulVecRows 80 T[tree[i].2]! (spinVecs 80 T v tree)[tree[i].1]! := by
    intro i hi
    have hp := (htr i hi).1
    rw [(htr i hi).2.2] at hp
    unfold spinVecs
    have := sp_entry T tree #[v] i hi (by rw [List.size_toArray, List.length_singleton]; omega)
    rw [show (#[v] : Array Nat).size + i = i + 1 from Nat.add_comm 1 i] at this
    exact this
  have hSlt : ∀ j < 80, (spinVecs 80 T v tree)[j]! < 2 ^ 80 := by
    intro j hj
    rcases j with _ | i
    · rw [hS0]
      exact hv
    · rw [hSe i (by omega)]
      exact mvr_lt _ _
  have hSw0 : rows80K (spinK rm t0 t1 t2 t3 t4 t5 t6 mats v tree) = true := by
    refine rows80K_of ?_ fun x hx => ?_
    · rw [← List.size_toArray, hSL, hSsize]
    · rw [← List.mem_toArray, hSL] at hx
      obtain ⟨j, hj, hx⟩ := Array.mem_iff_getElem.1 hx
      rw [← hx, ← getElem!_pos _ j hj]
      exact hSlt j (by rw [hSsize] at hj; exact hj)
  obtain ⟨hSw, hSp⟩ := rows80K_sound hSw0
  rw [hSL] at hSw hSp
  rw [hSp] at hSI
  obtain ⟨-, Ls, hLs, -⟩ := left_inv hK hSw hSI
  have hTS := CFSG.KS.SporSch.InvF2.invRowsF2_mul_of_mul hSw.1 hSw.2 hLs
  unfold sepF2OK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hvk⟩, ?_⟩, ?_⟩, hPw.1⟩, ?_⟩, ?_⟩, hS0⟩, ?_⟩, hSsize⟩, ?_⟩, hTS⟩
  · rw [Array.all_eq_true]
    intro i hi
    have := (hT i (by omega)).1.1
    rw [getElem!_pos T i hi] at this
    simp [this]
  · have e := hcol
    rw [hC.2, colK_eq hK hC.1] at e
    exact e
  · have e := hPK
    obtain ⟨hMw, hMe⟩ := mul80 hK hPw hC.1
    obtain ⟨hJw, hJe⟩ := projK_eq (v := v) hk
    rw [hPp, hC.2, hMe, hJe] at e
    exact enc80_inj hMw hJw e
  · rw [hSsize, htl]
  · rw [List.all_eq_true]
    intro i hi'
    have hi : i < tree.length := List.mem_range.1 hi'
    obtain ⟨hp, hr, he⟩ := htr i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨hp, by rw [hTs]; exact hr⟩, ?_⟩
    rw [he]
    exact hSe i hi
  · have := congrArg Array.size hTS
    rwa [size_mulRows, idRows_size] at this

private theorem sepK_parts {D zB RB v k P SI : Nat} {zs : List Nat} {terms : List (List Nat)}
    {tree : List (Nat × Nat)}
    (h : sepK c rm t0 t1 t2 t3 t4 t5 t6 D zB RB zs terms v k P tree SI = true) :
    mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 zB) = D ∧ k < 80 ∧ v.testBit k = true ∧
      colK rm t0 t1 t2 t3 t4 t5 t6
        (combK c rm D (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) terms) v = 0 ∧
      mulJ c rm P
        (combK c rm D (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) terms) =
        projK D v k ∧
      tree.length = 79 ∧
      (∀ i < 79, (tree.getD i (0, 0)).1 ≤ i ∧ (tree.getD i (0, 0)).2 < 4) ∧
      mulJ c rm SI (packRowsK (spinK rm t0 t1 t2 t3 t4 t5 t6
        (zs.map fun z => mulJ c rm RB (polarK t0 t1 t2 t3 t4 t5 t6 z)) v tree)) = D := by
  unfold sepK at h
  beta_reduce at h
  obtain ⟨hB, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hk, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hvk, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hcol, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hPK, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨htl, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨hall, hSI⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true hB, Eq.mp Nat.blt_eq hk, ?_, Nat.eq_of_beq_eq_true hcol,
    Nat.eq_of_beq_eq_true hPK, Nat.eq_of_beq_eq_true htl, fun i hi => ?_,
    Nat.eq_of_beq_eq_true hSI⟩
  · have e : (v >>> k) &&& 1 = 1 := Nat.eq_of_beq_eq_true hvk
    rw [CFSG.KC.J4Q.and_one_bit] at e
    by_contra hb
    rw [if_neg hb] at e
    exact absurd e (by decide)
  · obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 (CFSG.KS.allN_spec hall i hi)
    exact ⟨Nat.le_of_ble_eq_true h1, Eq.mp Nat.blt_eq h2⟩

theorem sep_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {zB RB SI : Nat}
    {zs : List Nat}
    (hzs : zs.length = 4) (hzB : zB < 2 ^ 3240) (hz : ∀ z ∈ zs, z < 2 ^ 3240)
    (hP : rows80K sepP.toList = true)
    (h : sepK c rm t0 t1 t2 t3 t4 t5 t6 dgK zB RB zs sepTerms sepVec sepIdx (packRowsK sepP.toList)
      sepTree SI = true) :
    sepCheckWith (Array.ofFn fun r : Fin 4 =>
      mulRows 80 (invRowsF2 80 (polarRowsZ 80 zB)) (polarRowsZ 80 (zs.getD r.val 0))) = true := by
  obtain ⟨hB, hk, hvk, hcol, hPK, htl, hall, hSI⟩ := sepK_parts h
  have hterms : ∀ w ∈ sepTerms, ∀ x ∈ w, x < 4 := by
    unfold sepTerms
    decide
  have hv : sepVec < 2 ^ 80 := by
    unfold sepVec
    decide
  unfold sepCheckWith
  exact core hK (by rw [Array.size_ofFn]) (mats_eq hK hzs hB) hterms hv hP hk hvk hcol hPK htl
    hall hSI

end CFSG.KS.SporSch.J3F.SepPf

end

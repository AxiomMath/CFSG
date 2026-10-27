module

public import Certificates.Data.Kernel.M1F2
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.Local
import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.Sporadic.HS.SmallF2Spec

public noncomputable section

namespace CFSG.KC.LocalComp.Cub

open CFSG.KC.M1F2 CFSG.KC.Loop CFSG.KLie.CT CFSG.SectionRank.Native CFSG.KC.Co1F2 CFSG.KC.F2W
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def powK (d X e : Nat) : Nat := powF d X e 16

@[expose] def getR (d : Nat) (R : List Nat) (i : Nat) : Nat := R.getD i (idF d)

@[expose] noncomputable def stepK (d : Nat) (R : List Nat) : Op → List Nat
  | .mul i j k => R.set k (mulF d (getR d R i) (getR d R j))
  | .pow e i k => R.set k (powK d (getR d R i) e)

@[expose] def expOK : Op → Bool
  | .mul _ _ _ => true
  | .pow e _ _ => decide (e < 65536)

@[expose] noncomputable def initK (d A B n : Nat) : List Nat :=
  (List.range n).map fun r => if r = 0 then A else if r = 1 then B else idF d

@[expose] noncomputable def appK (d X : Nat) : Nat → Nat → Nat
  | 0, v => v
  | n + 1, v => appK d X n (vmF d X v)

@[expose] noncomputable def appBaseK (d b : Nat) : List Nat → Nat → Nat → Nat
  | [], _, v => v
  | X :: xs, n, v => appBaseK d b xs (n / b) (appK d X (n % b) v)

@[expose] def allDistinct : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !(Nat.beq x y)) && allDistinct xs

@[expose] noncomputable def conjK (d X Y W : Nat) : Bool := Nat.beq (mulF d X Y) (mulF d W X)

@[expose] noncomputable def cubicK (d A B : Nat) (D : CubData) : Bool :=
  let R := D.prog.foldl (stepK d) (initK d A B D.nregs)
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let H := getR d R D.rh
  let one := idF d
  let Z := mulF d (mulF d (mulF d X Y) (powK d X (D.r - 1))) (powK d Y (D.r - 1))
  let u := pw2 D.t
  decide (0 < d) && decide (A < 2 ^ (d * d)) && decide (B < 2 ^ (d * d)) &&
    decide (D.t < d) && D.prog.all expOK &&
    [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ].all (decide <| · < 65536) &&
    decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && decide (D.rx < D.nregs) &&
    decide (D.ry < D.nregs) && decide (D.rh < D.nregs) && decide (0 < D.r) &&
    decide (0 < D.oh) && Nat.beq (powK d X D.r) one && Nat.beq (powK d Y D.r) one &&
    Nat.beq (powK d H D.oh) one && !(Nat.beq (vmF d Z u) u) &&
    Nat.beq (mulF d Z X) (mulF d X Z) && Nat.beq (mulF d Z Y) (mulF d Y Z) &&
    conjK d H X (mulF d (mulF d (powK d X D.a) (powK d Y D.b)) (powK d Z D.k)) &&
    conjK d H Y (mulF d (mulF d (powK d X D.c) (powK d Y D.d)) (powK d Z D.l)) &&
    conjK d H Z (powK d Z D.μ) &&
    allDistinct ((List.range (D.r ^ 3)).map fun n => appBaseK d D.r [X, Y, Z] n u)

private theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

private theorem unpackR_idF (d : Nat) : unpackR d (idF d) = idRows d := by
  unfold unpackR idRows
  congr 1
  funext i
  rw [← rowF_eq]
  have hf : ∀ j < d, pw2 j < 2 ^ d := fun j hj => by
    rw [show pw2 j = 2 ^ j from Nat.one_shiftLeft j]
    exact Nat.pow_lt_pow_right (by omega) hj
  exact rowF_orN d (f := pw2) hf i.isLt

private theorem rowsMatrix_unpackR_idF (d : Nat) :
    rowsMatrix d (unpackR d (idF d)) = 1 := by
  rw [unpackR_idF, rowsMatrix_idRows]

private theorem rowsMatrix_unpackR_mulF (d A B : Nat) :
    rowsMatrix d (unpackR d (mulF d A B)) =
      rowsMatrix d (unpackR d A) * rowsMatrix d (unpackR d B) := by
  rw [← mulRows_unpackR, rowsMatrix_mulRows]

private noncomputable def powFR (d X e N : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (idF d)
    (fun i acc => strictN (mulF d acc acc) fun sq =>
      nIf(bit e ((N - 1) - i), mulF d sq X, sq))

private theorem powF_eq_powFR (d X e nb : Nat) : powF d X e nb = powFR d X e nb nb := rfl

private theorem mod_two_pow_succ (q k : Nat) :
    q % 2 ^ (k + 1) = 2 * (q / 2 % 2 ^ k) + q % 2 := by
  conv_lhs => rw [show q = 2 * (q / 2) + q % 2 from (Nat.div_add_mod q 2).symm]
  rw [Nat.add_mod]
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ]; ring]
  rw [Nat.mul_mod_mul_left]
  have hb : q % 2 < 2 * 2 ^ k := by
    have h1 := Nat.mod_lt q (by norm_num : 0 < 2)
    have h2 := Nat.two_pow_pos k
    omega
  rw [Nat.mod_eq_of_lt hb]
  have ha : 2 * (q / 2 % 2 ^ k) < 2 * 2 ^ k := by
    have h := Nat.mod_lt (q / 2) (Nat.two_pow_pos k)
    omega
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem bit_eq_mod (e j : Nat) :
    bit e j = (e / 2 ^ j % 2 == 1) := by
  rw [bit_eq]
  have h := (Nat.testBit_div_two_pow (n := j) (x := e) (i := 0)).symm
  simpa [Nat.add_comm, beq_eq_decide] using h

private theorem powFR_succ (d X e N k : Nat) :
    powFR d X e N (k + 1) =
      (let sq := mulF d (powFR d X e N k) (powFR d X e N k)
       if bit e ((N - 1) - k) then mulF d sq X else sq) := by
  simp only [powFR, Nat.rec_add_one, strictN_eq, nIf_eq]

private theorem rowsMatrix_powFR (d X e N : Nat) :
    ∀ k, k ≤ N → rowsMatrix d (unpackR d (powFR d X e N k)) =
      rowsMatrix d (unpackR d X) ^ ((e / 2 ^ (N - k)) % 2 ^ k)
  | 0, _ => by
    simp only [powFR, Nat.rec_zero, rowsMatrix_unpackR_idF, Nat.sub_zero, pow_zero,
      Nat.mod_one, pow_zero]
  | k + 1, hk => by
    rw [powFR_succ]
    dsimp only
    have hk' : k ≤ N := by omega
    have hN : (N - 1) - k = N - (k + 1) := by omega
    have hM : (e / 2 ^ (N - k)) % 2 ^ k =
        (e / 2 ^ (N - (k + 1))) / 2 % 2 ^ k := by
      rw [show N - k = N - (k + 1) + 1 by omega, Nat.pow_succ]
      rw [← Nat.div_div_eq_div_mul]
    have ih := rowsMatrix_powFR d X e N k hk'
    rw [hM] at ih
    rw [mod_two_pow_succ (e / 2 ^ (N - (k + 1))) k]
    by_cases hb : bit e ((N - 1) - k) = true
    · have hb1 : e / 2 ^ (N - (k + 1)) % 2 = 1 := by
        have h := hb
        rw [bit_eq_mod, hN] at h
        exact Nat.eq_of_beq_eq_true h
      rw [if_pos hb, hb1]
      rw [rowsMatrix_unpackR_mulF, rowsMatrix_unpackR_mulF, ih]
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    · have hbf : bit e ((N - 1) - k) = false := by
        cases h : bit e ((N - 1) - k) <;> simp_all
      have hb0 : e / 2 ^ (N - (k + 1)) % 2 = 0 := by
        have h := hbf
        rw [bit_eq_mod, hN] at h
        have hne : e / 2 ^ (N - (k + 1)) % 2 ≠ 1 := by
          intro h1
          rw [beq_eq_decide, decide_eq_true h1] at h
          cases h
        have := Nat.mod_lt (e / 2 ^ (N - (k + 1))) (by norm_num : 0 < 2)
        omega
      rw [if_neg hb, hb0, Nat.add_zero]
      rw [rowsMatrix_unpackR_mulF, ih]
      rw [← pow_add]
      congr 1
      omega

private theorem rowsMatrix_powF {d X e nb : Nat} (he : e < 2 ^ nb) :
    rowsMatrix d (unpackR d (powF d X e nb)) = rowsMatrix d (unpackR d X) ^ e := by
  rw [powF_eq_powFR, rowsMatrix_powFR d X e nb nb (le_refl nb)]
  congr 1
  rw [Nat.sub_self, pow_zero, Nat.div_one, Nat.mod_eq_of_lt he]

private theorem rowsMatrix_ops2_pow (d : Nat) (M : Array Nat) (e : Nat) :
    rowsMatrix d ((ops2 d).pow M e) = rowsMatrix d M ^ e := by
  revert M
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro M
    unfold Ops.pow
    by_cases h0 : e = 0
    · rw [if_pos h0]
      rw [show (ops2 d).one = idRows d from rfl, rowsMatrix_idRows, h0, pow_zero]
    by_cases h1 : e = 1
    · rw [if_neg h0, if_pos h1, h1, pow_one]
    · rw [if_neg h0, if_neg h1]
      dsimp only
      have hMul : rowsMatrix d ((ops2 d).mul M M) = rowsMatrix d M * rowsMatrix d M := by
        change rowsMatrix d (mulRows d M M) = _
        rw [rowsMatrix_mulRows]
      have ihY := ih (e / 2) (by omega) ((ops2 d).mul M M)
      rw [hMul] at ihY
      have hpow : (rowsMatrix d M * rowsMatrix d M) ^ (e / 2) =
          rowsMatrix d M ^ (2 * (e / 2)) := by
        rw [← pow_two, ← pow_mul]
      have hdm := Nat.div_add_mod e 2
      by_cases ho : e % 2 = 1
      · rw [if_pos ho]
        change rowsMatrix d (mulRows d M ((ops2 d).pow ((ops2 d).mul M M) (e / 2))) = _
        rw [rowsMatrix_mulRows, ihY, hpow, ← pow_succ']
        congr 1
        omega
      · rw [if_neg ho, ihY, hpow]
        congr 1
        omega

private theorem foldl_xor_lt {d : Nat} {L : List Nat} {g : Nat → Nat} {v acc : Nat}
    (hacc : acc < 2 ^ d) (hg : ∀ j ∈ L, g j < 2 ^ d) :
    L.foldl (fun acc j => if v.testBit j then acc ^^^ g j else acc) acc < 2 ^ d := by
  induction L generalizing acc with
  | nil => exact hacc
  | cons j L ih =>
    rw [List.foldl_cons]
    have hg' : ∀ k ∈ L, g k < 2 ^ d := fun k hk => hg k (by simp [hk])
    split
    · exact ih (Nat.xor_lt_two_pow hacc (hg j (by simp))) hg'
    · exact ih hacc hg'

private theorem unpackR_lt {d M i : Nat} (hi : i < d) : (unpackR d M)[i]! < 2 ^ d := by
  unfold unpackR
  rw [getElem!_pos _ i (by simpa using hi)]
  rw [Array.getElem_ofFn]
  exact Nat.mod_lt _ (Nat.two_pow_pos d)

private theorem idRows_lt {d i : Nat} (hi : i < d) : (idRows d)[i]! < 2 ^ d := by
  rw [← unpackR_idF d]
  exact unpackR_lt hi

private theorem vecMulN_lt {d : Nat} {R : Array Nat} (hRsize : R.size = d)
    (hR : ∀ j < d, R[j]! < 2 ^ d) (v : Nat) : vecMulN d R v < 2 ^ d := by
  unfold vecMulN
  apply foldl_xor_lt (Nat.two_pow_pos d)
  intro j hj
  rw [List.mem_range] at hj
  rw [Array.getElem?_eq_getElem (by rw [hRsize]; exact hj), Option.getD_some]
  exact (by
    rw [← getElem!_pos R j (by rw [hRsize]; exact hj)]
    exact hR j hj)

private theorem mulRows_lt {d : Nat} {X Y : Array Nat} (hX : X.size = d) (hY : Y.size = d)
    (hYb : ∀ j < d, Y[j]! < 2 ^ d) :
    ∀ i < d, (mulRows d X Y)[i]! < 2 ^ d := by
  intro i hi
  rw [mulRows]
  rw [getElem!_pos (X.map (vecMulN d Y)) i (by simp [hX]; exact hi)]
  rw [Array.getElem_map]
  exact vecMulN_lt hY hYb _

private theorem ops2_pow_wf (d : Nat) : ∀ (M : Array Nat) (e : Nat),
    M.size = d → (∀ i < d, M[i]! < 2 ^ d) →
    ((ops2 d).pow M e).size = d ∧ ∀ i < d, ((ops2 d).pow M e)[i]! < 2 ^ d := by
  intro M e
  revert M
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro M hMsize hMb
    unfold Ops.pow
    by_cases h0 : e = 0
    · rw [if_pos h0]
      rw [show (ops2 d).one = idRows d from rfl]
      exact ⟨by simp [idRows], fun i hi => idRows_lt hi⟩
    by_cases h1 : e = 1
    · rw [if_neg h0, if_pos h1]
      exact ⟨hMsize, hMb⟩
    · rw [if_neg h0, if_neg h1]
      dsimp only
      have hMM : (mulRows d M M).size = d := by rw [mulRows, Array.size_map, hMsize]
      have hMMb : ∀ i < d, (mulRows d M M)[i]! < 2 ^ d :=
        mulRows_lt hMsize hMsize hMb
      obtain ⟨ihsz, ihb⟩ := ih (e / 2) (by omega) (mulRows d M M) hMM hMMb
      have hdm := Nat.div_add_mod e 2
      by_cases ho : e % 2 = 1
      · rw [if_pos ho]
        change (mulRows d M ((ops2 d).pow (mulRows d M M) (e / 2))).size = d ∧
          ∀ i < d, (mulRows d M ((ops2 d).pow (mulRows d M M) (e / 2)))[i]! < 2 ^ d
        exact ⟨by rw [mulRows, Array.size_map, hMsize], mulRows_lt hMsize ihsz ihb⟩
      · rw [if_neg ho]
        exact ⟨ihsz, ihb⟩

private theorem rowsMatrix_inj {d : Nat} {R S : Array Nat}
    (hRsize : R.size = d) (hSsize : S.size = d)
    (hRb : ∀ i < d, R[i]! < 2 ^ d) (hSb : ∀ i < d, S[i]! < 2 ^ d)
    (h : rowsMatrix d R = rowsMatrix d S) : R = S := by
  apply Array.ext
  · rw [hRsize, hSsize]
  · intro i hiR hiS
    have hi : i < d := by rw [hRsize] at hiR; exact hiR
    have hRi : R[i] < 2 ^ d := by
      rw [← getElem!_pos R i hiR]
      exact hRb i hi
    have hSi : S[i] < 2 ^ d := by
      rw [← getElem!_pos S i hiS]
      exact hSb i hi
    have hrow : toVecD d R[i] = toVecD d S[i] := by
      funext j
      have h' := congrArg (fun M => M ⟨i, hi⟩ j) h
      have hgetR : R[i]?.getD 0 = R[i] := by
        rw [Array.getElem?_eq_getElem (by rw [hRsize]; exact hi), Option.getD_some]
      have hgetS : S[i]?.getD 0 = S[i] := by
        rw [Array.getElem?_eq_getElem (by rw [hSsize]; exact hi), Option.getD_some]
      rw [rowsMatrix_apply, rowsMatrix_apply] at h'
      simpa [hgetR, hgetS] using h'
    exact toVecD_injective hRi hSi hrow

private theorem unpackR_powF16 {d X e : Nat} (he : e < 2 ^ 16) :
    unpackR d (powF d X e 16) = (ops2 d).pow (unpackR d X) e := by
  have hw := ops2_pow_wf d (unpackR d X) e (by simp [unpackR]) (fun i hi => unpackR_lt hi)
  refine rowsMatrix_inj (d := d) (R := unpackR d (powF d X e 16))
    (S := (ops2 d).pow (unpackR d X) e) ?_ ?_ ?_ ?_ ?_
  · simp [unpackR]
  · exact hw.1
  · intro i hi
    exact unpackR_lt hi
  · exact hw.2
  · rw [rowsMatrix_powF (nb := 16) he, rowsMatrix_ops2_pow]

private theorem length_stepK (d : Nat) (R : List Nat) (op : Op) :
    (stepK d R op).length = R.length := by
  cases op <;> simp [stepK, List.length_set]

private theorem length_stepK_foldl (d n : Nat) :
    ∀ (prog : List Op) (R : List Nat), R.length = n →
      (prog.foldl (stepK d) R).length = n
  | [], R, h => h
  | op :: prog, R, h =>
    length_stepK_foldl d n prog (stepK d R op) (by rw [length_stepK, h])

private theorem size_step (d : Nat) (R : Array (Array Nat)) (op : Op) :
    ((ops2 d).step R op).size = R.size := by
  cases op <;> simp [Ops.step, Array.size_set!]

private theorem getR_map {d n : Nat} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hlen : Rl.length = n) (hsize : Ra.size = n)
    (hmap : Rl.map (unpackR d) = Ra.toList) {i : Nat} (hi : i < n) :
    unpackR d (getR d Rl i) = Ra[i]! := by
  have hiL : i < Rl.length := by omega
  have hiMap : i < (Rl.map (unpackR d)).length := by simpa using hiL
  have hmap_i := congrArg (fun L => L[i]!) hmap
  rw [getElem!_pos (Rl.map (unpackR d)) i hiMap, List.getElem_map] at hmap_i
  rw [Array.getElem!_toList] at hmap_i
  rw [getR, show Rl.getD i (idF d) = Rl[i] from List.getD_eq_getElem Rl (idF d) hiL]
  exact hmap_i

private theorem stepK_map {d n : Nat} {Rl : List Nat} {Ra : Array (Array Nat)} (op : Op)
    (hlen : Rl.length = n) (hsize : Ra.size = n)
    (hmap : Rl.map (unpackR d) = Ra.toList)
    (hlt : Op.lt n op = true) (hexp : expOK op = true) :
    (stepK d Rl op).map (unpackR d) =
      ((ops2 d).step Ra op).toList := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨⟨hi, hj⟩, hk⟩ := hlt
    simp only [stepK, Ops.step, List.map_set, Array.toList_set!, hmap]
    congr 1
    change unpackR d (mulF d (getR d Rl i) (getR d Rl j)) = mulRows d Ra[i]! Ra[j]!
    rw [← mulRows_unpackR, getR_map hlen hsize hmap hi, getR_map hlen hsize hmap hj]
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hlt
    obtain ⟨hi, hk⟩ := hlt
    simp only [expOK, decide_eq_true_eq] at hexp
    have he : e < 2 ^ 16 := by simpa using hexp
    simp only [stepK, Ops.step, List.map_set, Array.toList_set!, hmap]
    congr 1
    change unpackR d (powF d (getR d Rl i) e 16) = (ops2 d).pow Ra[i]! e
    rw [← getR_map hlen hsize hmap hi, unpackR_powF16 he]

private theorem run_map {d n : Nat} {prog : List Op} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hlen : Rl.length = n) (hsize : Ra.size = n)
    (hmap : Rl.map (unpackR d) = Ra.toList)
    (hlt : prog.all (Op.lt n) = true) (hexp : prog.all expOK = true) :
    (prog.foldl (stepK d) Rl).map (unpackR d) = ((ops2 d).run prog Ra).toList := by
  induction prog generalizing Rl Ra with
  | nil => exact hmap
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hlt
    rw [List.all_cons, Bool.and_eq_true] at hexp
    have hstep := stepK_map op hlen hsize hmap hlt.1 hexp.1
    have hlen' : (stepK d Rl op).length = n := by rw [length_stepK, hlen]
    have hsize' : ((ops2 d).step Ra op).size = n := by rw [size_step, hsize]
    rw [List.foldl_cons]
    simp only [Ops.run, List.foldl_cons]
    exact ih hlen' hsize' hstep hlt.2 hexp.2

private theorem map_initK (d A B n : Nat) :
    (initK d A B n).map (unpackR d) =
      ((ops2 d).initRegs (unpackR d A) (unpackR d B) n).toList := by
  apply List.ext_getElem
  · simp [initK, Ops.initRegs, Array.toList_ofFn]
  · intro i hiL hiR
    simp only [initK, List.getElem_map, List.getElem_range, Ops.initRegs, Array.toList_ofFn,
      List.getElem_ofFn, show (ops2 d).one = idRows d from rfl]
    by_cases h0 : i = 0
    · simp [h0]
    · by_cases h1 : i = 1
      · simp [h0, h1]
      · simp [h0, h1, unpackR_idF]

private theorem appK_eq (d X : Nat) : ∀ (n v : Nat),
    (ops2 d).app (unpackR d X) n v = appK d X n v
  | 0, v => rfl
  | n + 1, v => by
    change (ops2 d).app (unpackR d X) n (vecMulN d (unpackR d X) v) =
      appK d X n (vmF d X v)
    rw [vecMulN_unpackR]
    exact appK_eq d X n (vmF d X v)

private theorem appBaseK_eq (d b : Nat) :
    ∀ (xs : List Nat) (n v : Nat),
      (ops2 d).appBase b (xs.map (unpackR d)) n v = appBaseK d b xs n v
  | [], n, v => rfl
  | X :: xs, n, v => by
    change (ops2 d).appBase b (xs.map (unpackR d)) (n / b)
      ((ops2 d).app (unpackR d X) (n % b) v) =
      appBaseK d b xs (n / b) (appK d X (n % b) v)
    rw [← appK_eq]
    exact appBaseK_eq d b xs (n / b) ((ops2 d).app (unpackR d X) (n % b) v)

private theorem appK_lt (d X n v : Nat) (hv : v < 2 ^ d) : appK d X n v < 2 ^ d := by
  induction n generalizing v with
  | zero => exact hv
  | succ n ih => exact ih (v := vmF d X v) (vmF_lt d X v)

private theorem appBaseK_lt (d b : Nat) :
    ∀ (xs : List Nat) (n v : Nat), v < 2 ^ d → appBaseK d b xs n v < 2 ^ d
  | [], n, v, hv => hv
  | X :: xs, n, v, hv =>
    appBaseK_lt d b xs (n / b) (appK d X (n % b) v) (appK_lt d X _ v hv)

private theorem vne_eq (d u w : Nat) :
    (ops2 d).vne u w = !Nat.beq (u % 2 ^ d) (w % 2 ^ d) := by
  change ((List.range d).any fun j => u.testBit j != w.testBit j) = _
  by_cases h : u % 2 ^ d = w % 2 ^ d
  · have hb : Nat.beq (u % 2 ^ d) (w % 2 ^ d) = true := by rw [Nat.beq_eq]; exact h
    rw [hb]
    apply List.any_eq_false.2
    intro j hj
    have hj' := List.mem_range.1 hj
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_mod_two_pow, hj', decide_true, Bool.true_and] at this
    simp [this]
  · have hb : Nat.beq (u % 2 ^ d) (w % 2 ^ d) = false := beq_false_of_ne h
    rw [hb]
    apply List.any_eq_true.2
    by_contra hc
    apply h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < d
    · simp only [hj, decide_true, Bool.true_and]
      by_contra hne
      exact hc ⟨j, List.mem_range.2 hj, by simp [hne]⟩
    · simp [hj]

private theorem nat_beq_false {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h e
    subst e
    rw [Nat.beq_refl] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : Nat.beq a b
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem allDistinct_iff_nodup : ∀ L : List Nat, allDistinct L = true ↔ L.Nodup
  | [] => by simp [allDistinct]
  | x :: xs => by
    change (xs.all (fun y => !(Nat.beq x y)) && allDistinct xs) = true ↔ _
    rw [Bool.and_eq_true, List.all_eq_true, allDistinct_iff_nodup xs]
    constructor
    · rintro ⟨h1, h2⟩
      refine List.nodup_cons.2 ⟨fun hx => ?_, h2⟩
      have := h1 x hx
      rw [Bool.not_eq_true', nat_beq_false] at this
      exact this rfl
    · intro h
      obtain ⟨hx, h2⟩ := List.nodup_cons.1 h
      refine ⟨fun y hy => ?_, h2⟩
      rw [Bool.not_eq_true', nat_beq_false]
      exact fun e => hx (e ▸ hy)

private theorem allDistinct_map_range {N : Nat} {f : Nat → Nat}
    (h : allDistinct ((List.range N).map f) = true) :
    ∀ i < N, ∀ j < N, i ≠ j → f i ≠ f j := by
  have hnodup : ((List.range N).map f).Nodup := (allDistinct_iff_nodup _).1 h
  have hinj := (List.nodup_map_iff_inj_on List.nodup_range).1 hnodup
  intro i hi j hj hij e
  exact hij (hinj i (List.mem_range.2 hi) j (List.mem_range.2 hj) e)

private theorem normalFormOK_of_allDistinct {d r t X Y Z : Nat} (ht : t < d)
    (h : allDistinct ((List.range (r ^ 3)).map fun n =>
      appBaseK d r [X, Y, Z] n (pw2 t)) = true) :
    (ops2 d).normalFormOK r [unpackR d X, unpackR d Y, unpackR d Z] t = true := by
  have hu : pw2 t < 2 ^ d := by
    rw [show pw2 t = 2 ^ t from Nat.one_shiftLeft t]
    exact Nat.pow_lt_pow_right (by norm_num) ht
  let vs : Array Nat := Array.ofFn (n := r ^ 3) fun n =>
    (ops2 d).appBase r [unpackR d X, unpackR d Y, unpackR d Z] n.val
      ((ops2 d).unit t)
  unfold Ops.normalFormOK
  change (ops2 d).distinctOK vs = true
  unfold Ops.distinctOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hvs : vs.size = r ^ 3 := by simp [vs]
  have hiN : i < r ^ 3 := by
    have := List.mem_range.1 hi
    rw [hvs] at this
    exact this
  have hjI : j < i := by simpa using hj
  have hjN : j < r ^ 3 := by omega
  have hpair := allDistinct_map_range h i hiN j hjN (by omega)
  have hvi : vs[i]! = appBaseK d r [X, Y, Z] i (pw2 t) := by
    dsimp only [vs]
    rw [getElem!_pos _ i (by simpa using hiN), Array.getElem_ofFn]
    exact (appBaseK_eq d r [X, Y, Z] i ((ops2 d).unit t)).trans (by
      rw [show (ops2 d).unit t = pw2 t from rfl])
  have hvj : vs[j]! = appBaseK d r [X, Y, Z] j (pw2 t) := by
    dsimp only [vs]
    rw [getElem!_pos _ j (by simpa using hjN), Array.getElem_ofFn]
    exact (appBaseK_eq d r [X, Y, Z] j ((ops2 d).unit t)).trans (by
      rw [show (ops2 d).unit t = pw2 t from rfl])
  rw [hvi, hvj, vne_eq, Nat.mod_eq_of_lt (appBaseK_lt d r [X, Y, Z] i (pw2 t) hu),
    Nat.mod_eq_of_lt (appBaseK_lt d r [X, Y, Z] j (pw2 t) hu),
    nat_beq_false.mpr hpair]
  rfl

private theorem ops2_eq_unpackR {d A B : Nat} (h : Nat.beq A B = true) :
    (ops2 d).eq (unpackR d A) (unpackR d B) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  change (unpackR d B == unpackR d B) = true
  exact beq_self_eq_true _

private theorem ops2_one_eq {d : Nat} : (ops2 d).one = unpackR d (idF d) :=
  (unpackR_idF d).symm

private theorem ops2_eq_self {d : Nat} (X : Array Nat) : (ops2 d).eq X X = true := by
  change (X == X) = true
  exact beq_self_eq_true X

private theorem vne_of_Zmove {d t Z : Nat} (ht : t < d)
    (h : (!Nat.beq (vmF d Z (pw2 t)) (pw2 t)) = true) :
    (ops2 d).vne ((ops2 d).vmul ((ops2 d).unit t) (unpackR d Z)) ((ops2 d).unit t) =
      true := by
  have hu : pw2 t < 2 ^ d := by
    rw [show pw2 t = 2 ^ t from Nat.one_shiftLeft t]
    exact Nat.pow_lt_pow_right (by norm_num) ht
  change (ops2 d).vne (vecMulN d (unpackR d Z) (1 <<< t)) (1 <<< t) = true
  rw [show (1 : Nat) <<< t = pw2 t from rfl, vecMulN_unpackR, vne_eq,
    Nat.mod_eq_of_lt (vmF_lt d Z (pw2 t)), Nat.mod_eq_of_lt hu]
  exact h

private theorem conjOK_of_conjK {d H X W : Nat} (h : conjK d H X W = true) :
    (ops2 d).conjOK (unpackR d H) (unpackR d X) (unpackR d W) = true := by
  unfold conjK at h
  unfold Ops.conjOK
  change (mulRows d (unpackR d H) (unpackR d X) ==
    mulRows d (unpackR d W) (unpackR d H)) = true
  rw [mulRows_unpackR, mulRows_unpackR, Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true _

private theorem unpackR_powK {d X e : Nat} (he : e < 2 ^ 16) :
    unpackR d (powK d X e) = (ops2 d).pow (unpackR d X) e := by
  change unpackR d (powF d X e 16) = _
  exact unpackR_powF16 he

private theorem unpackR_commM {d r X Y : Nat} (hr : r - 1 < 2 ^ 16) :
    unpackR d (mulF d (mulF d (mulF d X Y) (powK d X (r - 1)))
        (powK d Y (r - 1))) =
      (ops2 d).commM r (unpackR d X) (unpackR d Y) := by
  unfold Ops.commM
  rw [← mulRows_unpackR, ← mulRows_unpackR, ← mulRows_unpackR,
    unpackR_powK hr, unpackR_powK hr]
  rfl

private theorem unpackR_conj {d X Y Z a b k : Nat}
    (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) (hk : k < 2 ^ 16) :
    unpackR d (mulF d (mulF d (powK d X a) (powK d Y b)) (powK d Z k)) =
      (ops2 d).mul ((ops2 d).mul ((ops2 d).pow (unpackR d X) a)
          ((ops2 d).pow (unpackR d Y) b)) ((ops2 d).pow (unpackR d Z) k) := by
  rw [← mulRows_unpackR, ← mulRows_unpackR, unpackR_powK ha, unpackR_powK hb,
    unpackR_powK hk]
  rfl

private theorem size_run (d n : Nat) : ∀ (prog : List Op) (R : Array (Array Nat)),
    R.size = n → ((ops2 d).run prog R).size = n
  | [], R, h => h
  | op :: prog, R, h =>
    size_run d n prog ((ops2 d).step R op) (by rw [size_step, h])

private structure cubicKData (d A B : Nat) (D : CubData) where
  Rl : List Nat
  hRl : Rl = D.prog.foldl (stepK d) (initK d A B D.nregs)
  Xp : Nat
  hXp : Xp = getR d Rl D.rx
  Yp : Nat
  hYp : Yp = getR d Rl D.ry
  Hp : Nat
  hHp : Hp = getR d Rl D.rh
  Zp : Nat
  hZp : Zp = mulF d (mulF d (mulF d Xp Yp) (powK d Xp (D.r - 1)))
    (powK d Yp (D.r - 1))
  Wx : Nat
  hWx : Wx = mulF d (mulF d (powK d Xp D.a) (powK d Yp D.b)) (powK d Zp D.k)
  Wy : Nat
  hWy : Wy = mulF d (mulF d (powK d Xp D.c) (powK d Yp D.d)) (powK d Zp D.l)
  ht : D.t < d
  hexp : D.prog.all expOK = true
  hsmall : ([D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ].all fun x =>
    decide (x < 65536)) = true
  hnregs : 2 ≤ D.nregs
  hprog : D.prog.all (Op.lt D.nregs) = true
  hrx : D.rx < D.nregs
  hry : D.ry < D.nregs
  hrh : D.rh < D.nregs
  hr0 : 0 < D.r
  hoh0 : 0 < D.oh
  hXr : Nat.beq (powK d Xp D.r) (idF d) = true
  hYr : Nat.beq (powK d Yp D.r) (idF d) = true
  hHoh : Nat.beq (powK d Hp D.oh) (idF d) = true
  hZmove : (!Nat.beq (vmF d Zp (pw2 D.t)) (pw2 D.t)) = true
  hZX : Nat.beq (mulF d Zp Xp) (mulF d Xp Zp) = true
  hZY : Nat.beq (mulF d Zp Yp) (mulF d Yp Zp) = true
  hconjX : conjK d Hp Xp Wx = true
  hconjY : conjK d Hp Yp Wy = true
  hconjZ : conjK d Hp Zp (powK d Zp D.μ) = true
  hdist : allDistinct ((List.range (D.r ^ 3)).map fun n =>
    appBaseK d D.r [Xp, Yp, Zp] n (pw2 D.t)) = true
  eA : (ops2 d).decode D.seedA = unpackR d A
  eB : (ops2 d).decode D.seedB = unpackR d B

private theorem cubicKData_of_K {d A B : Nat} {csA csB : List Char} {D : CubData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : cubicK d A B D = true) : Nonempty (cubicKData d A B D) := by
  have h' := h
  simp only [cubicK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h'
  obtain ⟨_, _, _, ht, hexp, hsmall, hnregs, hprog, hrx, hry, hrh, hr0, hoh0,
    hXr, hYr, hHoh, hZmove, hZX, hZY, hconjX, hconjY, hconjZ, hdist⟩ := h'
  have eA : (ops2 d).decode D.seedA = unpackR d A := by
    change rowsOfPayload d D.seedA = _
    rw [hsA]
    exact bind_sound hA
  have eB : (ops2 d).decode D.seedB = unpackR d B := by
    change rowsOfPayload d D.seedB = _
    rw [hsB]
    exact bind_sound hB
  let Rl := D.prog.foldl (stepK d) (initK d A B D.nregs)
  let Xp := getR d Rl D.rx
  let Yp := getR d Rl D.ry
  let Hp := getR d Rl D.rh
  let Zp := mulF d (mulF d (mulF d Xp Yp) (powK d Xp (D.r - 1)))
    (powK d Yp (D.r - 1))
  let Wx := mulF d (mulF d (powK d Xp D.a) (powK d Yp D.b)) (powK d Zp D.k)
  let Wy := mulF d (mulF d (powK d Xp D.c) (powK d Yp D.d)) (powK d Zp D.l)
  have hF : cubicKData d A B D := {
    Rl := Rl, hRl := rfl
    Xp := Xp, hXp := rfl
    Yp := Yp
    hYp := rfl
    Hp := Hp
    hHp := rfl
    Zp := Zp
    hZp := rfl
    Wx := Wx
    hWx := rfl
    Wy := Wy
    hWy := rfl
    ht := ht
    hexp := hexp
    hsmall := hsmall
    hnregs := hnregs
    hprog := hprog
    hrx := hrx
    hry := hry
    hrh := hrh
    hr0 := hr0
    hoh0 := hoh0
    hXr := hXr
    hYr := hYr
    hHoh := hHoh
    hZmove := hZmove
    hZX := hZX
    hZY := hZY
    hconjX := hconjX
    hconjY := hconjY
    hconjZ := hconjZ
    hdist := hdist
    eA := eA
    eB := eB }
  exact ⟨hF⟩

private structure cubicRunData (d A B : Nat) (D : CubData) (F : cubicKData d A B D) where
  Ra : Array (Array Nat)
  Xa : Array Nat
  Ya : Array Nat
  Ha : Array Nat
  hRa : (ops2 d).regsOf D.seedA D.seedB D.nregs D.prog = Ra
  hRasize : Ra.size = D.nregs
  hX : unpackR d F.Xp = Xa
  hY : unpackR d F.Yp = Ya
  hH : unpackR d F.Hp = Ha
  hXa : Xa = Ra[D.rx]!
  hYa : Ya = Ra[D.ry]!
  hHa : Ha = Ra[D.rh]!

private theorem cubicRunData_of_K {d A B : Nat} {D : CubData} (F : cubicKData d A B D) :
    Nonempty (cubicRunData d A B D F) := by
  have hinitlen : (initK d A B D.nregs).length = D.nregs := by simp [initK]
  have hinitsize : ((ops2 d).initRegs (unpackR d A) (unpackR d B) D.nregs).size =
      D.nregs := by simp [Ops.initRegs]
  let Ra := (ops2 d).run D.prog
    ((ops2 d).initRegs (unpackR d A) (unpackR d B) D.nregs)
  have hRa : (ops2 d).regsOf D.seedA D.seedB D.nregs D.prog = Ra := by
    unfold Ops.regsOf
    rw [F.eA, F.eB]
  have hlenRl : F.Rl.length = D.nregs := by
    rw [F.hRl]
    exact length_stepK_foldl d D.nregs D.prog _ hinitlen
  have hregmap : F.Rl.map (unpackR d) = Ra.toList := by
    rw [F.hRl]
    simpa only [Ra] using
      run_map hinitlen hinitsize (map_initK d A B D.nregs) F.hprog F.hexp
  have hRasize : Ra.size = D.nregs := by
    dsimp only [Ra]
    exact size_run d D.nregs D.prog _ hinitsize
  have hX0 : unpackR d (getR d F.Rl D.rx) = Ra[D.rx]! :=
    getR_map hlenRl hRasize hregmap F.hrx
  have hY0 : unpackR d (getR d F.Rl D.ry) = Ra[D.ry]! :=
    getR_map hlenRl hRasize hregmap F.hry
  have hH0 : unpackR d (getR d F.Rl D.rh) = Ra[D.rh]! :=
    getR_map hlenRl hRasize hregmap F.hrh
  let Xa := Ra[D.rx]!
  let Ya := Ra[D.ry]!
  let Ha := Ra[D.rh]!
  have hRD : cubicRunData d A B D F := {
    Ra := Ra
    Xa := Xa
    Ya := Ya
    Ha := Ha
    hRa := hRa
    hRasize := hRasize
    hX := by rw [F.hXp]; exact hX0
    hY := by rw [F.hYp]; exact hY0
    hH := by rw [F.hHp]; exact hH0
    hXa := rfl
    hYa := rfl
    hHa := rfl }
  exact ⟨hRD⟩

private structure cubicPackData (d A B : Nat) (D : CubData) (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) : Prop where
  hZp : unpackR d F.Zp = (ops2 d).commM D.r RD.Xa RD.Ya
  hWx : unpackR d F.Wx =
    (ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.a) ((ops2 d).pow RD.Ya D.b))
      ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.k)
  hWy : unpackR d F.Wy =
    (ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.c) ((ops2 d).pow RD.Ya D.d))
      ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.l)
  hr16 : D.r < 2 ^ 16
  hoh16 : D.oh < 2 ^ 16
  ha16 : D.a < 2 ^ 16
  hb16 : D.b < 2 ^ 16
  hc16 : D.c < 2 ^ 16
  hd16 : D.d < 2 ^ 16
  hk16 : D.k < 2 ^ 16
  hl16 : D.l < 2 ^ 16
  hmu16 : D.μ < 2 ^ 16
  hrm1 : D.r - 1 < 2 ^ 16

private theorem cubicPackData_of_K {d A B : Nat} {D : CubData} (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) : cubicPackData d A B D F RD := by
  have hbound : ∀ x, x ∈ [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ] →
      x < 2 ^ 16 := by
    intro x hx
    have h := (List.all_eq_true.1 F.hsmall) x hx
    have hx' : x < 65536 := by simpa using h
    norm_num at hx' ⊢
    exact hx'
  have hr16 : D.r < 2 ^ 16 := hbound D.r (by simp)
  have hoh16 : D.oh < 2 ^ 16 := hbound D.oh (by simp)
  have ha16 : D.a < 2 ^ 16 := hbound D.a (by simp)
  have hb16 : D.b < 2 ^ 16 := hbound D.b (by simp)
  have hc16 : D.c < 2 ^ 16 := hbound D.c (by simp)
  have hd16 : D.d < 2 ^ 16 := hbound D.d (by simp)
  have hk16 : D.k < 2 ^ 16 := hbound D.k (by simp)
  have hl16 : D.l < 2 ^ 16 := hbound D.l (by simp)
  have hmu16 : D.μ < 2 ^ 16 := hbound D.μ (by simp)
  have hrm1 : D.r - 1 < 2 ^ 16 := by omega
  have hZp : unpackR d F.Zp = (ops2 d).commM D.r RD.Xa RD.Ya := by
    rw [F.hZp, unpackR_commM hrm1, RD.hX, RD.hY]
  have hWx : unpackR d F.Wx =
      (ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.a) ((ops2 d).pow RD.Ya D.b))
        ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.k) := by
    rw [F.hWx, unpackR_conj ha16 hb16 hk16, RD.hX, RD.hY, hZp]
  have hWy : unpackR d F.Wy =
      (ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.c) ((ops2 d).pow RD.Ya D.d))
        ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.l) := by
    rw [F.hWy, unpackR_conj hc16 hd16 hl16, RD.hX, RD.hY, hZp]
  exact {
    hZp := hZp
    hWx := hWx
    hWy := hWy
    hr16 := hr16
    hoh16 := hoh16
    ha16 := ha16
    hb16 := hb16
    hc16 := hc16
    hd16 := hd16
    hk16 := hk16
    hl16 := hl16
    hmu16 := hmu16
    hrm1 := hrm1 }

private structure cubicMoveData (d A B : Nat) (D : CubData) (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) : Prop where
  hXpow : (ops2 d).pow RD.Xa D.r = (ops2 d).one
  hYpow : (ops2 d).pow RD.Ya D.r = (ops2 d).one
  hHpow : (ops2 d).pow RD.Ha D.oh = (ops2 d).one
  hZmoveA : (ops2 d).vne
    ((ops2 d).vmul ((ops2 d).unit D.t) ((ops2 d).commM D.r RD.Xa RD.Ya))
    ((ops2 d).unit D.t) = true
  hZXA : (ops2 d).eq ((ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Xa)
    ((ops2 d).mul RD.Xa ((ops2 d).commM D.r RD.Xa RD.Ya)) = true
  hZYA : (ops2 d).eq ((ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Ya)
    ((ops2 d).mul RD.Ya ((ops2 d).commM D.r RD.Xa RD.Ya)) = true

private theorem cubicMoveData_of_K {d A B : Nat} {D : CubData} (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) (PD : cubicPackData d A B D F RD) :
    cubicMoveData d A B D F RD := by
  have hXpow : (ops2 d).pow RD.Xa D.r = (ops2 d).one := by
    rw [← RD.hX, ← unpackR_powK PD.hr16, Nat.eq_of_beq_eq_true F.hXr]
    exact (ops2_one_eq).symm
  have hYpow : (ops2 d).pow RD.Ya D.r = (ops2 d).one := by
    rw [← RD.hY, ← unpackR_powK PD.hr16, Nat.eq_of_beq_eq_true F.hYr]
    exact (ops2_one_eq).symm
  have hHpow : (ops2 d).pow RD.Ha D.oh = (ops2 d).one := by
    rw [← RD.hH, ← unpackR_powK PD.hoh16, Nat.eq_of_beq_eq_true F.hHoh]
    exact (ops2_one_eq).symm
  have hZmoveA : (ops2 d).vne
      ((ops2 d).vmul ((ops2 d).unit D.t) ((ops2 d).commM D.r RD.Xa RD.Ya))
      ((ops2 d).unit D.t) = true := by
    have h := vne_of_Zmove (d := d) (t := D.t) (Z := F.Zp) F.ht F.hZmove
    rwa [PD.hZp] at h
  have hZXA : (ops2 d).eq ((ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Xa)
      ((ops2 d).mul RD.Xa ((ops2 d).commM D.r RD.Xa RD.Ya)) = true := by
    have h := ops2_eq_unpackR (d := d) F.hZX
    rw [show (ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Xa =
        unpackR d (mulF d F.Zp F.Xp) from by
      rw [← PD.hZp, ← RD.hX]
      exact mulRows_unpackR d F.Zp F.Xp,
      show (ops2 d).mul RD.Xa ((ops2 d).commM D.r RD.Xa RD.Ya) =
        unpackR d (mulF d F.Xp F.Zp) from by
      rw [← PD.hZp, ← RD.hX]
      exact mulRows_unpackR d F.Xp F.Zp]
    exact h
  have hZYA : (ops2 d).eq ((ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Ya)
      ((ops2 d).mul RD.Ya ((ops2 d).commM D.r RD.Xa RD.Ya)) = true := by
    have h := ops2_eq_unpackR (d := d) F.hZY
    rw [show (ops2 d).mul ((ops2 d).commM D.r RD.Xa RD.Ya) RD.Ya =
        unpackR d (mulF d F.Zp F.Yp) from by
      rw [← PD.hZp, ← RD.hY]
      exact mulRows_unpackR d F.Zp F.Yp,
      show (ops2 d).mul RD.Ya ((ops2 d).commM D.r RD.Xa RD.Ya) =
        unpackR d (mulF d F.Yp F.Zp) from by
      rw [← PD.hZp, ← RD.hY]
      exact mulRows_unpackR d F.Yp F.Zp]
    exact h
  exact {
    hXpow := hXpow
    hYpow := hYpow
    hHpow := hHpow
    hZmoveA := hZmoveA
    hZXA := hZXA
    hZYA := hZYA }

private structure cubicConjData (d A B : Nat) (D : CubData) (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) : Prop where
  hconjXA : (ops2 d).conjOK RD.Ha RD.Xa
    ((ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.a) ((ops2 d).pow RD.Ya D.b))
      ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.k)) = true
  hconjYA : (ops2 d).conjOK RD.Ha RD.Ya
    ((ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.c) ((ops2 d).pow RD.Ya D.d))
      ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.l)) = true
  hconjZA : (ops2 d).conjOK RD.Ha ((ops2 d).commM D.r RD.Xa RD.Ya)
    ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.μ) = true
  hdistA : (ops2 d).normalFormOK D.r [RD.Xa, RD.Ya, (ops2 d).commM D.r RD.Xa RD.Ya] D.t =
    true

private theorem cubicConjData_of_K {d A B : Nat} {D : CubData} (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) (PD : cubicPackData d A B D F RD) :
    cubicConjData d A B D F RD := by
  have hconjXA : (ops2 d).conjOK RD.Ha RD.Xa
      ((ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.a) ((ops2 d).pow RD.Ya D.b))
        ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.k)) = true := by
    have h := conjOK_of_conjK F.hconjX
    simp only [PD.hWx, RD.hH, RD.hX, RD.hY, PD.hZp] at h
    exact h
  have hconjYA : (ops2 d).conjOK RD.Ha RD.Ya
      ((ops2 d).mul ((ops2 d).mul ((ops2 d).pow RD.Xa D.c) ((ops2 d).pow RD.Ya D.d))
        ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.l)) = true := by
    have h := conjOK_of_conjK F.hconjY
    simp only [PD.hWy, RD.hH, RD.hX, RD.hY, PD.hZp] at h
    exact h
  have hconjZA : (ops2 d).conjOK RD.Ha ((ops2 d).commM D.r RD.Xa RD.Ya)
      ((ops2 d).pow ((ops2 d).commM D.r RD.Xa RD.Ya) D.μ) = true := by
    have h := conjOK_of_conjK F.hconjZ
    simp only [unpackR_powK PD.hmu16, RD.hH, PD.hZp] at h
    exact h
  have hdistA : (ops2 d).normalFormOK D.r
      [RD.Xa, RD.Ya, (ops2 d).commM D.r RD.Xa RD.Ya] D.t = true := by
    have h := normalFormOK_of_allDistinct F.ht F.hdist
    rw [RD.hX, RD.hY, PD.hZp] at h
    exact h
  exact {
    hconjXA := hconjXA
    hconjYA := hconjYA
    hconjZA := hconjZA
    hdistA := hdistA }

private theorem cubicCheck_assembly {d A B : Nat} {D : CubData} (F : cubicKData d A B D)
    (RD : cubicRunData d A B D F) (MD : cubicMoveData d A B D F RD)
    (CD : cubicConjData d A B D F RD) : (ops2 d).cubicCheck D = true := by
  unfold Ops.cubicCheck
  rw [RD.hRa]
  dsimp only
  rw [← RD.hXa, ← RD.hYa, ← RD.hHa]
  simp only [MD.hXpow, MD.hYpow, MD.hHpow, MD.hZmoveA, MD.hZXA, MD.hZYA,
    CD.hconjXA, CD.hconjYA, CD.hconjZA, CD.hdistA,
    F.hnregs, F.hprog, F.hrx, F.hry, F.hrh, F.hr0, F.hoh0]
  simp only [decide_true, ops2_eq_self, Bool.true_and, Bool.and_true]

theorem cubicCheck_of_K {d A B : Nat} {csA csB : List Char} {D : CubData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : cubicK d A B D = true) : (ops2 d).cubicCheck D = true := by
  obtain ⟨F⟩ := cubicKData_of_K hA hB hsA hsB h
  obtain ⟨RD⟩ := cubicRunData_of_K F
  let PD := cubicPackData_of_K F RD
  exact cubicCheck_assembly F RD (cubicMoveData_of_K F RD PD) (cubicConjData_of_K F RD PD)

end CFSG.KC.LocalComp.Cub

end

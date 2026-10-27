module

public import Certificates.Data.Kernel.SporSch.J4SBig
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.Schreier.J4SNative

public section

namespace CFSG.KS.SporSch.J4B

open CFSG.KC.J4Q CFSG.KC.Loop CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CFSG.SectionRank.Native

@[expose] def encN (X : Array Nat) : Nat :=
  (List.range 112).foldr (fun i acc => Nat.lor (Nat.shiftLeft (X.getD i 0) (128 * i)) acc) 0

@[expose] def WfN (X : Array Nat) : Prop := X.size = 112 ∧ ∀ i < 112, X[i]! < 2 ^ 112

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

open CFSG.Sporadic.J4.Native (V2)

private theorem get!_eq (X : Array Nat) (i : Nat) : X[i]! = X[i]?.getD 0 := by
  by_cases h : i < X.size
  · rw [getElem!_pos X i h, getElem?_pos X i h, Option.getD_some]
  · rw [getElem!_neg X i h, getElem?_neg X i h, Option.getD_none]
    rfl

private theorem row_lt {X : Array Nat} (hX : WfN X) (i : Nat) : X[i]?.getD 0 < 2 ^ 112 := by
  by_cases h : i < 112
  · rw [← get!_eq]
    exact hX.2 i h
  · rw [getElem?_neg X i (by rw [hX.1]; exact h), Option.getD_none]
    exact Nat.two_pow_pos _

private theorem foldl_xor (h : Nat → Nat) : ∀ (n acc : Nat),
    (List.range n).foldl (fun acc j => acc ^^^ h j) acc = acc ^^^ xsum h n
  | 0, acc => (Nat.xor_zero acc).symm
  | n + 1, acc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldl_xor h n acc,
      xsum_succ, Nat.xor_assoc]

private theorem ite_xor (b : Bool) (acc r : Nat) :
    (if b = true then acc ^^^ r else acc) = acc ^^^ (if b = true then r else 0) := by
  cases b <;> simp

private theorem xsum_xor (f g : Nat → Nat) : ∀ n,
    xsum (fun k => f k ^^^ g k) n = xsum f n ^^^ xsum g n
  | 0 => (Nat.xor_zero 0).symm
  | n + 1 => by
    rw [xsum_succ, xsum_succ, xsum_succ, xsum_xor f g n]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases (xsum f n).testBit i <;> cases (xsum g n).testBit i <;> cases (f n).testBit i <;>
      cases (g n).testBit i <;> rfl

private theorem xsum_lt {f : Nat → Nat} {m : Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ m) →
    xsum f n < 2 ^ m
  | 0, _ => Nat.two_pow_pos m
  | n + 1, h => by
    rw [xsum_succ]
    exact Nat.xor_lt_two_pow (xsum_lt fun k hk => h k (by omega)) (h n (by omega))

private theorem xsum_blocks4 (f : Nat → Nat) : ∀ n,
    xsum f (4 * n) = xsum (fun q => xsum (fun i => f (4 * q + i)) 4) n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ, xsum_add, xsum_blocks4 f n]
    rfl

private noncomputable def vmN (R : Nat → Nat) (v : Nat) : Nat :=
  xsum (fun j => if v.testBit j then R j else 0) 112

private theorem vecMulN_eq (d : Nat) (R : Array Nat) (v : Nat) :
    vecMulN d R v = xsum (fun j => if v.testBit j then R[j]?.getD 0 else 0) d := by
  unfold vecMulN
  have e : (fun acc j => if v.testBit j = true then acc ^^^ R[j]?.getD 0 else acc) =
      (fun acc j => acc ^^^ (if v.testBit j = true then R[j]?.getD 0 else 0)) := by
    funext acc j
    exact ite_xor _ _ _
  rw [e, foldl_xor, Nat.zero_xor]

private theorem vmN_xor (R : Nat → Nat) (a b : Nat) : vmN R (a ^^^ b) = vmN R a ^^^ vmN R b := by
  unfold vmN
  rw [← xsum_xor]
  apply xsum_congr
  intro k _
  rw [Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> simp

private theorem vmN_zero (R : Nat → Nat) : vmN R 0 = 0 :=
  xsum_zero fun k _ => by simp

private theorem vmN_xsum (R : Nat → Nat) (g : Nat → Nat) : ∀ n,
    vmN R (xsum g n) = xsum (fun k => vmN R (g k)) n
  | 0 => vmN_zero R
  | n + 1 => by rw [xsum_succ, xsum_succ, vmN_xor, vmN_xsum R g n]

private theorem vmN_lt {R : Nat → Nat} (hR : ∀ j < 112, R j < 2 ^ 112) (v : Nat) :
    vmN R v < 2 ^ 112 :=
  xsum_lt fun k hk => by
    split
    · exact hR k hk
    · exact Nat.two_pow_pos _

private theorem xsum_pow (v : Nat) : ∀ n, xsum (fun j => if v.testBit j then 2 ^ j else 0) n = v % 2 ^ n
  | 0 => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1 => by
    rw [xsum_succ, xsum_pow v n]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases e : i = n
    · subst e
      cases v.testBit i <;> simp [Nat.testBit_two_pow_self]
    · have h1 : (i < n + 1) ↔ i < n := by omega
      cases v.testBit n <;> simp [h1, Ne.symm e]

private theorem mapRow {X : Array Nat} (hX : WfN X) (i : Nat) :
    v2N ((X.map ofN)[i]?.getD V2.zero) = X[i]?.getD 0 := by
  have hl := row_lt hX i
  rw [Array.getElem?_map]
  cases h : X[i]? with
  | none => rfl
  | some x =>
    rw [h, Option.getD_some] at hl
    rw [Option.map_some, Option.getD_some, Option.getD_some]
    exact ofN_eq hl

private theorem wfV {X : Array Nat} (hX : WfN X) : WfA (X.map ofN) := by
  refine ⟨by rw [Array.size_map, hX.1], Array.all_eq_true.mpr fun i hi => ?_⟩
  rw [Array.getElem_map]
  have hi' : i < X.size := by simpa using hi
  have := row_lt hX i
  rw [getElem?_pos X i hi', Option.getD_some] at this
  exact wf_ofN this

private theorem encN_eq {X : Array Nat} (hX : WfN X) : encN X = encR (X.map ofN) := by
  unfold encN encR
  congr 1
  funext i acc
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, mapRow hX]

private theorem encR_congr {A B : Array V2}
    (h : ∀ i < 112, v2N (A[i]?.getD V2.zero) = v2N (B[i]?.getD V2.zero)) : encR A = encR B := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encR_bit, encR_bit]
  by_cases hp : p / 128 < 112
  · rw [h _ hp]
  · simp [hp]

private theorem wfAll {X : Array V2} (hX : WfA X) : ∀ i (h : i < X.size), X[i].wf = true :=
  Array.all_eq_true.mp hX.2

private theorem byte_eq (x l : Nat) {b : Nat} (hb : b < 4) :
    (((x >>> (32 * l)) % 4294967296) >>> (8 * b)) % 256 = (x >>> (8 * (4 * l + b))) % 256 := by
  have e1 : (4294967296 : Nat) = 2 ^ 32 := rfl
  have e2 : (256 : Nat) = 2 ^ 8 := rfl
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have h1 : 8 * b + i < 32 := by omega
    have h2 : 32 * l + (8 * b + i) = 8 * (4 * l + b) + i := by omega
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, h2, decide_eq_true hi,
      decide_eq_true h1, Bool.true_and]
  · simp only [Nat.testBit_mod_two_pow, decide_eq_false hi, Bool.false_and]

private theorem foldl_step {F : Nat → Nat → Nat} {G : Nat → Nat} : ∀ (n a : Nat),
    (∀ acc l, l < n → F acc l = acc ^^^ G l) → (List.range n).foldl F a = a ^^^ xsum G n
  | 0, a, _ => (Nat.xor_zero a).symm
  | n + 1, a, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_step n a (fun acc l hl => h acc l (by omega)), h _ n (by omega), xsum_succ, Nat.xor_assoc]

private theorem frApply_eq (nw : Nat) (T : Array Nat) (x : Nat) :
    frApply nw T x = xsum (fun q => T[256 * q + (x >>> (8 * q)) % 256]?.getD 0) (4 * nw) := by
  unfold frApply
  refine (foldl_step (G := fun l =>
    xsum (fun b => T[256 * (4 * l + b) + (x >>> (8 * (4 * l + b))) % 256]?.getD 0) 4) nw 0
    ?_).trans ?_
  · intro acc l _
    dsimp only
    refine (foldl_step (G := fun b => T[256 * (4 * l + b) + (x >>> (8 * (4 * l + b))) % 256]?.getD 0)
      4 acc ?_).trans rfl
    intro acc' b hb
    rw [byte_eq x l hb]
  · rw [Nat.zero_xor]
    exact (xsum_blocks4 (fun q => T[256 * q + (x >>> (8 * q)) % 256]?.getD 0) nw).symm

private theorem frEntry_eq (Y : Array Nat) (k c : Nat) :
    frEntry Y k c = xsum (fun i => if c.testBit i then Y[8 * k + i]?.getD 0 else 0) 8 := by
  unfold frEntry
  have e : (fun acc i => if c.testBit i = true then acc ^^^ Y[8 * k + i]?.getD 0 else acc) =
      (fun acc i => acc ^^^ (if c.testBit i = true then Y[8 * k + i]?.getD 0 else 0)) := by
    funext acc i
    exact ite_xor _ _ _
  rw [e, foldl_xor, Nat.zero_xor]

private theorem frTable_get (nb : Nat) (Y : Array Nat) {q r : Nat} (hq : q < nb) (hr : r < 256) :
    (frTable nb Y)[256 * q + r]?.getD 0 = frEntry Y q r := by
  have hlt : 256 * q + r < nb * 256 := by omega
  have e1 : (256 * q + r) / 256 = q := by omega
  have e2 : (256 * q + r) % 256 = r := by omega
  simp [frTable, hlt, e1, e2]

private theorem fr_nat {Y : Array Nat} (hY : WfN Y) (x : Nat) :
    frApply 4 (frTable 16 Y) x = vecMulN 112 Y x := by
  rw [frApply_eq, vecMulN_eq]
  have h1 : xsum (fun q => (frTable 16 Y)[256 * q + (x >>> (8 * q)) % 256]?.getD 0) (4 * 4) =
      xsum (fun q => xsum (fun i => if x.testBit (8 * q + i) then Y[8 * q + i]?.getD 0 else 0) 8)
        16 := by
    apply xsum_congr
    intro q hq
    rw [frTable_get 16 Y hq (Nat.mod_lt _ (by omega)), frEntry_eq]
    apply xsum_congr
    intro i hi
    have e2 : (256 : Nat) = 2 ^ 8 := rfl
    rw [e2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hi]
  have h2 := xsum_blocks (fun j => if x.testBit j then Y[j]?.getD 0 else 0) 16
  rw [h1, ← h2]
  have e : 8 * 16 = 112 + 16 := rfl
  rw [e, xsum_add]
  have h3 : xsum (fun i => if x.testBit (112 + i) then Y[112 + i]?.getD 0 else 0) 16 = 0 :=
    xsum_zero fun i _ => by
      rw [getElem?_neg Y (112 + i) (by rw [hY.1]; omega)]
      simp
  rw [h3, Nat.xor_zero]

private theorem mul_eq {X Y : Array Nat} (hY : WfN Y) : O.mul X Y = mulRows 112 X Y := by
  change X.map (frApply 4 (frTable 16 Y)) = X.map (vecMulN 112 Y)
  congr 1
  funext x
  exact fr_nat hY x

private theorem mulRows_row {X Y : Array Nat} (hX : WfN X) {i : Nat} (hi : i < 112) :
    (mulRows 112 X Y)[i]?.getD 0 = vecMulN 112 Y (X[i]?.getD 0) := by
  have hs : i < X.size := by rw [hX.1]; exact hi
  simp [mulRows, hs]

private theorem vecMulN_lt {Y : Array Nat} (hY : WfN Y) (v : Nat) : vecMulN 112 Y v < 2 ^ 112 := by
  rw [vecMulN_eq]
  exact vmN_lt (fun j _ => row_lt hY j) v

private theorem wf_mulRows {X Y : Array Nat} (hX : WfN X) (hY : WfN Y) : WfN (mulRows 112 X Y) := by
  refine ⟨by simp [mulRows, hX.1], fun i hi => ?_⟩
  rw [get!_eq, mulRows_row hX hi]
  exact vecMulN_lt hY _

private theorem vec_enc' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : WfN X)
    (v : Nat) : vecMulN 112 X v = vecJ rm v (encN X) := by
  obtain ⟨-, hrm⟩ := consts_c hK
  subst hrm
  rw [vecJ_eq, vecMulN_eq, encN_eq hX]
  apply xsum_congr
  intro k hk
  rw [and_one_bit, rowJ_eq (wfAll (wfV hX)) hk, mapRow hX]
  split <;> simp

private theorem mulRows_enc' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array Nat}
    (hX : WfN X) (hY : WfN Y) :
    WfN (mulRows 112 X Y) ∧ encN (mulRows 112 X Y) = mulJ c rm (encN X) (encN Y) := by
  have hW := wf_mulRows hX hY
  refine ⟨hW, ?_⟩
  rw [encN_eq hW, encN_eq hX, encN_eq hY, ← enc_mulRows hK (wfV hX) (wfV hY)]
  apply encR_congr
  intro i hi
  rw [mapRow hW, mulRows_row hX hi]
  have hs : i < X.size := by rw [hX.1]; exact hi
  have hm : (CFSG.Sporadic.J4.Native.mulRows (X.map ofN) (Y.map ofN))[i]?.getD V2.zero =
      CFSG.Sporadic.J4.Native.frApply (CFSG.Sporadic.J4.Native.frTable (Y.map ofN))
        (ofN (X[i]?.getD 0)) := by
    simp [CFSG.Sporadic.J4.Native.mulRows, hs]
  rw [hm, v2N_frApply hK (wfV hY) (wf_ofN (row_lt hX i)), ofN_eq (row_lt hX i), ← encN_eq hY,
    ← vec_enc' hK hY]

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem blt_lt {x k : Nat} (h : Nat.blt x (Nat.shiftLeft 1 k) = true) : x < 2 ^ k := by
  have hlt : x < 1 <<< k := Eq.mp Nat.blt_eq h
  rwa [Nat.one_shiftLeft] at hlt

private def pk : List Nat → Nat → Nat
  | [], _ => 0
  | x :: l, r => (x <<< (128 * r)) ||| pk l (r + 1)

private theorem pack_run (P : Nat) : ∀ (l : List Nat) (r acc : Nat),
    List.rec (motive := fun _ => Nat → Nat → Bool)
      (fun r acc => andB (Nat.beq r (nat_lit 112)) (Nat.beq acc P))
      (fun x _ ih r acc => andB (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 112)))
        (strictB (Nat.lor acc (Nat.shiftLeft x (Nat.mul (nat_lit 128) r))) fun a => ih (Nat.succ r) a))
      l r acc = true →
    (∀ x ∈ l, x < 2 ^ 112) ∧ r + l.length = 112 ∧ P = acc ||| pk l r
  | [], r, acc, h => by
    obtain ⟨h1, h2⟩ := andB_true' h
    refine ⟨fun x hx => absurd hx List.not_mem_nil, ?_, ?_⟩
    · rw [List.length_nil, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h1
    · rw [← Nat.eq_of_beq_eq_true h2]
      exact (Nat.or_zero acc).symm
  | x :: l, r, acc, h => by
    obtain ⟨h1, h2⟩ := andB_true' h
    rw [strictB_eq] at h2
    obtain ⟨ih1, ih2, ih3⟩ := pack_run P l _ _ h2
    have hx : x < 2 ^ 112 := blt_lt h1
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact hx
      · exact ih1 y hy'
    · rw [List.length_cons]
      omega
    · rw [ih3]
      change (acc ||| x <<< (128 * r)) ||| pk l (r + 1) = acc ||| (x <<< (128 * r) ||| pk l (r + 1))
      exact Nat.or_assoc _ _ _

private theorem pk_eq (L : List Nat) : ∀ n r, r + n = L.length →
    (List.range' r n).foldr (fun i acc => Nat.lor (Nat.shiftLeft (L.getD i 0) (128 * i)) acc) 0 =
      pk (L.drop r) r
  | 0, r, h => by
    rw [List.drop_eq_nil_of_le (by omega : L.length ≤ r)]
    rfl
  | n + 1, r, h => by
    have hr : r < L.length := by omega
    rw [List.range'_succ, List.foldr_cons, pk_eq L n (r + 1) (by omega), List.drop_eq_getElem_cons hr,
      List.getD_eq_getElem _ _ hr]
    rfl

private theorem decRun_cons (M : Nat) (ch : Char) (cs : List Char) (ph i j acc : Nat) :
    decRun M (ch :: cs) ph i j acc =
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (decRun M cs 0 i j acc) (decRun M cs 1 i j acc)
          (Nat.beq ch.toNat 10))
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (decRun M cs 1 i (j + 1) (acc + (ent2 ch.toNat <<< j)))
              (andB (Nat.beq (row128 M i) (acc + (ent2 ch.toNat <<< j)))
                (decRun M cs 1 (i + 1) 0 0))
              (Nat.beq (j + 1) 112))
            (decRun M cs 1 i j acc) (Nat.ble 112 i))
          (decRun M cs 1 i j acc) (isWs ch.toNat))
        (Nat.beq ph 1) := by
  unfold decRun
  simp only [strictB_eq]
  try rfl

private theorem row128_eq (M r : Nat) : row128 M r = (M >>> (128 * r)) % 2 ^ 128 := by
  unfold row128
  change (M >>> (128 * r)) &&& (2 ^ 128 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private noncomputable def dg (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

private noncomputable def ents (B : List Char) : List Nat :=
  (B.filter fun c => !CFSG.Sporadic.Th.Native.wsChar c).map dg

private noncomputable def gE (E : List Nat) (i j : Nat) : Bool := (E[i * 112 + j]?.getD 0) % 2 == 1

private theorem char_beq (c d : Char) : (c == d) = (c.toNat == d.toNat) := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact Char.ext (UInt32.toNat_inj.mp h)

private theorem char_le (c d : Char) : (c ≤ d) ↔ c.toNat ≤ d.toNat := UInt32.le_iff_toNat_le

private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem nbeq (x k : Nat) : Nat.beq x k = (x == k) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq])

private theorem isWs_eq (c : Char) : isWs c.toNat = CFSG.Sporadic.Th.Native.wsChar c := by
  unfold isWs CFSG.Sporadic.Th.Native.wsChar
  rw [char_beq, char_beq, char_beq, char_beq]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  simp only [orB_eq, nbeq, Bool.or_assoc]

private theorem ent2_eq (c : Char) : ent2 c.toNat = dg c % 2 := by
  unfold ent2 dg
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  rw [e0, andB_eq]
  have hd : ('0' ≤ c && c ≤ '9') = (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq, char_le, e0, e9]
  rw [hd]
  cases Nat.ble 48 c.toNat <;> cases Nat.ble c.toNat 57 <;> simp [Nat.and_one_is_mod]

private theorem ofBits_succ (m : Nat) (f : Nat → Bool) :
    ofBits (m + 1) f = ofBits m f ||| (if f m then 1 <<< m else 0) := by
  unfold ofBits
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split <;> simp

private theorem ofBits_congr {f f' : Nat → Bool} : ∀ m, (∀ j < m, f j = f' j) →
    ofBits m f = ofBits m f'
  | 0, _ => rfl
  | m + 1, h => by
    rw [ofBits_succ, ofBits_succ, ofBits_congr m (fun j hj => h j (by omega)), h m (by omega)]

private theorem ofBits_lt (f : Nat → Bool) : ∀ m, ofBits m f < 2 ^ m
  | 0 => by
    unfold ofBits
    simp
  | m + 1 => by
    rw [ofBits_succ]
    have h1 : ofBits m f < 2 ^ (m + 1) :=
      Nat.lt_of_lt_of_le (ofBits_lt f m) (Nat.pow_le_pow_right (by omega) (by omega))
    split
    · rw [Nat.one_shiftLeft]
      exact Nat.or_lt_two_pow h1 (Nat.pow_lt_pow_right (by omega) (by omega))
    · rw [Nat.or_zero]
      exact h1

private theorem ofBits_tail {f : Nat → Bool} {j : Nat} : ∀ d,
    (∀ j', j ≤ j' → j' < j + d → f j' = false) → ofBits (j + d) f = ofBits j f
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, ofBits_succ, ofBits_tail d (fun j' h1 h2 => h j' h1 (by omega)),
      h (j + d) (by omega) (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero]

private theorem gE_past {E : List Nat} {i j : Nat} (h : E.length ≤ i * 112 + j) : gE E i j = false := by
  unfold gE
  rw [List.getElem?_eq_none h]
  rfl

private theorem getD_append_left {pre X : List Nat} {n : Nat} (h : n < pre.length) :
    (pre ++ X)[n]?.getD 0 = pre[n]?.getD 0 := by
  rw [List.getElem?_append_left h]

private theorem bit_shl (x m : Nat) : (x % 2) <<< m = if (x % 2 == 1) then 1 <<< m else 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h]
  · simp
  · rfl

private theorem dec_body (M : Nat) : ∀ (B : List Char) (i j acc : Nat) (pre : List Nat),
    (i < 112 → pre.length = 112 * i + j ∧ j < 112 ∧ acc = ofBits j (gE pre i)) →
    (112 ≤ i → i = 112 ∧ acc = 0) →
    decRun M B 1 i j acc = true →
    M >>> (128 * 112) = 0 ∧ ∀ r < 112, i ≤ r → row128 M r = ofBits 112 (gE (pre ++ ents B) r)
  | [], i, j, acc, pre, h1, h2, h => by
    have hM : M >>> (128 * i) = acc := Nat.eq_of_beq_eq_true h
    have he : pre ++ ents [] = pre := by simp [ents]
    rw [he]
    by_cases hi : i < 112
    · obtain ⟨hl, hj, hacc⟩ := h1 hi
      have hlt : acc < 2 ^ 112 := by
        rw [hacc]
        exact Nat.lt_of_lt_of_le (ofBits_lt _ j) (Nat.pow_le_pow_right (by omega) (by omega))
      have hshift : ∀ d, 0 < d → acc >>> (128 * d) = 0 := fun d hd =>
        Nat.shiftRight_eq_zero _ _ (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
      have hMr : ∀ r, i ≤ r → M >>> (128 * r) = acc >>> (128 * (r - i)) := fun r hr => by
        rw [← hM, ← Nat.shiftRight_add]
        congr 1
        rw [← Nat.mul_add]
        congr 1
        omega
      refine ⟨by rw [hMr 112 (by omega), hshift _ (by omega)], fun r hr1 hr2 => ?_⟩
      rw [row128_eq, hMr r hr2]
      by_cases hri : r = i
      · subst hri
        rw [Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))),
          hacc]
        have e : 112 = j + (112 - j) := by omega
        rw [e, ofBits_tail (112 - j) fun j' h3 _ => gE_past (by rw [hl]; omega)]
      · rw [hshift _ (by omega), Nat.zero_mod]
        have e : 112 = 0 + 112 := rfl
        rw [e, ofBits_tail 112 fun j' _ _ => gE_past (by rw [hl]; omega)]
        rfl
    · obtain ⟨hi', hacc⟩ := h2 (by omega)
      subst hi' hacc
      exact ⟨hM, fun r hr1 hr2 => absurd hr2 (by omega)⟩
  | ch :: B, i, j, acc, pre, h1, h2, h => by
    rw [decRun_cons] at h
    have e1 : Nat.beq 1 1 = true := rfl
    rw [e1] at h
    dsimp only at h
    by_cases hws : CFSG.Sporadic.Th.Native.wsChar ch = true
    · rw [isWs_eq, hws] at h
      dsimp only at h
      have he : ents (ch :: B) = ents B := by
        simp [ents, hws]
      rw [he]
      exact dec_body M B i j acc pre h1 h2 h
    · have hws' : CFSG.Sporadic.Th.Native.wsChar ch = false := by simpa using hws
      rw [isWs_eq, hws'] at h
      dsimp only at h
      have he : ents (ch :: B) = dg ch :: ents B := by
        simp [ents, hws']
      have ha : pre ++ dg ch :: ents B = (pre ++ [dg ch]) ++ ents B := by simp
      rw [he, ha]
      cases hb : Nat.ble 112 i <;> rw [hb] at h <;> dsimp only at h
      · have hi : i < 112 := by
          apply Nat.lt_of_not_le
          intro h'
          rw [Nat.ble_eq_true_of_le h'] at hb
          exact Bool.noConfusion hb
        obtain ⟨hl, hj, hacc⟩ := h1 hi
        have hl' : (pre ++ [dg ch]).length = 112 * i + (j + 1) := by simp [hl]; omega
        have hr : acc + (ent2 ch.toNat <<< j) = ofBits (j + 1) (gE (pre ++ [dg ch]) i) := by
          rw [hacc, ent2_eq, ofBits_succ]
          have e1 : ∀ j' < j, gE pre i j' = gE (pre ++ [dg ch]) i j' := by
            intro j' hj'
            unfold gE
            rw [getD_append_left (by rw [hl]; omega)]
          rw [ofBits_congr _ e1]
          have e2 : gE (pre ++ [dg ch]) i j = (dg ch % 2 == 1) := by
            unfold gE
            have : i * 112 + j = pre.length := by rw [hl]; omega
            rw [this, List.getElem?_concat_length]
            rfl
          rw [e2, bit_shl]
          split
          · rw [Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt (ofBits_lt _ j), Nat.or_comm]
          · rw [Nat.add_zero, Nat.or_zero]
        cases hlast : Nat.beq (j + 1) 112 <;> rw [hlast] at h <;> dsimp only at h
        · have hj1 : j + 1 ≠ 112 := fun e => by
            rw [e, Nat.beq_refl] at hlast
            exact Bool.noConfusion hlast
          exact dec_body M B i (j + 1) _ (pre ++ [dg ch]) (fun _ => ⟨hl', by omega, hr⟩)
            (fun h' => absurd h' (by omega)) h
        · have hj1 : j + 1 = 112 := Nat.eq_of_beq_eq_true hlast
          obtain ⟨hrow, hrest⟩ := andB_true' h
          have hrow' : row128 M i = ofBits 112 (gE (pre ++ [dg ch]) i) := by
            rw [Nat.eq_of_beq_eq_true hrow, hr, hj1]
          have ih := dec_body M B (i + 1) 0 0 (pre ++ [dg ch])
            (fun _ => ⟨by rw [hl']; omega, by omega, rfl⟩) (fun _ => ⟨by omega, rfl⟩) hrest
          refine ⟨ih.1, fun r hr1 hr2 => ?_⟩
          by_cases hri : r = i
          · subst hri
            rw [hrow']
            apply ofBits_congr
            intro j' hj'
            unfold gE
            rw [getD_append_left (pre := pre ++ [dg ch]) (X := ents B) (by rw [hl']; omega)]
          · exact ih.2 r hr1 (by omega)
      · obtain ⟨hi, hacc⟩ := h2 (Nat.le_of_ble_eq_true hb)
        exact dec_body M B i j acc (pre ++ [dg ch]) (fun h' => absurd h' (by omega))
          (fun _ => ⟨hi, hacc⟩) h

private theorem dec_header (M : Nat) : ∀ cs : List Char, decRun M cs 0 0 0 0 = true →
    decRun M ((cs.dropWhile (· != '\n')).drop 1) 1 0 0 0 = true
  | [], h => h
  | ch :: cs, h => by
    rw [decRun_cons] at h
    have e0 : Nat.beq 0 1 = false := rfl
    rw [e0] at h
    dsimp only at h
    by_cases hc : ch = '\n'
    · subst hc
      exact h
    · have h10 : Nat.beq (Char.toNat ch) 10 = false := by
        cases hb : Nat.beq (Char.toNat ch) 10
        · rfl
        · exfalso
          apply hc
          have := Nat.eq_of_beq_eq_true hb
          exact Char.ext (UInt32.toNat_inj.mp (by simpa using this))
      rw [h10] at h
      dsimp only at h
      have hne : (ch != '\n') = true := by simpa using hc
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact dec_header M cs h

theorem decode_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Nat} {l : List Char}
    (_h : decOK M l = true) : WfN (O.decode (String.ofList l)) ∧ encN (O.decode (String.ofList l)) = M := by
  obtain ⟨hM, hrows⟩ := dec_body M _ 0 0 0 [] (fun _ => ⟨rfl, by omega, rfl⟩)
    (fun h => absurd h (by omega)) (dec_header M l _h)
  have hdec : CFSG.Sporadic.Th.Native.decodeEntries (String.ofList l) =
      ents ((l.dropWhile (· != '\n')).drop 1) := by
    unfold CFSG.Sporadic.Th.Native.decodeEntries ents
    rw [String.toList_ofList]
    rfl
  have e1 : O.decode (String.ofList l) = Array.ofFn (n := 112) fun i => ofBits 112 fun j =>
      ((CFSG.Sporadic.Th.Native.decodeEntries (String.ofList l)).toArray[i.val * 112 + j]?.getD 0)
        % 2 == 1 := rfl
  have hR : ∀ i (hi : i < 112), (O.decode (String.ofList l))[i]?.getD 0 =
      ofBits 112 (gE (ents ((l.dropWhile (· != '\n')).drop 1)) i) := by
    intro i hi
    rw [e1, hdec]
    simp only [Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some, List.getElem?_toArray]
    rfl
  have hW : WfN (O.decode (String.ofList l)) := ⟨by rw [e1, Array.size_ofFn], fun i hi => by
    rw [get!_eq, hR i hi]
    exact ofBits_lt _ 112⟩
  refine ⟨hW, ?_⟩
  rw [encN_eq hW]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encR_bit]
  by_cases hp : p / 128 < 112
  · rw [mapRow hW, hR _ hp, ← List.nil_append (ents _), ← hrows (p / 128) hp (Nat.zero_le _),
      row128_eq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    have e : 128 * (p / 128) + p % 128 = p := by omega
    have hm : p % 128 < 128 := Nat.mod_lt _ (by omega)
    simp [hp, hm, e]
  · have e : 128 * 112 + (p - 128 * 112) = p := by omega
    have h0 : (M >>> (128 * 112)).testBit (p - 128 * 112) = (0 : Nat).testBit (p - 128 * 112) := by
      rw [hM]
    rw [Nat.testBit_shiftRight, e, Nat.zero_testBit] at h0
    rw [h0]
    simp [hp]

theorem mul_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array Nat} (_hX : WfN X)
    (_hY : WfN Y) : WfN (O.mul X Y) ∧ encN (O.mul X Y) = mulJ c rm (encN X) (encN Y) := by
  rw [mul_eq _hY]
  exact mulRows_enc' _hK _hX _hY

theorem mulRows_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array Nat}
    (_hX : WfN X) (_hY : WfN Y) :
    WfN (mulRows 112 X Y) ∧ encN (mulRows 112 X Y) = mulJ c rm (encN X) (encN Y) :=
  mulRows_enc' _hK _hX _hY

theorem vec_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (_hX : WfN X)
    (v : Nat) : vecMulN 112 X v = vecJ rm v (encN X) :=
  vec_enc' _hK _hX v

theorem vec_mul {X Y : Array Nat} (_hX : WfN X) (_hY : WfN Y) (v : Nat) :
    vecMulN 112 (O.mul X Y) v = vecMulN 112 Y (vecMulN 112 X v) := by
  have hV : ∀ u, vecMulN 112 Y u = vmN (fun j => Y[j]?.getD 0) u := fun u => vecMulN_eq 112 Y u
  rw [mul_eq _hY, vecMulN_eq, vecMulN_eq 112 X v, hV, vmN_xsum]
  apply xsum_congr
  intro k hk
  rw [mulRows_row _hX hk]
  split
  · exact hV _
  · exact (vmN_zero _).symm

private theorem id_row' {i : Nat} (hi : i < 112) : (idRows 112)[i]?.getD 0 = 2 ^ i := by
  simp [idRows, hi, Nat.one_shiftLeft]

private theorem wf_id : WfN (idRows 112) :=
  ⟨by simp [idRows], fun i hi => by
    rw [get!_eq, id_row' hi]
    exact Nat.pow_lt_pow_right (by omega) hi⟩

theorem id_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    WfN (idRows 112) ∧ encN (idRows 112) = one := by
  refine ⟨wf_id, ?_⟩
  rw [encN_eq wf_id, ← enc_idRows _hK]
  apply encR_congr
  intro i hi
  rw [mapRow wf_id, id_row' hi, id_row hi]

theorem id_vec {v : Nat} (_hv : v < 2 ^ 112) : vecMulN 112 (idRows 112) v = v := by
  have h : ∀ j < 112, (if v.testBit j then (idRows 112)[j]?.getD 0 else 0) =
      (if v.testBit j then 2 ^ j else 0) := fun j hj => by rw [id_row' hj]
  rw [vecMulN_eq, xsum_congr h, xsum_pow, Nat.mod_eq_of_lt _hv]

theorem enc_inj {X Y : Array Nat} (_hX : WfN X) (_hY : WfN Y) (_h : encN X = encN Y) : X = Y := by
  have hr : ∀ i < 112, X[i]?.getD 0 = Y[i]?.getD 0 := fun i hi => by
    have := rows_of_encR_eq (A := X.map ofN) (B := Y.map ofN)
      (by rw [← encN_eq _hX, ← encN_eq _hY]; exact _h) hi
    rwa [mapRow _hX, mapRow _hY] at this
  apply Array.ext
  · rw [_hX.1, _hY.1]
  · intro i h1 h2
    have hi : i < 112 := by rw [_hX.1] at h1; exact h1
    have := hr i hi
    rwa [getElem?_pos X i h1, getElem?_pos Y i h2, Option.getD_some, Option.getD_some] at this

theorem pack_enc {X : Array Nat} {P : Nat} (_h : packNK X.toList P = true) : WfN X ∧ encN X = P := by
  unfold packNK at _h
  obtain ⟨hlt, hlen, hP⟩ := pack_run P X.toList 0 0 _h
  rw [Nat.zero_add, Array.length_toList] at hlen
  have hW : WfN X := ⟨hlen, fun i hi => by
    have hs : i < X.size := by rw [hlen]; exact hi
    rw [getElem!_pos X i hs]
    exact hlt _ (Array.getElem_mem_toList hs)⟩
  refine ⟨hW, ?_⟩
  rw [hP, Nat.zero_or]
  unfold encN
  rw [List.range_eq_range']
  have e : (fun i acc => Nat.lor (Nat.shiftLeft (X.getD i 0) (128 * i)) acc) =
      (fun i acc => Nat.lor (Nat.shiftLeft (X.toList.getD i 0) (128 * i)) acc) := by
    funext i acc
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [e, pk_eq X.toList 112 0 (by rw [Array.length_toList, hlen]), List.drop_zero]

theorem ofFn_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {f : Fin 112 → Nat} {P : Nat}
    (_hf : ∀ i, f i < 2 ^ 112) (_hP : canonJ pad P = true) (_hr : ∀ i : Fin 112, rowJ rm P i = f i) :
    WfN (Array.ofFn f) ∧ encN (Array.ofFn f) = P := by
  obtain ⟨-, hrm⟩ := consts_c _hK
  subst hrm
  have hrow : ∀ i (hi : i < 112), (Array.ofFn f)[i]?.getD 0 = f ⟨i, hi⟩ := fun i hi => by
    simp [hi]
  have hW : WfN (Array.ofFn f) := ⟨by simp, fun i hi => by
    rw [get!_eq, hrow i hi]
    exact _hf _⟩
  refine ⟨hW, ?_⟩
  rw [encN_eq hW, ← encR_decN (consts_pad _hK) _hP]
  apply encR_congr
  intro i hi
  have hlt : rowJ (2 ^ 112 - 1) P i < 2 ^ 112 := Nat.and_lt_two_pow _ (by omega)
  rw [mapRow hW, hrow i hi, decN_row P hi, ofN_eq hlt]
  exact (_hr ⟨i, hi⟩).symm

theorem pow3_eq (X : Array Nat) : O.pow X 3 = O.mul X (O.mul X X) := by
  rw [Ops.pow, ite_eq_right (by decide), ite_eq_right (by decide)]
  simp only [show (3 : Nat) / 2 = 1 from rfl, show (3 : Nat) % 2 = 1 from rfl, ite_true]
  rw [Ops.pow, ite_eq_right (by decide), ite_eq_left rfl]

end CFSG.KS.SporSch.J4B

end

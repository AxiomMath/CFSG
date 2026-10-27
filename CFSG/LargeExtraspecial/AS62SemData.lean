module

public import CFSG.LargeExtraspecial.AS62Rels

public section

namespace CFSG.LargeExtraspecial.AS62.Sem

@[expose] def natEqB (n m : Nat) : Bool := Nat.beq n m

theorem eq_of_natEqB {n m : Nat} (h : natEqB n m = true) : n = m := Nat.eq_of_beq_eq_true h

@[expose] def app (q i : Nat) : Nat := q / 10 ^ (4 - i) % 10

@[expose] def colN (j : Nat) : Nat := 2 ^ j % 16 + j / 4 * 15

@[expose] def actN (q c : Nat) : Nat :=
  (c % 2 * colN (app q 0)) ^^^ (c / 2 % 2 * colN (app q 1)) ^^^
    (c / 4 % 2 * colN (app q 2)) ^^^ (c / 8 % 2 * colN (app q 3))

@[expose] def compN (q r : Nat) : Nat :=
  10000 * app q (app r 0) + 1000 * app q (app r 1) + 100 * app q (app r 2) +
    10 * app q (app r 3) + app q (app r 4)

@[expose] def invN (q : Nat) : Nat :=
  0 * 10 ^ (4 - app q 0) + 1 * 10 ^ (4 - app q 1) + 2 * 10 ^ (4 - app q 2) +
    3 * 10 ^ (4 - app q 3) + 4 * 10 ^ (4 - app q 4)

theorem colN_lt {j : Nat} (hj : j < 5) : colN j < 16 := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem xor_lt_16 {a b : Nat} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

theorem mod_two_mul_lt {c a : Nat} (ha : a < 16) : c % 2 * a < 16 := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> omega

theorem div_mod_two_mul_lt {c d a : Nat} (ha : a < 16) : c / d % 2 * a < 16 :=
  mod_two_mul_lt ha

theorem actN_lt {q : Nat} (hq : ∀ i, i < 4 → app q i < 5) (c : Nat) : actN q c < 16 := by
  unfold actN
  refine xor_lt_16 (xor_lt_16 (xor_lt_16 ?_ ?_) ?_) ?_
  · exact mod_two_mul_lt (colN_lt (hq 0 (by omega)))
  · exact div_mod_two_mul_lt (colN_lt (hq 1 (by omega)))
  · exact div_mod_two_mul_lt (colN_lt (hq 2 (by omega)))
  · exact div_mod_two_mul_lt (colN_lt (hq 3 (by omega)))

@[expose] def one : Nat × Nat := (0, 1234)

@[expose] def dmul (a b : Nat × Nat) : Nat × Nat := (a.1 ^^^ actN a.2 b.1, compN a.2 b.2)

@[expose] def dinv (a : Nat × Nat) : Nat × Nat := (actN (invN a.2) a.1, invN a.2)

@[expose] def deq (a b : Nat × Nat) : Bool := natEqB a.1 b.1 && natEqB a.2 b.2

theorem deq_self (a : Nat × Nat) : deq a a = true := by
  simp [deq, natEqB]

theorem eq_of_deq {a b : Nat × Nat} (h : deq a b = true) : a = b := by
  simp only [deq, Bool.and_eq_true] at h
  exact Prod.ext (eq_of_natEqB h.1) (eq_of_natEqB h.2)

@[expose] def zD : Nat × Nat := (1, 1234)

@[expose] def tD : Nat × Nat := (2, 1234)

@[expose] def eD : Nat × Nat := (0, 2143)

@[expose] def xD : Nat × Nat := (0, 1342)

@[expose] def sD : Nat × Nat := (0, 10324)

@[expose] def gdB (i : Fin 4) : Nat × Nat := [zD, tD, eD, xD].getD i.val one

@[expose] def gd2 (i : Fin 5) : Nat × Nat := [zD, tD, eD, xD, sD].getD i.val one

@[expose] def letterD {n : Nat} (gd : Fin n → Nat × Nat) (a : Fin n × Bool) : Nat × Nat :=
  cond a.2 (gd a.1) (dinv (gd a.1))

@[expose] def semEval {n : Nat} (gd : Fin n → Nat × Nat) (w : List (Fin n × Bool)) : Nat × Nat :=
  w.foldr (fun a d => dmul (letterD gd a) d) one

theorem semEval_nil {n : Nat} (gd : Fin n → Nat × Nat) : semEval gd [] = one := rfl

theorem semEval_cons {n : Nat} (gd : Fin n → Nat × Nat) (a : Fin n × Bool)
    (w : List (Fin n × Bool)) : semEval gd (a :: w) = dmul (letterD gd a) (semEval gd w) := rfl

theorem semEval_relsB : ∀ r ∈ relsB, semEval gdB r = one := by decide +kernel

theorem semEval_rels2 : ∀ r ∈ rels2, semEval gd2 r = one := by decide +kernel

@[expose] def dcode (d : Nat × Nat) : Nat := d.1 + 16 * (d.2 / 10)

@[expose] def bitsNodup : Nat → List Nat → Bool
  | _, [] => true
  | m, a :: l => !m.testBit a && bitsNodup (m ||| 1 <<< a) l

theorem nodup_of_bitsNodup : ∀ {m : Nat} {l : List Nat}, bitsNodup m l = true →
    l.Nodup ∧ ∀ a ∈ l, m.testBit a = false
  | _, [], _ => ⟨List.nodup_nil, by simp⟩
  | m, a :: l, h => by
    simp only [bitsNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hnd, hm⟩ := nodup_of_bitsNodup h2
    refine ⟨List.nodup_cons.2 ⟨fun ha => ?_, hnd⟩, fun b hb => ?_⟩
    · have := hm a ha
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact Bool.noConfusion this
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h1
      · have := hm b hb
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

@[expose] def wordOfCodeAux {n : Nat} (letter : Nat → Fin n × Bool) :
    Nat → Nat → List (Fin n × Bool) → List (Fin n × Bool)
  | 0, _, acc => acc
  | f + 1, c, acc =>
    if c = 0 then acc else wordOfCodeAux letter f (c / 10) (letter (c % 10) :: acc)

@[expose] def wordOfCode {n : Nat} (letter : Nat → Fin n × Bool) (c : Nat) :
    List (Fin n × Bool) :=
  wordOfCodeAux letter 20 c []

@[expose] def wordsDistinct {n : Nat} (gd : Fin n → Nat × Nat) (letter : Nat → Fin n × Bool)
    (cs : List Nat) : Bool :=
  bitsNodup 0 (cs.map fun c => dcode (semEval gd (wordOfCode letter c)))

theorem eq_of_wordsDistinct {n : Nat} {gd : Fin n → Nat × Nat} {letter : Nat → Fin n × Bool}
    {cs : List Nat} (h : wordsDistinct gd letter cs = true) {i j : Nat} (hi : i < cs.length)
    (hj : j < cs.length)
    (hij : semEval gd (wordOfCode letter cs[i]) = semEval gd (wordOfCode letter cs[j])) :
    i = j := by
  have hnd := (nodup_of_bitsNodup h).1
  have hi' : i < (cs.map fun c => dcode (semEval gd (wordOfCode letter c))).length := by
    rw [List.length_map]
    exact hi
  have hj' : j < (cs.map fun c => dcode (semEval gd (wordOfCode letter c))).length := by
    rw [List.length_map]
    exact hj
  refine (hnd.getElem_inj (hi := hi') (hj := hj')).1 ?_
  rw [List.getElem_map, List.getElem_map, hij]

@[expose] def letterB (d : Nat) : Fin 4 × Bool :=
  if d = 5 then (3, false) else (Fin.ofNat 4 (d - 1), true)

@[expose] def bCodes : List Nat :=
  [0, 1, 2, 3, 4, 5, 12, 13, 14, 15, 23, 24, 25, 32, 34, 35, 43, 53, 123, 124, 125, 132, 134, 135,
   143, 153, 232, 234, 235, 243, 253, 323, 324, 325, 343, 353, 432, 435, 532, 534, 1232, 1234, 1235,
   1243, 1253, 1323, 1324, 1325, 1343, 1353, 1432, 1435, 1532, 1534, 2323, 2324, 2325, 2343, 2353,
   2432, 2435, 2532, 2534, 3234, 3235, 3243, 3253, 3432, 3532, 4323, 4325, 5323, 5324, 12323, 12324,
   12325, 12343, 12353, 12432, 12435, 12532, 12534, 13234, 13235, 13243, 13253, 13432, 13532, 14323,
   14325, 15323, 15324, 23234, 23235, 23243, 23253, 23432, 23532, 24323, 24325, 25323, 25324, 32343,
   32353, 32432, 32435, 32532, 32534, 34323, 35323, 43234, 43235, 43253, 53234, 53235, 53243,
   123234, 123235, 123243, 123253, 123432, 123532, 124323, 124325, 125323, 125324, 132343, 132353,
   132432, 132435, 132532, 132534, 134323, 135323, 143234, 143235, 143253, 153234, 153235, 153243,
   232343, 232353, 232432, 232435, 232532, 232534, 234323, 235323, 243234, 243235, 243253, 253234,
   253235, 253243, 323432, 323532, 324323, 324325, 325323, 325324, 343234, 343235, 353234, 353235,
   432343, 432532, 432534, 532353, 532432, 532435, 1232343, 1232353, 1234323, 1235323, 1243234,
   1243235, 1253234, 1253235, 1323432, 1323532, 1324323, 1325323, 1343234, 1343235, 1353234,
   1353235, 1432343, 1532353, 2343235, 2353234, 3243235, 3253234]

theorem length_bCodes : bCodes.length = 192 := by decide +kernel

@[expose] def bWord (k : Fin 192) : List (Fin 4 × Bool) :=
  wordOfCode letterB (bCodes[k.val]'(Nat.lt_of_lt_of_eq k.isLt length_bCodes.symm))

theorem bDistinct_eq_true : wordsDistinct gdB letterB bCodes = true := by decide +kernel

theorem semEval_bWord_injective : Function.Injective fun k : Fin 192 => semEval gdB (bWord k) :=
  fun _ _ h => Fin.ext (eq_of_wordsDistinct bDistinct_eq_true _ _ h)

@[expose] def dconj (g u : Nat × Nat) : Nat × Nat := dmul (dmul g u) (dinv g)

@[expose] def dcomm (u v : Nat × Nat) : Nat × Nat := dmul (dmul (dmul u v) (dinv u)) (dinv v)

@[expose] def uOK (u : Nat × Nat) : Bool :=
  deq (dmul u u) one && deq (dmul u (dconj xD u)) (dmul (dconj xD u) u) &&
    deq (dconj xD (dconj xD u)) (dmul (dmul zD u) (dconj xD u))

@[expose] def vOK (v : Nat × Nat) : Bool :=
  deq (dmul v v) one && deq (dmul v (dconj xD v)) (dmul (dconj xD v) v) &&
    deq (dconj xD (dconj xD v)) (dmul v (dconj xD v))

@[expose] def mixedOK (u v : Nat × Nat) : Bool :=
  deq (dcomm u v) one && deq (dcomm u (dconj xD v)) zD && deq (dcomm (dconj xD u) v) zD &&
    deq (dcomm (dconj xD u) (dconj xD v)) one

@[expose] def relsOK (u v : Nat × Nat) : Bool := uOK u && vOK v && mixedOK u v

@[expose] def k1Codes : List Nat := [1234, 2143, 3412, 4321]

@[expose] def cands : List (Nat × Nat) :=
  (List.range 16).flatMap fun c => k1Codes.map fun q => (c, q)

@[expose] def sol18 : List ((Nat × Nat) × (Nat × Nat)) :=
  [((1, 2143), (6, 2143)), ((1, 2143), (7, 1234)), ((1, 3412), (10, 3412)),
   ((1, 3412), (11, 1234)), ((1, 4321), (12, 1234)), ((1, 4321), (13, 4321)),
   ((6, 1234), (0, 2143)), ((6, 1234), (6, 2143)), ((7, 2143), (0, 2143)),
   ((7, 2143), (7, 1234)), ((10, 1234), (0, 3412)), ((10, 1234), (10, 3412)),
   ((11, 3412), (0, 3412)), ((11, 3412), (11, 1234)), ((12, 4321), (0, 4321)),
   ((12, 4321), (12, 1234)), ((13, 1234), (0, 4321)), ((13, 1234), (13, 4321))]

@[expose] def memSol (u v : Nat × Nat) : Bool := sol18.any fun p => deq p.1 u && deq p.2 v

@[expose] def fcyCheck : Bool :=
  cands.all fun u => !uOK u || cands.all fun v => !vOK v || !mixedOK u v || memSol u v

theorem fcyCheck_eq_true : fcyCheck = true := by decide +kernel

theorem mem_cands {u : Nat × Nat} (h1 : u.1 < 16) (h2 : u.2 ∈ k1Codes) : u ∈ cands :=
  List.mem_flatMap.2 ⟨u.1, List.mem_range.2 h1, List.mem_map.2 ⟨u.2, h2, rfl⟩⟩

theorem mem_sol18_of_memSol {u v : Nat × Nat} (h : memSol u v = true) : (u, v) ∈ sol18 := by
  obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true] at hpe
  rw [← eq_of_deq hpe.1, ← eq_of_deq hpe.2]
  exact hp

theorem mem_sol18_of_relsOK {u v : Nat × Nat} (hu1 : u.1 < 16) (hu2 : u.2 ∈ k1Codes)
    (hv1 : v.1 < 16) (hv2 : v.2 ∈ k1Codes) (h : relsOK u v = true) : (u, v) ∈ sol18 := by
  have hc := fcyCheck_eq_true
  unfold fcyCheck at hc
  rw [List.all_eq_true] at hc
  have h1 := hc u (mem_cands hu1 hu2)
  simp only [relsOK, Bool.and_eq_true] at h
  obtain ⟨⟨hu, hv⟩, hm⟩ := h
  rw [hu, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
  have h2 := h1 v (mem_cands hv1 hv2)
  rw [hv, hm, Bool.not_true, Bool.false_or, Bool.false_or] at h2
  exact mem_sol18_of_memSol h2

theorem relsOK_of_mem_sol18 : ∀ p ∈ sol18, relsOK p.1 p.2 = true := by decide +kernel

theorem length_sol18 : sol18.length = 18 := rfl

theorem nodup_sol18 : sol18.Nodup := by decide +kernel

theorem alpha0_mem_sol18 : (dmul zD eD, dmul (dmul tD eD) tD) ∈ sol18 := by decide +kernel

@[expose] def zeD : Nat × Nat := dmul zD eD

@[expose] def tetD : Nat × Nat := dmul (dmul tD eD) tD

@[expose] def b1D : Nat × Nat := dmul (dmul (dmul tD eD) tD) eD

@[expose] def b2D : Nat × Nat := dconj xD b1D

@[expose] def e2D : Nat × Nat := dconj xD eD

theorem dmul_I1 : dmul (dmul zD zeD) tetD = b1D := by decide +kernel

theorem dmul_I2 : dmul (dmul (dmul zD tetD) zeD) tetD = eD := by decide +kernel

theorem dmul_I3 : dmul (dmul tD zeD) tD = dmul zD tetD := by decide +kernel

theorem dmul_I4 : dmul (dmul tD (dmul zeD tetD)) tD = dmul zeD tetD := by decide +kernel

@[expose] def qProdD (c : Nat) : Nat × Nat :=
  dmul (dmul (dmul (dmul (cond (c.testBit 0) b1D one) (cond (c.testBit 1) b2D one))
    (cond (c.testBit 2) eD one)) (cond (c.testBit 3) e2D one)) (cond (c.testBit 4) zD one)

theorem qDistinct_eq_true : bitsNodup 0 ((List.range 32).map fun c => dcode (qProdD c)) = true := by
  decide +kernel

theorem qProdD_injective {c d : Nat} (hc : c < 32) (hd : d < 32) (h : qProdD c = qProdD d) :
    c = d := by
  have hnd := (nodup_of_bitsNodup qDistinct_eq_true).1
  have hc' : c < ((List.range 32).map fun c => dcode (qProdD c)).length := by
    rw [List.length_map, List.length_range]
    exact hc
  have hd' : d < ((List.range 32).map fun c => dcode (qProdD c)).length := by
    rw [List.length_map, List.length_range]
    exact hd
  refine (hnd.getElem_inj (hi := hc') (hj := hd')).1 ?_
  rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_range, h]

end CFSG.LargeExtraspecial.AS62.Sem

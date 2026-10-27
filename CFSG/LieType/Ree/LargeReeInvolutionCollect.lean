module

public import CFSG.LieType.Ree.LargeReeB2
public import CFSG.LieType.Ree.Duality
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag (F4)
open scoped commutatorElement

abbrev Mono := List ℕ

abbrev Poly := List Mono

@[expose] def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => Nat.blt a b || (Nat.beq a b && monoLt m n)

@[expose] def monoInsert (a : ℕ) : Mono → Mono
  | [] => [a]
  | b :: m => if Nat.ble a b then a :: b :: m else b :: monoInsert a m

@[expose] def monoMul (m n : Mono) : Mono :=
  m.foldr monoInsert n

@[expose] def polyInsert (m : Mono) : Poly → Poly
  | [] => [m]
  | n :: p => if monoLt m n then m :: n :: p else if monoLt n m then n :: polyInsert m p else p

@[expose] def polyAdd (p q : Poly) : Poly :=
  p.foldr polyInsert q

@[expose] def polyMul (p q : Poly) : Poly :=
  p.foldr (fun m r => polyAdd (q.map (monoMul m)) r) []

@[expose] def polyPow (p : Poly) : ℕ → Poly
  | 0 => [[]]
  | n + 1 => polyMul p (polyPow p n)

section Eval

variable {R : Type*} [CommRing R]

@[expose] def monoEval (x : ℕ → R) (m : Mono) : R :=
  (m.map x).prod

@[expose] def polyEval (x : ℕ → R) (p : Poly) : R :=
  (p.map (monoEval x)).sum

theorem monoEval_nil (x : ℕ → R) : monoEval x [] = 1 :=
  rfl

theorem monoEval_cons (x : ℕ → R) (a : ℕ) (m : Mono) :
    monoEval x (a :: m) = x a * monoEval x m := by
  simp [monoEval]

theorem polyEval_nil (x : ℕ → R) : polyEval x [] = 0 :=
  rfl

theorem polyEval_cons (x : ℕ → R) (m : Mono) (p : Poly) :
    polyEval x (m :: p) = monoEval x m + polyEval x p := by
  simp [polyEval]

theorem monoEval_monoInsert (x : ℕ → R) (a : ℕ) :
    ∀ m : Mono, monoEval x (monoInsert a m) = x a * monoEval x m
  | [] => by simp [monoInsert, monoEval]
  | b :: m => by
    unfold monoInsert
    split
    · simp only [monoEval_cons]
    · rw [monoEval_cons, monoEval_monoInsert x a m, monoEval_cons, mul_left_comm]

theorem monoEval_monoMul (x : ℕ → R) (m n : Mono) :
    monoEval x (monoMul m n) = monoEval x m * monoEval x n := by
  induction m with
  | nil => simp [monoMul, monoEval]
  | cons a m ih =>
    change monoEval x (monoInsert a (monoMul m n)) = _
    rw [monoEval_monoInsert, ih, monoEval_cons, mul_assoc]

theorem eq_of_monoLt_eq_false : ∀ {m n : Mono}, monoLt m n = false → monoLt n m = false → m = n
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [monoLt] at h
  | _ :: _, [], _, h => by simp [monoLt] at h
  | a :: m, b :: n, h, h' => by
    simp only [monoLt, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h h'
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    have hab : a = b := by
      have ha : ¬ a < b := by simpa [Bool.eq_false_iff, Nat.blt_eq] using h1
      have hb : ¬ b < a := by simpa [Bool.eq_false_iff, Nat.blt_eq] using h1'
      omega
    subst hab
    have h3 : monoLt m n = false := by
      rcases h2 with h2 | h2
      · simp at h2
      · exact h2
    have h4 : monoLt n m = false := by
      rcases h2' with h2' | h2'
      · simp at h2'
      · exact h2'
    rw [eq_of_monoLt_eq_false h3 h4]

theorem polyEval_map_monoMul (x : ℕ → R) (m : Mono) (q : Poly) :
    polyEval x (q.map (monoMul m)) = monoEval x m * polyEval x q := by
  induction q with
  | nil => simp [polyEval]
  | cons n q ih =>
    rw [List.map_cons, polyEval_cons, ih, monoEval_monoMul, polyEval_cons, mul_add]

variable [CharP R 2]

theorem polyEval_polyInsert (x : ℕ → R) (m : Mono) :
    ∀ p : Poly, polyEval x (polyInsert m p) = monoEval x m + polyEval x p
  | [] => by simp [polyInsert, polyEval]
  | n :: p => by
    unfold polyInsert
    split
    · simp only [polyEval_cons]
    · split
      · rw [polyEval_cons, polyEval_polyInsert x m p, polyEval_cons, add_left_comm]
      · rename_i h1 h2
        have hmn : m = n := eq_of_monoLt_eq_false (by simpa using h1) (by simpa using h2)
        subst hmn
        rw [polyEval_cons, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem polyEval_polyAdd (x : ℕ → R) (p q : Poly) :
    polyEval x (polyAdd p q) = polyEval x p + polyEval x q := by
  induction p with
  | nil => simp [polyAdd, polyEval]
  | cons m p ih =>
    change polyEval x (polyInsert m (polyAdd p q)) = _
    rw [polyEval_polyInsert, ih, polyEval_cons, add_assoc]

theorem polyEval_polyMul (x : ℕ → R) (p q : Poly) :
    polyEval x (polyMul p q) = polyEval x p * polyEval x q := by
  induction p with
  | nil => simp [polyMul, polyEval]
  | cons m p ih =>
    change polyEval x (polyAdd (q.map (monoMul m)) (polyMul p q)) = _
    rw [polyEval_polyAdd, polyEval_map_monoMul, ih, polyEval_cons, add_mul]

theorem polyEval_polyPow (x : ℕ → R) (p : Poly) (n : ℕ) :
    polyEval x (polyPow p n) = polyEval x p ^ n := by
  induction n with
  | zero => simp [polyPow, polyEval, monoEval]
  | succ n ih => rw [polyPow, polyEval_polyMul, ih, pow_succ']

end Eval

abbrev Word := List (ℕ × Poly)

@[expose] def commTable : List (List (List (ℕ × ℕ × ℕ))) := [
  [[], [(1, 1, 26)], [], [], [(1, 1, 29)], [], [(1, 1, 31), (2, 1, 32)], [], [], [], [],
   [(1, 1, 36)], [], [(1, 1, 38), (2, 1, 39)], [], [], [(1, 1, 41), (2, 1, 42)], [], [],
   [(1, 1, 44)], [], [], [], []],
  [[(1, 1, 26)], [], [], [(1, 1, 28), (2, 1, 30)], [], [(1, 1, 31)], [], [], [], [],
   [(1, 1, 35), (2, 1, 37)], [], [(1, 1, 38)], [], [], [], [], [(1, 1, 43)],
   [(1, 1, 44), (2, 1, 45)], [], [], [], [], []],
  [[], [], [], [(1, 1, 29), (2, 1, 32)], [(1, 1, 31)], [], [], [], [], [],
   [(1, 1, 36), (2, 1, 39)], [(1, 1, 38)], [], [], [], [], [(1, 1, 43), (2, 1, 45)],
   [(1, 1, 44)], [], [], [], [], [], []],
  [[], [(1, 1, 28), (1, 2, 30)], [(1, 1, 29), (1, 2, 32)], [], [], [], [], [], [], [(1, 1, 34)],
   [], [], [], [(1, 1, 40)], [(1, 1, 41), (1, 2, 47)], [(1, 1, 42)], [], [], [], [], [],
   [(1, 1, 46)], [], []],
  [[(1, 1, 29)], [], [(1, 1, 31)], [], [], [], [], [], [], [(1, 1, 35), (2, 1, 40)], [], [],
   [(1, 1, 41)], [], [(1, 1, 43)], [(1, 1, 44), (2, 1, 46)], [], [], [], [], [], [], [], []],
  [[], [(1, 1, 31)], [], [], [], [], [], [], [], [(1, 1, 36), (2, 1, 42)], [], [(1, 1, 41)], [],
   [(1, 1, 43), (2, 1, 46)], [(1, 1, 44)], [], [], [], [], [], [], [], [], []],
  [[(1, 1, 31), (1, 2, 32)], [], [], [], [], [], [], [], [], [(1, 1, 37)], [(1, 1, 40)], [],
   [(1, 1, 43), (1, 2, 47)], [], [], [(1, 1, 45)], [], [], [(1, 1, 46)], [], [], [], [], []],
  [[], [], [], [], [], [], [], [], [], [(1, 1, 38), (2, 1, 45)], [(1, 1, 41), (2, 1, 46)],
   [(1, 1, 43)], [(1, 1, 44)], [], [], [], [], [], [], [], [], [], [], []],
  [[], [], [], [], [], [], [], [], [], [(1, 1, 39)], [(1, 1, 42)], [(1, 1, 44), (1, 2, 47)], [],
   [(1, 1, 45)], [], [], [(1, 1, 46)], [], [], [], [], [], [], []],
  [[], [], [], [(1, 1, 34)], [(1, 1, 35), (1, 2, 40)], [(1, 1, 36), (1, 2, 42)], [(1, 1, 37)],
   [(1, 1, 38), (1, 2, 45)], [(1, 1, 39)], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [(1, 1, 47)], []],
  [[], [(1, 1, 35), (1, 2, 37)], [(1, 1, 36), (1, 2, 39)], [], [], [], [(1, 1, 40)],
   [(1, 1, 41), (1, 2, 46)], [(1, 1, 42)], [], [], [], [], [], [], [], [], [], [], [], [],
   [(1, 1, 47)], [], []],
  [[(1, 1, 36)], [], [(1, 1, 38)], [], [], [(1, 1, 41)], [], [(1, 1, 43)],
   [(1, 1, 44), (2, 1, 47)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
  [[], [(1, 1, 38)], [], [], [(1, 1, 41)], [], [(1, 1, 43), (2, 1, 47)], [(1, 1, 44)], [], [],
   [], [], [], [], [], [], [], [], [], [], [], [], [], []],
  [[(1, 1, 38), (1, 2, 39)], [], [], [(1, 1, 40)], [], [(1, 1, 43), (1, 2, 46)], [], [],
   [(1, 1, 45)], [], [], [], [], [], [], [], [], [], [(1, 1, 47)], [], [], [], [], []],
  [[], [], [], [(1, 1, 41), (2, 1, 47)], [(1, 1, 43)], [(1, 1, 44)], [], [], [], [], [], [], [],
   [], [], [], [], [], [], [], [], [], [], []],
  [[], [], [], [(1, 1, 42)], [(1, 1, 44), (1, 2, 46)], [], [(1, 1, 45)], [], [], [], [], [], [],
   [], [], [], [(1, 1, 47)], [], [], [], [], [], [], []],
  [[(1, 1, 41), (1, 2, 42)], [], [(1, 1, 43), (1, 2, 45)], [], [], [], [], [], [(1, 1, 46)], [],
   [], [], [], [], [], [(1, 1, 47)], [], [], [], [], [], [], [], []],
  [[], [(1, 1, 43)], [(1, 1, 44)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [], [], [], [], [], []],
  [[], [(1, 1, 44), (1, 2, 45)], [], [], [], [], [(1, 1, 46)], [], [], [], [], [], [],
   [(1, 1, 47)], [], [], [], [], [], [], [], [], [], []],
  [[(1, 1, 44)], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [], [], []],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []],
  [[], [], [], [(1, 1, 46)], [], [], [], [], [], [], [(1, 1, 47)], [], [], [], [], [], [], [],
   [], [], [], [], [], []],
  [[], [], [], [], [], [], [], [], [], [(1, 1, 47)], [], [], [], [], [], [], [], [], [], [], [],
   [], [], []],
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]]

@[expose] def commFactors (i j : ℕ) : List (ℕ × ℕ × ℕ) :=
  (commTable.getD (i - 24) []).getD (j - 24) []

theorem commFactors_eq_0 : ∀ j : Fin 24, commFactors 24 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (24, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_1 : ∀ j : Fin 24, commFactors 25 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (25, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_2 : ∀ j : Fin 24, commFactors 26 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (26, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_3 : ∀ j : Fin 24, commFactors 27 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (27, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_4 : ∀ j : Fin 24, commFactors 28 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (28, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_5 : ∀ j : Fin 24, commFactors 29 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (29, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_6 : ∀ j : Fin 24, commFactors 30 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (30, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_7 : ∀ j : Fin 24, commFactors 31 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (31, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_8 : ∀ j : Fin 24, commFactors 32 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (32, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_9 : ∀ j : Fin 24, commFactors 33 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (33, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_10 : ∀ j : Fin 24, commFactors 34 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (34, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_11 : ∀ j : Fin 24, commFactors 35 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (35, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_12 : ∀ j : Fin 24, commFactors 36 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (36, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_13 : ∀ j : Fin 24, commFactors 37 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (37, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_14 : ∀ j : Fin 24, commFactors 38 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (38, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_15 : ∀ j : Fin 24, commFactors 39 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (39, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_16 : ∀ j : Fin 24, commFactors 40 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (40, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_17 : ∀ j : Fin 24, commFactors 41 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (41, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_18 : ∀ j : Fin 24, commFactors 42 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (42, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_19 : ∀ j : Fin 24, commFactors 43 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (43, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_20 : ∀ j : Fin 24, commFactors 44 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (44, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_21 : ∀ j : Fin 24, commFactors 45 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (45, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_22 : ∀ j : Fin 24, commFactors 46 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (46, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq_23 : ∀ j : Fin 24, commFactors 47 (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (47, 24 + (j : ℕ))).getD [] := by
  decide +kernel

theorem commFactors_eq : ∀ i j : Fin 24, commFactors (24 + (i : ℕ)) (24 + (j : ℕ)) =
    (f4OddCommutatorFactors.lookup (24 + (i : ℕ), 24 + (j : ℕ))).getD [] := by
  intro i
  fin_cases i
  · exact commFactors_eq_0
  · exact commFactors_eq_1
  · exact commFactors_eq_2
  · exact commFactors_eq_3
  · exact commFactors_eq_4
  · exact commFactors_eq_5
  · exact commFactors_eq_6
  · exact commFactors_eq_7
  · exact commFactors_eq_8
  · exact commFactors_eq_9
  · exact commFactors_eq_10
  · exact commFactors_eq_11
  · exact commFactors_eq_12
  · exact commFactors_eq_13
  · exact commFactors_eq_14
  · exact commFactors_eq_15
  · exact commFactors_eq_16
  · exact commFactors_eq_17
  · exact commFactors_eq_18
  · exact commFactors_eq_19
  · exact commFactors_eq_20
  · exact commFactors_eq_21
  · exact commFactors_eq_22
  · exact commFactors_eq_23

theorem commFactors_range : ∀ i j : Fin 24, (commFactors (24 + (i : ℕ)) (24 + (j : ℕ))).all
    (fun e => Nat.ble 24 e.2.2 && Nat.ble e.2.2 47) = true := by
  decide +kernel

@[expose] def commWord (g f : ℕ × Poly) : Word :=
  (commFactors g.1 f.1).map fun e => (e.2.2, polyMul (polyPow g.2 e.1) (polyPow f.2 e.2.1))

@[expose] def collect : ℕ → Word → Word → Word
  | 0, S, w => S.reverse ++ w
  | _ + 1, S, [] => S.reverse
  | n + 1, S, f :: w =>
    match f.2 with
    | [] => collect n S w
    | _ :: _ =>
      match S with
      | [] => collect n [f] w
      | g :: S' =>
        if Nat.blt g.1 f.1 then collect n (f :: g :: S') w
        else if Nat.beq g.1 f.1 then collect n S' ((f.1, polyAdd g.2 f.2) :: w)
        else collect n S' (commWord g f ++ f :: g :: w)

@[expose] def posWord : ℕ → List Poly → Word
  | _, [] => []
  | n, p :: ps => (n, p) :: posWord (n + 1) ps

@[expose] def collectCheck (n : ℕ) (w : Word) (T : List Poly) : Bool :=
  w.all (fun f => Nat.ble 24 f.1 && Nat.ble f.1 47) && Nat.beq T.length 24 &&
    collect n [] w == (posWord 24 T).filter fun f => !f.2.isEmpty

section WordEval

variable (R : Type) [CommRing R]

@[expose] def wordEval
    (x : ℕ → R) (w : Word) : (Module.End R (RootModule F4.tag R))ˣ :=
  (w.map fun f => pinnedX F4.tag R (orbitCertRoot F4.tag f.1) (polyEval x f.2)).prod

variable {R}

theorem wordEval_nil
    (x : ℕ → R) : wordEval R x [] = 1 :=
  rfl

theorem wordEval_cons
    (x : ℕ → R) (f : ℕ × Poly) (w : Word) :
    wordEval R x (f :: w) = pinnedX F4.tag R (orbitCertRoot F4.tag f.1) (polyEval x f.2) *
      wordEval R x w := by
  simp [wordEval]

theorem wordEval_append
    (x : ℕ → R) (w w' : Word) :
    wordEval R x (w ++ w') = wordEval R x w * wordEval R x w' := by
  simp [wordEval]

theorem pinnedX_mul_pinnedX_eq
    [CharP R 2] {i j : ℕ} (hi : 24 ≤ i ∧ i ≤ 47)
    (hj : 24 ≤ j ∧ j ≤ 47) (hij : i ≠ j) (s t : R) :
    pinnedX F4.tag R (orbitCertRoot F4.tag i) s * pinnedX F4.tag R (orbitCertRoot F4.tag j) t =
      (((f4OddCommutatorFactors.lookup (i, j)).getD []).map fun f =>
          pinnedX F4.tag R (orbitCertRoot F4.tag f.2.2) (s ^ f.1 * t ^ f.2.1)).prod *
        pinnedX F4.tag R (orbitCertRoot F4.tag j) t *
          pinnedX F4.tag R (orbitCertRoot F4.tag i) s := by
  have h : ⁅pinnedX F4.tag R (orbitCertRoot F4.tag i) s,
      pinnedX F4.tag R (orbitCertRoot F4.tag j) t⁆ =
      (((f4OddCommutatorFactors.lookup (i, j)).getD []).map fun f =>
        pinnedX F4.tag R (orbitCertRoot F4.tag f.2.2) (s ^ f.1 * t ^ f.2.1)).prod :=
    f4_even_positive_root_commutator_table.2.2.2.2 R i j hi.1 hi.2 hj.1 hj.2 hij s t
  rw [← h, commutatorElement_def]
  group

theorem wordEval_commWord
    [CharP R 2] (x : ℕ → R) {g f : ℕ × Poly} (hg : 24 ≤ g.1 ∧ g.1 ≤ 47)
    (hf : 24 ≤ f.1 ∧ f.1 ≤ 47) (hgf : g.1 ≠ f.1) :
    wordEval R x (commWord g f ++ f :: g :: []) = wordEval R x [g, f] := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 24, g.1 = 24 + i := ⟨⟨g.1 - 24, by omega⟩, by simp; omega⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 24, f.1 = 24 + j := ⟨⟨f.1 - 24, by omega⟩, by simp; omega⟩
  have hc := commFactors_eq i j
  rw [← hi, ← hj] at hc
  have hw : wordEval R x (commWord g f) = (((f4OddCommutatorFactors.lookup (g.1, f.1)).getD []).map
      fun e => pinnedX F4.tag R (orbitCertRoot F4.tag e.2.2)
        (polyEval x g.2 ^ e.1 * polyEval x f.2 ^ e.2.1)).prod := by
    rw [wordEval, commWord, hc, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun e _ => by
      simp only [Function.comp_apply, polyEval_polyMul, polyEval_polyPow])
  rw [wordEval_append, hw, wordEval_cons, wordEval_cons, wordEval_nil, mul_one, wordEval_cons,
    wordEval_cons, wordEval_nil, mul_one, pinnedX_mul_pinnedX_eq hg hf hgf, mul_assoc]

theorem mem_commWord_range {g f : ℕ × Poly} (hg : 24 ≤ g.1 ∧ g.1 ≤ 47)
    (hf : 24 ≤ f.1 ∧ f.1 ≤ 47) : ∀ e ∈ commWord g f, 24 ≤ e.1 ∧ e.1 ≤ 47 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 24, g.1 = 24 + i := ⟨⟨g.1 - 24, by omega⟩, by simp; omega⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 24, f.1 = 24 + j := ⟨⟨f.1 - 24, by omega⟩, by simp; omega⟩
  have h := commFactors_range i j
  rw [← hi, ← hj, List.all_eq_true] at h
  intro e he
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 he
  have := h c hc
  simp only [Bool.and_eq_true, Nat.ble_eq] at this
  exact this

theorem wordEval_collect
    [CharP R 2] (x : ℕ → R) :
    ∀ (n : ℕ) (S w : Word), (∀ f ∈ S, 24 ≤ f.1 ∧ f.1 ≤ 47) → (∀ f ∈ w, 24 ≤ f.1 ∧ f.1 ≤ 47) →
      wordEval R x (collect n S w) = wordEval R x (S.reverse ++ w) := by
  intro n
  induction n with
  | zero => intro S w _ _; rfl
  | succ n ih =>
    intro S w hS hw
    match w, hw with
    | [], _ => simp [collect]
    | f :: w, hw =>
      have hf := hw f List.mem_cons_self
      have hw' : ∀ e ∈ w, 24 ≤ e.1 ∧ e.1 ≤ 47 := fun e he => hw e (List.mem_cons_of_mem _ he)
      match hf2 : f.2 with
      | [] =>
        have h1 : collect (n + 1) S (f :: w) = collect n S w := by
          simp only [collect, hf2]
        rw [h1, ih S w hS hw', wordEval_append, wordEval_append, wordEval_cons, hf2,
          polyEval_nil, pinnedX_zero, one_mul]
      | m :: p =>
        match S, hS with
        | [], _ =>
          have h1 : collect (n + 1) [] (f :: w) = collect n [f] w := by
            simp only [collect, hf2]
          rw [h1, ih [f] w (by simpa using hf) hw']
          simp
        | g :: S', hS =>
          have hg := hS g List.mem_cons_self
          have hS' : ∀ e ∈ S', 24 ≤ e.1 ∧ e.1 ≤ 47 := fun e he => hS e (List.mem_cons_of_mem _ he)
          by_cases hlt : g.1 < f.1
          · have h1 : collect (n + 1) (g :: S') (f :: w) = collect n (f :: g :: S') w := by
              have hb : Nat.blt g.1 f.1 = true := by rw [Nat.blt_eq]; exact hlt
              simp only [collect, hf2, hb, ite_true]
            rw [h1, ih (f :: g :: S') w (by
              intro e he
              rcases List.mem_cons.1 he with rfl | he
              · exact hf
              · exact hS e he) hw']
            simp
          · by_cases heq : g.1 = f.1
            · have h1 : collect (n + 1) (g :: S') (f :: w) =
                  collect n S' ((f.1, polyAdd g.2 f.2) :: w) := by
                have hb : Nat.blt g.1 f.1 = false := by
                  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hlt
                have hb' : Nat.beq g.1 f.1 = true := by rw [Nat.beq_eq]; exact heq
                simp only [collect, hf2, hb, hb', Bool.false_eq_true, ite_false, ite_true]
              rw [h1, ih S' _ hS' (by
                intro e he
                rcases List.mem_cons.1 he with rfl | he
                · exact hf
                · exact hw' e he)]
              rw [List.reverse_cons, List.append_assoc, List.singleton_append, wordEval_append,
                wordEval_append, wordEval_cons, wordEval_cons, wordEval_cons, polyEval_polyAdd,
                pinnedX_add, heq, mul_assoc]
            · have h1 : collect (n + 1) (g :: S') (f :: w) =
                  collect n S' (commWord g f ++ f :: g :: w) := by
                have hb : Nat.blt g.1 f.1 = false := by
                  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hlt
                have hb' : Nat.beq g.1 f.1 = false := by
                  rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact heq
                simp only [collect, hf2, hb, hb', Bool.false_eq_true, ite_false]
              rw [h1, ih S' _ hS' (by
                intro e he
                rcases List.mem_append.1 he with he | he
                · exact mem_commWord_range hg hf e he
                · rcases List.mem_cons.1 he with rfl | he
                  · exact hf
                  · rcases List.mem_cons.1 he with rfl | he
                    · exact hg
                    · exact hw' e he)]
              have hc := wordEval_commWord x hg hf heq
              have e2 : wordEval R x (commWord g f ++ f :: g :: w) =
                  wordEval R x (g :: f :: w) := by
                have e1 : commWord g f ++ f :: g :: w = (commWord g f ++ [f, g]) ++ w := by simp
                rw [e1, wordEval_append, hc, show (g :: f :: w) = [g, f] ++ w from rfl,
                  wordEval_append]
              rw [List.reverse_cons, List.append_assoc, List.singleton_append, wordEval_append, e2,
                wordEval_append]

theorem wordEval_filter
    (x : ℕ → R) (w : Word) :
    wordEval R x (w.filter fun f => !f.2.isEmpty) = wordEval R x w := by
  induction w with
  | nil => rfl
  | cons f w ih =>
    rcases f with ⟨k, _ | ⟨m, p⟩⟩
    · simp [ih, wordEval_cons, polyEval_nil, pinnedX_zero]
    · simp [ih, wordEval_cons]

theorem wordEval_posWord (x : ℕ → R) :
    ∀ (n : ℕ) (ps : List Poly), wordEval R x (posWord n ps) =
      (List.ofFn fun i : Fin ps.length =>
        pinnedX F4.tag R (orbitCertRoot F4.tag (n + i)) (polyEval x (ps.get i))).prod
  | _, [] => rfl
  | n, p :: ps => by
    rw [posWord, wordEval_cons, wordEval_posWord x (n + 1) ps, List.ofFn_succ, List.prod_cons]
    have h0 : n + ((0 : Fin (ps.length + 1)) : ℕ) = n := by simp
    have hs : ∀ i : Fin ps.length, n + ((i.succ : Fin (ps.length + 1)) : ℕ) = n + 1 + i := by
      intro i
      simp only [Fin.val_succ]
      omega
    simp only [h0, hs, List.get_cons_zero]
    rfl

theorem wordEval_of_collectCheck
    [CharP R 2] {n : ℕ} {w : Word} {T : List Poly}
    (h : collectCheck n w T = true) (x : ℕ → R) :
    wordEval R x w = (List.ofFn fun i : Fin 24 =>
      pinnedX F4.tag R (orbitCertRoot F4.tag (24 + i)) (polyEval x (T.getD i []))).prod := by
  simp only [collectCheck, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, beq_iff_eq,
    Nat.beq_eq] at h
  obtain ⟨⟨hw, hT⟩, hc⟩ := h
  have h1 := wordEval_collect x n [] w (by simp) hw
  rw [List.reverse_nil, List.nil_append, hc, wordEval_filter, wordEval_posWord] at h1
  rw [← h1, List.ofFn_congr hT]
  refine congrArg List.prod (List.ofFn_inj.2 (funext fun i => ?_))
  rw [Fin.val_cast, List.get_eq_getElem, List.getD_eq_getElem _ _ (by omega)]
  rfl

end WordEval

section Coordinates

variable {R : Type} [CommRing R]

theorem orbitCertRoot_pos
    (i : Fin 24) :
    IsRoot F4.tag (orbitCertRoot F4.tag (24 + i)) ∧ 0 < height (orbitCertRoot F4.tag (24 + i)) :=
  (f4_even_positive_root_commutator_table.{0}.1 _).2 ⟨24 + i, by omega, by omega, rfl⟩

theorem orbitCertRoot_injective :
    Function.Injective fun i : Fin 24 => orbitCertRoot F4.tag (24 + (i : ℕ)) := fun i j h =>
  Fin.ext (by have := f4_orbitCertRoot_inj' (by omega) (by omega) h; omega)

theorem ofFn_pinnedX_injective :
    Function.Injective fun c : Fin 24 → R =>
      (List.ofFn fun i : Fin 24 => pinnedX F4.tag R (orbitCertRoot F4.tag (24 + i)) (c i)).prod :=
  CFSG.LieType.Ree.list_ofFn_pinnedX_injective _ orbitCertRoot_injective orbitCertRoot_pos R

theorem ofFn_pinnedX_zero :
    (List.ofFn fun i : Fin 24 => pinnedX F4.tag R (orbitCertRoot F4.tag (24 + i)) 0).prod = 1 := by
  simp [pinnedX_zero]

variable [CharP R 2]

theorem wordEval_eq_iff
    {n n' : ℕ} {w w' : Word} {T T' : List Poly}
    (h : collectCheck n w T = true) (h' : collectCheck n' w' T' = true) (x : ℕ → R) :
    wordEval R x w = wordEval R x w' ↔
      ∀ i : Fin 24, polyEval x (T.getD i []) = polyEval x (T'.getD i []) := by
  rw [wordEval_of_collectCheck h, wordEval_of_collectCheck h']
  exact ⟨fun hc i => congrFun (ofFn_pinnedX_injective hc) i, fun hc => by
    simp only [hc]⟩

theorem wordEval_eq_one_iff
    {n : ℕ} {w : Word} {T : List Poly} (h : collectCheck n w T = true)
    (x : ℕ → R) : wordEval R x w = 1 ↔ ∀ i : Fin 24, polyEval x (T.getD i []) = 0 := by
  rw [wordEval_of_collectCheck h, ← ofFn_pinnedX_zero]
  exact ⟨fun hc i => congrFun (ofFn_pinnedX_injective hc) i, fun hc => by
    simp only [hc]⟩

end Coordinates

@[expose] def monoSubst (φ : ℕ → Poly) (m : Mono) : Poly :=
  m.foldr (fun i r => polyMul (φ i) r) [[]]

@[expose] def polySubst (φ : ℕ → Poly) (p : Poly) : Poly :=
  p.foldr (fun m r => polyAdd (monoSubst φ m) r) []

@[expose] def substOf (l : List (ℕ × Poly)) (i : ℕ) : Poly :=
  (l.lookup i).getD [[i]]

@[expose] def sigmaVar (n i : ℕ) : Poly :=
  if Nat.blt i n then [[i + n]] else [[i - n, i - n]]

@[expose] def varsBelow (N : ℕ) (p : Poly) : Bool :=
  p.all fun m => m.all fun i => Nat.blt i N

section Subst

variable {R : Type} [CommRing R]

theorem polyEval_substOf (x : ℕ → R) {l : List (ℕ × Poly)}
    (hl : ∀ e ∈ l, polyEval x e.2 = x e.1) (i : ℕ) : polyEval x (substOf l i) = x i := by
  unfold substOf
  induction l with
  | nil => simp [polyEval, monoEval]
  | cons e l ih =>
    rw [List.lookup_cons]
    by_cases h : i = e.1
    · subst h
      simp only [beq_self_eq_true, Option.getD_some]
      exact hl e List.mem_cons_self
    · have hne : (i == e.1) = false := by simpa using h
      rw [hne]
      exact ih fun e' he' => hl e' (List.mem_cons_of_mem _ he')

theorem map_monoEval (σ : R →+* R) (x : ℕ → R) (m : Mono) :
    σ (monoEval x m) = monoEval (fun i => σ (x i)) m := by
  induction m with
  | nil => simp [monoEval]
  | cons i m ih => rw [monoEval_cons, map_mul, ih, monoEval_cons]

theorem map_polyEval (σ : R →+* R) (x : ℕ → R) (p : Poly) :
    σ (polyEval x p) = polyEval (fun i => σ (x i)) p := by
  induction p with
  | nil => simp [polyEval]
  | cons m p ih => rw [polyEval_cons, map_add, ih, map_monoEval, polyEval_cons]

theorem monoEval_congr {x y : ℕ → R} {m : Mono} (h : ∀ i ∈ m, x i = y i) :
    monoEval x m = monoEval y m := by
  unfold monoEval
  rw [List.map_congr_left h]

theorem polyEval_congr {x y : ℕ → R} {p : Poly} (h : ∀ m ∈ p, ∀ i ∈ m, x i = y i) :
    polyEval x p = polyEval y p := by
  unfold polyEval
  rw [List.map_congr_left fun m hm => monoEval_congr (h m hm)]

variable [CharP R 2]

theorem polyEval_monoSubst (x : ℕ → R) (φ : ℕ → Poly) (m : Mono) :
    polyEval x (monoSubst φ m) = monoEval (fun i => polyEval x (φ i)) m := by
  induction m with
  | nil => simp [monoSubst, polyEval, monoEval]
  | cons i m ih =>
    change polyEval x (polyMul (φ i) (monoSubst φ m)) = _
    rw [polyEval_polyMul, ih, monoEval_cons]

theorem polyEval_polySubst (x : ℕ → R) (φ : ℕ → Poly) (p : Poly) :
    polyEval x (polySubst φ p) = polyEval (fun i => polyEval x (φ i)) p := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    change polyEval x (polyAdd (monoSubst φ m) (polySubst φ p)) = _
    rw [polyEval_polyAdd, ih, polyEval_monoSubst, polyEval_cons]

theorem polyEval_polySubst_of (x : ℕ → R) {φ : ℕ → Poly} (hφ : ∀ i, polyEval x (φ i) = x i)
    (p : Poly) : polyEval x (polySubst φ p) = polyEval x p := by
  rw [polyEval_polySubst]
  exact congrArg (polyEval · p) (funext hφ)

theorem polyEval_polySubst_sigmaVar (σ : R →+* R) (hσ : ∀ c, σ (σ c) = c ^ 2) {n : ℕ}
    (x : ℕ → R) (hx : ∀ i < n, x (i + n) = σ (x i)) {p : Poly}
    (hp : varsBelow (2 * n) p = true) :
    polyEval x (polySubst (sigmaVar n) p) = σ (polyEval x p) := by
  rw [polyEval_polySubst, map_polyEval]
  refine polyEval_congr fun m hm i hi => ?_
  have hi' : i < 2 * n := by
    simp only [varsBelow, List.all_eq_true, Nat.blt_eq] at hp
    exact hp m hm i hi
  unfold sigmaVar
  by_cases h : i < n
  · rw [show Nat.blt i n = true by rw [Nat.blt_eq]; exact h]
    simp [polyEval, monoEval, hx i h]
  · rw [show Nat.blt i n = false by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h]
    simp only [Bool.false_eq_true, ite_false]
    have e : x i = σ (x (i - n)) := by
      have := hx (i - n) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this
    rw [e, hσ]
    simp [polyEval, monoEval, sq]

end Subst

end CFSG.LieType.Ree.LargeReeInvolution

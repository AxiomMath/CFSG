module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Leaf
public import CFSG.Sporadic.Schreier.Co1Base
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open Timmesfeld.Co1Leaf
open CFSG.Sporadic.Co1Schreier.Native (Rows mul one pow act add wf)

abbrev M24 : Type := Matrix (Fin 24) (Fin 24) (ZMod 2)

theorem rowsMatrix_mul24 (X Y : Rows) :
    rowsMatrix 24 (mul X Y) = rowsMatrix 24 X * rowsMatrix 24 Y :=
  rowsMatrix_mulRows 24 X Y

theorem rowsMatrix_one24 : rowsMatrix 24 (one ()) = 1 := rowsMatrix_idRows 24

theorem rowsMatrix_pow24 (X : Rows) (e : ℕ) : rowsMatrix 24 (pow X e) = rowsMatrix 24 X ^ e := by
  induction e with
  | zero => exact rowsMatrix_one24
  | succ e ih =>
    show rowsMatrix 24 (mul (pow X e) X) = _
    rw [rowsMatrix_mul24, ih, pow_succ]

theorem toVecD_shiftLeft (i : Fin 24) : toVecD 24 (1 <<< i.val) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h', Ne.symm h]

theorem vecMulN_lt (R : Array ℕ) (hR : ∀ r ∈ R, r < 2 ^ 24) (v : ℕ) : vecMulN 24 R v < 2 ^ 24 := by
  unfold vecMulN
  suffices h : ∀ (l : List ℕ) (a : ℕ), a < 2 ^ 24 →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) a < 2 ^ 24 from
    h _ 0 (by norm_num)
  intro l
  induction l with
  | nil => intro a ha; exact ha
  | cons j l ih =>
    intro a ha
    rw [List.foldl_cons]
    apply ih
    split_ifs
    · refine Nat.xor_lt_two_pow ha ?_
      cases h : R[j]? with
      | none => simp
      | some r => exact hR r (Array.mem_of_getElem? h)
    · exact ha

theorem exists_toVecD (v : Vec24) : ∃ x < 2 ^ 24, toVecD 24 x = v := by
  refine ⟨ofBits 24 fun j => if h : j < 24 then decide (v ⟨j, h⟩ = 1) else false,
    ofBits_lt 24 _, ?_⟩
  funext j
  rw [toVecD_ofBits]
  simp only [j.isLt, dite_true]
  have : v j = 0 ∨ v j = 1 := by
    generalize v j = x
    revert x
    decide
  rcases this with h | h <;> simp [h]

theorem matrix_eq_one_of_mulVec {A : M24} (h : ∀ v : Vec24, A *ᵥ v = v) : A = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at this
  rw [Matrix.one_apply]
  simp only [Matrix.col_apply] at this
  rw [this, Pi.single_apply]

theorem vec_eq_sum (v : Vec24) : v = ∑ i : Fin 24, v i • (Pi.single i 1 : Vec24) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

section Comm

variable {n a b : M24}

theorem comm_mul24 (ha : n * a = a * n) (hb : n * b = b * n) : n * (a * b) = (a * b) * n := by
  rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem comm_pow24 (ha : n * a = a * n) (k : ℕ) : n * a ^ k = a ^ k * n := by
  induction k with
  | zero => rw [pow_zero, mul_one, one_mul]
  | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, ha, mul_assoc]

theorem comm_add24 (ha : n * a = a * n) (hb : n * b = b * n) : n * (a + b) = (a + b) * n := by
  rw [mul_add, add_mul, ha, hb]

theorem comm_one24 : n * 1 = 1 * n := by rw [mul_one, one_mul]

theorem comm_zero24 : n * 0 = 0 * n := by rw [mul_zero, zero_mul]

theorem comm_ite24 {p : Prop} [Decidable p] (ha : n * a = a * n) :
    n * (if p then a else 0) = (if p then a else 0) * n := by
  split_ifs
  · exact ha
  · exact comm_zero24

theorem comm_listSum24 (l : List M24) (h : ∀ x ∈ l, n * x = x * n) : n * l.sum = l.sum * n := by
  induction l with
  | nil => rw [List.sum_nil]; exact comm_zero24
  | cons x l ih =>
    rw [List.sum_cons]
    exact comm_add24 (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem comm_finsetSum24 {ι : Type*} (s : Finset ι) (f : ι → M24) (h : ∀ i ∈ s, n * f i = f i * n) :
    n * (∑ i ∈ s, f i) = (∑ i ∈ s, f i) * n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact comm_zero24
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact comm_add24 (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mul_pow24 (h : a * b = b * a) (k : ℕ) : (a * b) ^ k = a ^ k * b ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, mul_one]
  | succ k ih =>
    have hb : b ^ k * a = a * b ^ k := (comm_pow24 h k).symm
    rw [pow_succ, ih, pow_succ, pow_succ, mul_assoc, ← mul_assoc (b ^ k), hb, mul_assoc,
      mul_assoc]

theorem add_self24 (M : M24) : M + M = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  generalize M i j = x
  revert x
  decide

theorem pow_four_add24 (h : a * b = b * a) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have sq : ∀ {x y : M24}, x * y = y * x → (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y hxy
    rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add, hxy, add_assoc, ← add_assoc (y * x),
      add_self24, zero_add]
  have h2 : a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 := by
    rw [comm_pow24 (comm_pow24 h 2).symm 2 |>.symm]
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq h, sq h2, ← pow_mul, ← pow_mul]

end Comm

section Elements

variable {gs : List Rows}

def GensComm (gs : List Rows) : Prop :=
  ∀ g ∈ gs, ∀ g' ∈ gs, rowsMatrix 24 g * rowsMatrix 24 g' = rowsMatrix 24 g' * rowsMatrix 24 g

theorem comm_eltR {n : M24} (h : ∀ g ∈ gs, n * rowsMatrix 24 g = rowsMatrix 24 g * n)
    (e : List ℕ) : n * rowsMatrix 24 (eltR gs e) = rowsMatrix 24 (eltR gs e) * n := by
  unfold eltR
  have key : ∀ (l : List (Rows × ℕ)) (acc : Rows), (∀ ge ∈ l, ge.1 ∈ gs) →
      n * rowsMatrix 24 acc = rowsMatrix 24 acc * n →
      n * rowsMatrix 24 (l.foldl (fun acc ge => mul acc (pow ge.1 ge.2)) acc) =
        rowsMatrix 24 (l.foldl (fun acc ge => mul acc (pow ge.1 ge.2)) acc) * n := by
    intro l
    induction l with
    | nil => intro acc _ hacc; exact hacc
    | cons ge l ih =>
      intro acc hl hacc
      rw [List.foldl_cons]
      refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_
      rw [rowsMatrix_mul24, rowsMatrix_pow24]
      exact comm_mul24 hacc (comm_pow24 (h _ (hl ge List.mem_cons_self)) _)
  refine key _ _ (fun ge hge => (List.of_mem_zip hge).1) ?_
  rw [rowsMatrix_one24]
  exact comm_one24

theorem eltR_cube
    (hc : GensComm gs)
    (h3 : ∀ g ∈ gs, rowsMatrix 24 g ^ 3 = 1) (e : List ℕ) : rowsMatrix 24 (eltR gs e) ^ 3 = 1 := by
  unfold eltR
  have key : ∀ (l : List (Rows × ℕ)) (acc : Rows), (∀ ge ∈ l, ge.1 ∈ gs) →
      (∀ g ∈ gs, rowsMatrix 24 acc * rowsMatrix 24 g = rowsMatrix 24 g * rowsMatrix 24 acc) →
      rowsMatrix 24 acc ^ 3 = 1 →
      rowsMatrix 24 (l.foldl (fun acc ge => mul acc (pow ge.1 ge.2)) acc) ^ 3 = 1 := by
    intro l
    induction l with
    | nil => intro acc _ _ h; exact h
    | cons ge l ih =>
      intro acc hl hca h3a
      rw [List.foldl_cons]
      have hg := hl ge List.mem_cons_self
      refine ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) ?_ ?_
      · intro g hgm
        rw [rowsMatrix_mul24, rowsMatrix_pow24]
        have h1 : rowsMatrix 24 g * rowsMatrix 24 acc = rowsMatrix 24 acc * rowsMatrix 24 g :=
          (hca g hgm).symm
        have h2 : rowsMatrix 24 g * rowsMatrix 24 ge.1 ^ ge.2 =
            rowsMatrix 24 ge.1 ^ ge.2 * rowsMatrix 24 g := comm_pow24 (hc g hgm _ hg) _
        exact (comm_mul24 h1 h2).symm
      · rw [rowsMatrix_mul24, rowsMatrix_pow24, mul_pow24 (comm_pow24 (hca _ hg) _), h3a, one_mul,
          ← pow_mul, mul_comm, pow_mul, h3 _ hg, one_pow]
  refine key _ _ (fun ge hge => (List.of_mem_zip hge).1) (fun g _ => ?_) ?_
  · rw [rowsMatrix_one24, mul_one, one_mul]
  · rw [rowsMatrix_one24, one_pow]

theorem comm_eltR_eltR
    (hc : GensComm gs)
    (e e' : List ℕ) :
    rowsMatrix 24 (eltR gs e) * rowsMatrix 24 (eltR gs e') =
      rowsMatrix 24 (eltR gs e') * rowsMatrix 24 (eltR gs e) :=
  comm_eltR (fun g hg => (comm_eltR (fun g' hg' => hc g hg g' hg') e).symm) e'

theorem eltsOf_getD (j : ℕ) : ∃ e, (eltsOf gs).getD j (one ()) = eltR gs e := by
  by_cases hj : j < (eltsOf gs).size
  · have hj' : j < (expVecs 3 gs.length).length := by simpa [eltsOf] using hj
    refine ⟨(expVecs 3 gs.length)[j], ?_⟩
    simp [eltsOf, Array.getD, hj']
  · refine ⟨[], ?_⟩
    simp [Array.getD, hj, eltR]

noncomputable abbrev fM (gs : List Rows) (j : ℕ) : M24 :=
  rowsMatrix 24 ((eltsOf gs).getD j (one ()))

theorem comm_fM {n : M24} (h : ∀ g ∈ gs, n * rowsMatrix 24 g = rowsMatrix 24 g * n) (j : ℕ) :
    n * fM gs j = fM gs j * n := by
  obtain ⟨e, he⟩ := eltsOf_getD (gs := gs) j
  rw [fM, he]
  exact comm_eltR h e

theorem comm_fM_fM
    (hc : GensComm gs)
    (j j' : ℕ) : fM gs j * fM gs j' = fM gs j' * fM gs j := by
  obtain ⟨e, he⟩ := eltsOf_getD (gs := gs) j
  obtain ⟨e', he'⟩ := eltsOf_getD (gs := gs) j'
  rw [fM, fM, he, he']
  exact comm_eltR_eltR hc e e'

theorem fM_cube
    (hc : GensComm gs)
    (h3 : ∀ g ∈ gs, rowsMatrix 24 g ^ 3 = 1) (j : ℕ) : fM gs j ^ 3 = 1 := by
  obtain ⟨e, he⟩ := eltsOf_getD (gs := gs) j
  rw [fM, he]
  exact eltR_cube hc h3 e

def IsSumF (gs : List Rows) (M : M24) : Prop := ∃ l : List ℕ, M = (l.map (fM gs)).sum

theorem IsSumF.comm {n : M24} (h : ∀ g ∈ gs, n * rowsMatrix 24 g = rowsMatrix 24 g * n)
    {M : M24} (hM : IsSumF gs M) : n * M = M * n := by
  obtain ⟨l, rfl⟩ := hM
  refine comm_listSum24 _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact comm_fM h j

theorem IsSumF.comm_sumF
    (hc : GensComm gs)
    {M M' : M24} (hM : IsSumF gs M) (hM' : IsSumF gs M') : M * M' = M' * M := by
  obtain ⟨l, rfl⟩ := hM
  refine (comm_listSum24 _ fun x hx => ?_).symm
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l', rfl⟩ := hM'
  exact (comm_listSum24 _ fun y hy => by
    obtain ⟨j', -, rfl⟩ := List.mem_map.1 hy
    exact comm_fM_fM hc j j').symm

theorem IsSumF.pow_four
    (hc : GensComm gs)
    (h3 : ∀ g ∈ gs, rowsMatrix 24 g ^ 3 = 1) {M : M24} (hM : IsSumF gs M) : M ^ 4 = M := by
  obtain ⟨l, rfl⟩ := hM
  induction l with
  | nil =>
    rw [List.map_nil, List.sum_nil]
    exact zero_pow (by norm_num)
  | cons j l ih =>
    rw [List.map_cons, List.sum_cons]
    have hcomm : fM gs j * (l.map (fM gs)).sum = (l.map (fM gs)).sum * fM gs j :=
      comm_listSum24 _ fun y hy => by
        obtain ⟨j', -, rfl⟩ := List.mem_map.1 hy
        exact comm_fM_fM hc j j'
    rw [pow_four_add24 hcomm, ih, pow_succ, fM_cube hc h3 j, one_mul]

end Elements

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem vec_eq_ite (v : Vec24) :
    v = ∑ i : Fin 24, if v i = 1 then (Pi.single i 1 : Vec24) else 0 := by
  conv_lhs => rw [vec_eq_sum v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod2_cases (v i) with h | h <;> simp [h]

theorem mulVec_eq_ite (M : M24) (v : Vec24) :
    M *ᵥ v = ∑ i : Fin 24, if v i = 1 then M *ᵥ (Pi.single i 1 : Vec24) else 0 := by
  conv_lhs => rw [vec_eq_ite v]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem vec_add_self (v : Vec24) : v + v = 0 := by
  funext i
  rw [Pi.add_apply, Pi.zero_apply]
  generalize v i = x
  revert x
  decide

theorem mulVec_fix_of_cube {n : M24} {m : ℕ} (hm : n ^ m = 1) (hm3 : Nat.Coprime m 3)
    {v : Vec24} (h3 : (n ^ 3) *ᵥ v = v) : n *ᵥ v = v := by
  have hpow : ∀ q : ℕ, (n ^ (3 * q)) *ᵥ v = v := by
    intro q
    induction q with
    | zero => rw [mul_zero, pow_zero, Matrix.one_mulVec]
    | succ q ih => rw [mul_add, mul_one, pow_add, ← Matrix.mulVec_mulVec, h3, ih]
  have hmod : (n ^ (m % 3)) *ᵥ v = v := by
    have e : (n ^ m) *ᵥ v = v := by rw [hm, Matrix.one_mulVec]
    rw [← Nat.mod_add_div m 3, pow_add, ← Matrix.mulVec_mulVec, hpow] at e
    exact e
  have hnd : ¬ 3 ∣ m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hm3.symm
  have hlt := Nat.mod_lt m (show 0 < 3 by norm_num)
  interval_cases hr : m % 3
  · exact absurd (Nat.dvd_of_mod_eq_zero hr) hnd
  · rwa [pow_one] at hmod
  · calc n *ᵥ v = n *ᵥ ((n ^ 2) *ᵥ v) := by rw [hmod]
      _ = (n ^ 3) *ᵥ v := by rw [Matrix.mulVec_mulVec, ← pow_succ']
      _ = v := h3

theorem finset_sum_pow_four {ι : Type*} (s : Finset ι) (f : ι → M24)
    (hc : ∀ i ∈ s, ∀ j ∈ s, f i * f j = f j * f i) (h4 : ∀ i ∈ s, f i ^ 4 = f i) :
    (∑ i ∈ s, f i) ^ 4 = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero_pow (by norm_num)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    have hcs : f x * (∑ i ∈ s, f i) = (∑ i ∈ s, f i) * f x :=
      comm_finsetSum24 _ _ fun i hi =>
        hc x (Finset.mem_insert_self x s) i (Finset.mem_insert_of_mem hi)
    rw [pow_four_add24 hcs, h4 x (Finset.mem_insert_self x s),
      ih (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (fun i hi => h4 i (Finset.mem_insert_of_mem hi))]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

end

module

public import Certificates.Data.H9Four
public import Certificates.Data.Kernel.H9Four.Pk
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.H9Four.Codes

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec

@[simp] theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

@[simp] theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

@[simp] theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

@[simp] theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem allL_iff (l : List ℕ) (f : ℕ → Bool) : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons x t ih =>
    change andB (f x) (allL t f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyL_iff (l : List ℕ) (f : ℕ → Bool) : anyL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | cons x t ih =>
    change orB (f x) (anyL t f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    simp

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (n : ℕ) (f : ℕ → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl h

theorem memN_iff (x : ℕ) (l : List ℕ) : memN x l = true ↔ x ∈ l := by
  unfold memN
  rw [letB_eq]
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons z t ih =>
    change orB (Nat.beq x z) _ = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenN t) = _
    rw [ih, List.length_cons]

theorem eqLN_iff (a b : List ℕ) : eqLN a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [eqLN]
  | cons x t ih =>
    cases b with
    | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h (List.cons_ne_nil _ _)⟩
    | cons y u =>
      change andB (Nat.beq x y) (eqLN t u) = true ↔ _
      rw [andB_eq, Bool.and_eq_true, ih, Nat.beq_eq, List.cons.injEq]

theorem nodupN_iff (l : List ℕ) : nodupN l = true ↔ l.Nodup := by
  induction l with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | cons z t ih =>
    change andB (notB (memN z t)) (nodupN t) = true ↔ _
    rw [andB_eq, notB_eq, Bool.and_eq_true, ih, List.nodup_cons, Bool.not_eq_true',
      ← Bool.not_eq_true, memN_iff]

theorem mapL_eq (g : ℕ → ℕ) (l : List ℕ) : mapL g l = l.map g := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change g x :: mapL g t = _
    rw [ih, List.map_cons]

theorem appL_eq (a b : List ℕ) : appL a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x t ih =>
    change x :: appL t b = _
    rw [ih, List.cons_append]

theorem lenLL_eq (L : List (List ℕ)) : lenLL L = L.length := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    change Nat.succ (lenLL t) = _
    rw [ih, List.length_cons]

theorem eqLL_iff (A B : List (List ℕ)) : eqLL A B = true ↔ A = B := by
  induction A generalizing B with
  | nil => cases B <;> simp [eqLL]
  | cons x t ih =>
    cases B with
    | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h (List.cons_ne_nil _ _)⟩
    | cons y u =>
      change andB (eqLN x y) (eqLL t u) = true ↔ _
      rw [andB_eq, Bool.and_eq_true, ih, eqLN_iff, List.cons.injEq]

theorem nthK_eq (L : List (List ℕ)) (i : ℕ) : nthK L i = L.getD i [] := by
  unfold nthK nthL
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons x t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem land_eq (x y : ℕ) : Nat.land x y = x &&& y := rfl
theorem lor_eq (x y : ℕ) : Nat.lor x y = x ||| y := rfl
theorem xor_eq (x y : ℕ) : Nat.xor x y = x ^^^ y := rfl
theorem shiftLeft_eq (x y : ℕ) : Nat.shiftLeft x y = x <<< y := rfl
theorem shiftRight_eq (x y : ℕ) : Nat.shiftRight x y = x >>> y := rfl

theorem toMatrix_ofCode (k : ℕ) : (Mat.ofCode k).toMatrix = pkMat 4 k := by
  ext i j
  simp [Mat.toMatrix, Mat.ofCode, pkMat]

theorem ofMatrix_toMatrix (v : Mat) : Mat.ofMatrix v.toMatrix = v := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [Mat.ofMatrix, Mat.toMatrix]

theorem ofCode_eq_ofMatrix (k : ℕ) : Mat.ofCode k = Mat.ofMatrix (pkMat 4 k) := by
  rw [← toMatrix_ofCode, ofMatrix_toMatrix]

theorem ofCode_mul4 (a b : ℕ) : Mat.ofCode (mul4 a b) = Mat.mul (Mat.ofCode a) (Mat.ofCode b) := by
  rw [Mat.mul, toMatrix_ofCode, toMatrix_ofCode, ← pkMat_mulF2, ofCode_eq_ofMatrix]
  rfl

theorem pkMat_one4 : pkMat 4 one4 = 1 := pkMat_oneF2 4

theorem ofCode_one4 : Mat.ofCode one4 = Mat.one := by
  rw [ofCode_eq_ofMatrix, pkMat_one4]
  rfl

theorem pkMat_mul4 (a b : ℕ) : pkMat 4 (mul4 a b) = pkMat 4 a * pkMat 4 b := pkMat_mulF2 4 a b

theorem testBit_tr4 (a : ℕ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    (tr4 a).testBit (4 * i + j) = a.testBit (4 * j + i) := by
  simp only [tr4, letN_eq, land_eq, lor_eq, xor_eq, shiftLeft_eq, shiftRight_eq]
  have c1 : ∀ n, Nat.testBit 2570 n = decide (2570 / 2 ^ n % 2 = 1) :=
    fun _ => Nat.testBit_eq_decide_div_mod_eq
  have c2 : ∀ n, Nat.testBit 204 n = decide (204 / 2 ^ n % 2 = 1) :=
    fun _ => Nat.testBit_eq_decide_div_mod_eq
  interval_cases i <;> interval_cases j <;>
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight] <;>
    simp [c1, c2, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, Bool.and_xor_distrib_right]

theorem pkMat_tr4 (a : ℕ) : pkMat 4 (tr4 a) = (pkMat 4 a).transpose := by
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.transpose_apply]
  rw [testBit_tr4 a i.isLt j.isLt]

theorem ofCode_tr4 (a : ℕ) : Mat.ofCode (tr4 a) = Mat.tr (Mat.ofCode a) := by
  rw [Mat.tr, toMatrix_ofCode, ← pkMat_tr4, ofCode_eq_ofMatrix]

theorem testBit_lt_of_ofCode {a b : ℕ} (h : Mat.ofCode a = Mat.ofCode b) {n : ℕ} (hn : n < 16) :
    a.testBit n = b.testBit n := by
  have h1 := congrArg Mat.toMatrix h
  rw [toMatrix_ofCode, toMatrix_ofCode] at h1
  have h2 := congrFun (congrFun h1 ⟨n / 4, by omega⟩) ⟨n % 4, by omega⟩
  simp only [pkMat, Matrix.of_apply] at h2
  have hn' : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
  rw [hn'] at h2
  cases ha : a.testBit n <;> cases hb : b.testBit n <;> simp_all

theorem ofCode_injective {a b : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (h : Mat.ofCode a = Mat.ofCode b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 16
  · exact testBit_lt_of_ofCode h hn
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem exists_code (A : Fin 4 → Fin 4 → ZMod 2) :
    ∃ k < 2 ^ 16, pkMat 4 k = Matrix.of A := by
  let f : ℕ → ℕ := fun t => if h : t < 16 then
    (if A ⟨t / 4, by omega⟩ ⟨t % 4, by omega⟩ = 1 then 1 else 0) else 0
  have hf : ∀ t < 16, f t < 2 ^ 1 := fun t _ => by
    simp only [f]
    split_ifs <;> norm_num
  refine ⟨∑ t ∈ Finset.range 16, f t * 2 ^ (1 * t), blockSum_lt 16 hf, ?_⟩
  ext i j
  simp only [pkMat, Matrix.of_apply]
  have h1 := testBit_blockSum 16 hf (4 * i.val + j.val) 0 (by norm_num)
  rw [Nat.one_mul, Nat.add_zero] at h1
  rw [h1]
  have hlt : 4 * i.val + j.val < 16 := by omega
  have hi : (4 * i.val + j.val) / 4 = i.val := by omega
  have hj : (4 * i.val + j.val) % 4 = j.val := by omega
  simp only [f, hlt, dite_true, decide_true, Bool.true_and]
  have e : A ⟨(4 * i.val + j.val) / 4, by omega⟩ ⟨(4 * i.val + j.val) % 4, by omega⟩ = A i j := by
    congr 1 <;> exact Fin.ext (by simp [hi, hj])
  rw [e]
  generalize A i j = x
  revert x
  decide

theorem mul4_lt (a b : ℕ) : mul4 a b < 2 ^ 16 := by
  rw [mul4, mulF2_eq_fold (by norm_num)]
  have hs : ∀ k, stepF2 4 a b k < 2 ^ 16 := by
    intro k
    unfold stepF2
    refine lt_of_le_of_lt (Nat.and_le_right) ?_
    have h1 : ((b >>> (4 * k)) &&& (2 ^ 4 - 1)) ≤ 2 ^ 4 - 1 := Nat.and_le_right
    have h2 := repu_mul 4 4
    calc ((b >>> (4 * k)) &&& (2 ^ 4 - 1)) * repu 4 4 ≤ (2 ^ 4 - 1) * repu 4 4 :=
          Nat.mul_le_mul_right _ h1
      _ < 2 ^ 16 := by omega
  have key : ∀ m, foldF2 4 a b m < 2 ^ 16 := by
    intro m
    induction m with
    | zero => exact Nat.two_pow_pos 16
    | succ m ih => exact Nat.xor_lt_two_pow ih (hs m)
  exact key 4

theorem tr4_lt {a : ℕ} (ha : a < 2 ^ 16) : tr4 a < 2 ^ 16 := by
  simp only [tr4, letN_eq, land_eq, xor_eq, shiftLeft_eq, shiftRight_eq]
  have ht : ∀ x, (x &&& 2570) <<< 3 < 2 ^ 16 := fun x => by
    rw [Nat.shiftLeft_eq]
    have := Nat.and_le_right (n := x) (m := 2570)
    omega
  have hu : ∀ x, (x &&& 204) <<< 6 < 2 ^ 16 := fun x => by
    rw [Nat.shiftLeft_eq]
    have := Nat.and_le_right (n := x) (m := 204)
    omega
  have ht' : ∀ x, (x &&& 2570) < 2 ^ 16 := fun x =>
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hu' : ∀ x, (x &&& 204) < 2 ^ 16 := fun x =>
    lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hy := Nat.xor_lt_two_pow ha (Nat.xor_lt_two_pow (ht' (a ^^^ a >>> 3)) (ht (a ^^^ a >>> 3)))
  exact Nat.xor_lt_two_pow hy (Nat.xor_lt_two_pow (hu' _) (hu _))

theorem one4_lt : one4 < 2 ^ 16 := by decide

theorem pkMat_eq_iff {a b : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) : pkMat 4 a = pkMat 4 b ↔ a = b :=
  ⟨fun h => ofCode_injective ha hb (by rw [ofCode_eq_ofMatrix, h, ← ofCode_eq_ofMatrix]),
    fun h => h ▸ rfl⟩

theorem lt_two {b : ℕ} (h : b < 2) : b = 0 ∨ b = 1 := by omega

@[expose] noncomputable def decE (t : ℕ) : Elt := ⟨Mat.ofCode (fa t), Mat.ofCode (fai t), Nat.beq (fb t) 1⟩

@[expose] def Canon (t : ℕ) : Prop := ∃ a < 2 ^ 16, ∃ ai < 2 ^ 16, ∃ b < 2, t = mkE a ai b

theorem testBit_mkE (a ai b n : ℕ) : (mkE a ai b).testBit n =
    (a.testBit n || (decide (16 ≤ n) && ai.testBit (n - 16)) ||
      (decide (32 ≤ n) && b.testBit (n - 32))) := by
  simp only [mkE, lor_eq, shiftLeft_eq, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_assoc]

theorem fa_mkE {a : ℕ} (ha : a < 2 ^ 16) (ai b : ℕ) : fa (mkE a ai b) = a := by
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [fa, land_eq, Nat.testBit_and, testBit_mkE]
  have h65 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num
  rw [h65, Nat.testBit_two_pow_sub_one]
  by_cases hn : n < 16
  · simp [hn, show ¬ 16 ≤ n by omega, show ¬ 32 ≤ n by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hn]

theorem fai_mkE {a ai : ℕ} (ha : a < 2 ^ 16) (hai : ai < 2 ^ 16) (b : ℕ) : fai (mkE a ai b) = ai := by
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [fai, land_eq, shiftRight_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_mkE]
  have h65 : (65535 : ℕ) = 2 ^ 16 - 1 := by norm_num
  rw [h65, Nat.testBit_two_pow_sub_one]
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  by_cases hn : n < 16
  · simp [hn, show ¬ 32 ≤ 16 + n by omega, show 16 + n - 16 = n by omega]
  · simp only [hn, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hai (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem fb_mkE {a ai b : ℕ} (ha : a < 2 ^ 16) (hai : ai < 2 ^ 16) (hb : b < 2) : fb (mkE a ai b) = b := by
  apply Nat.eq_of_testBit_eq
  intro n
  simp only [fb, land_eq, shiftRight_eq, Nat.testBit_and, Nat.testBit_shiftRight, testBit_mkE]
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hai (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rcases lt_two hb with rfl | rfl
  · simp
  · cases n <;> simp [Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem fa_lt (t : ℕ) : fa t < 2 ^ 16 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem fai_lt (t : ℕ) : fai t < 2 ^ 16 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem fb_lt (t : ℕ) : fb t < 2 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem canon_mkE {a ai b : ℕ} (ha : a < 2 ^ 16) (hai : ai < 2 ^ 16) (hb : b < 2) :
    Canon (mkE a ai b) := ⟨a, ha, ai, hai, b, hb, rfl⟩

theorem decE_mkE {a ai b : ℕ} (ha : a < 2 ^ 16) (hai : ai < 2 ^ 16) (hb : b < 2) :
    decE (mkE a ai b) = ⟨Mat.ofCode a, Mat.ofCode ai, Nat.beq b 1⟩ := by
  rw [decE, fa_mkE ha, fai_mkE ha hai, fb_mkE ha hai hb]

theorem decE_injective {s t : ℕ} (hs : Canon s) (ht : Canon t) (h : decE s = decE t) : s = t := by
  obtain ⟨a, ha, ai, hai, b, hb, rfl⟩ := hs
  obtain ⟨a', ha', ai', hai', b', hb', rfl⟩ := ht
  rw [decE_mkE ha hai hb, decE_mkE ha' hai' hb'] at h
  simp only [Elt.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [ofCode_injective ha ha' h1, ofCode_injective hai hai' h2]
  congr 1
  rcases lt_two hb with rfl | rfl <;> rcases lt_two hb' with rfl | rfl <;>
    simp_all

theorem oneE_eq : oneE = mkE one4 one4 0 := by decide +kernel

theorem decE_oneE : decE oneE = Elt.one := by
  rw [oneE_eq, decE_mkE one4_lt one4_lt (by norm_num), ofCode_one4]
  rfl

theorem canon_oneE : Canon oneE := oneE_eq ▸ canon_mkE one4_lt one4_lt (by norm_num)

theorem canon_mulE (s t : ℕ) : Canon (mulE s t) := by
  unfold mulE
  simp only [letN_eq]
  cases Nat.beq (fb s) 1
  · exact canon_mkE (mul4_lt _ _) (mul4_lt _ _) (fb_lt t)
  · refine canon_mkE (mul4_lt _ _) (mul4_lt _ _) ?_
    have := fb_lt t
    rw [xor_eq]
    rcases lt_two this with h | h <;> rw [h] <;> decide +kernel

theorem decE_mulE (s t : ℕ) : decE (mulE s t) = (decE s).mul (decE t) := by
  have hb := canon_mulE s t
  unfold mulE
  simp only [letN_eq]
  cases hs : Nat.beq (fb s) 1
  · simp only
    rw [decE_mkE (mul4_lt _ _) (mul4_lt _ _) (fb_lt t)]
    simp only [decE, Elt.mul, hs, Bool.false_eq_true, ↓reduceIte, ofCode_mul4, Bool.false_xor]
  · simp only
    have hx : Nat.xor 1 (fb t) < 2 := by
      have := fb_lt t
      rcases lt_two this with h | h <;> rw [h] <;> decide +kernel
    rw [decE_mkE (mul4_lt _ _) (mul4_lt _ _) hx]
    simp only [decE, Elt.mul, hs, ↓reduceIte, ofCode_mul4, ofCode_tr4, Bool.true_xor,
      Elt.mk.injEq, true_and]
    have := fb_lt t
    rcases lt_two this with h | h <;> rw [h] <;> decide +kernel

theorem decE_invE (t : ℕ) : decE (invE t) = (decE t).inv := by
  unfold invE
  cases hs : Nat.beq (fb t) 1
  · simp only
    rw [decE_mkE (fai_lt t) (fa_lt t) (by norm_num)]
    simp only [decE, Elt.inv, hs, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only
    rw [decE_mkE (tr4_lt (fa_lt t)) (tr4_lt (fai_lt t)) (by norm_num)]
    simp only [decE, Elt.inv, hs, ↓reduceIte, ofCode_tr4]
    rfl

theorem validE_iff (t : ℕ) : validE t = (decE t).valid := by
  unfold validE Elt.valid
  simp only [andB_eq, decE, toMatrix_ofCode]
  rw [← pkMat_mul4, ← pkMat_mul4, ← pkMat_one4]
  congr 1
  · rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, pkMat_eq_iff (mul4_lt _ _) one4_lt]
  · rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, pkMat_eq_iff (mul4_lt _ _) one4_lt]

end CFSG.KC.H9Four.Codes

end

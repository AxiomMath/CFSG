module

public import Certificates.Data.RouteCCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteC

@[expose] def bitVec (m x : ℕ) : Fin m → ZMod 2 := fun i => if x.testBit i then 1 else 0

@[expose] def toMat (m p : ℕ) (A : Mat) : Matrix (Fin m) (Fin p) (ZMod 2) :=
  Matrix.of fun i j => bitVec m (A.getD j 0) i

theorem bitVec_zero (m : ℕ) : bitVec m 0 = 0 := by
  funext i
  simp [bitVec]

theorem bitVec_xor (m x y : ℕ) : bitVec m (x ^^^ y) = bitVec m x + bitVec m y := by
  funext i
  simp only [bitVec, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem bitVec_ite (m c : ℕ) (a : Prop) [Decidable a] :
    bitVec m (if a then c else 0) = if a then bitVec m c else 0 := by
  by_cases h : a
  · simp [h]
  · simp [h, bitVec_zero]

theorem mulVec_spec (m : ℕ) : ∀ (A : Mat) (v : ℕ),
    bitVec m (mulVec A v) = (toMat m A.length A).mulVec (bitVec A.length v)
  | [], v => by
    funext i
    simp [mulVec, bitVec_zero, Matrix.mulVec]
  | a :: as, v => by
    funext i
    have ih := congrFun (mulVec_spec m as (v / 2)) i
    rw [mulVec, bitVec_xor, List.length_cons, Pi.add_apply, ih, bitVec_ite]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    have h0 : bitVec (as.length + 1) v 0 = if v % 2 = 1 then 1 else 0 := by
      simp [bitVec, Nat.testBit_zero]
    have hs : ∀ j : Fin as.length,
        bitVec (as.length + 1) v j.succ = bitVec as.length (v / 2) j := by
      intro j
      simp [bitVec, Nat.testBit_succ]
    simp only [hs, h0, toMat, Matrix.of_apply]
    by_cases h : v % 2 = 1 <;> simp [h]

theorem mulVec_zero : ∀ A : Mat, mulVec A 0 = 0
  | [] => rfl
  | a :: as => by simp [mulVec, mulVec_zero as]

theorem getD_map_mulVec (A B : Mat) (j : ℕ) :
    (B.map (mulVec A)).getD j 0 = mulVec A (B.getD j 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases B[j]? <;> simp [mulVec_zero]

theorem toMat_mul (m p q : ℕ) (A B : Mat) (hA : A.length = p) :
    toMat m q (mul A B) = toMat m p A * toMat p q B := by
  subst hA
  ext i j
  have h := congrFun (mulVec_spec m A (B.getD j 0)) i
  simp only [toMat, mul, Matrix.of_apply, Matrix.mul_apply, getD_map_mulVec]
  rw [h]
  simp [Matrix.mulVec, dotProduct, toMat]

theorem toMat_one : toMat 6 6 one = 1 := by decide

@[simp] theorem length_mul (A B : Mat) : (mul A B).length = B.length := by simp [mul]

@[simp] theorem length_one : one.length = 6 := rfl

@[simp] theorem length_chartY (φ : ℕ) : (chartY φ).length = 6 := rfl
@[simp] theorem length_chartD (ψ : ℕ) : (chartD ψ).length = 6 := rfl
@[simp] theorem length_chartT : chartT.length = 6 := rfl

theorem length_pow (A : Mat) (hA : A.length = 6) : ∀ k, (pow A k).length = 6
  | 0 => rfl
  | k + 1 => by simp [pow, length_pow A hA k]

theorem length_gen (φ ψ l : ℕ) : (gen φ ψ l).length = 6 := by
  unfold gen
  split <;> simp

theorem toMat_pow (A : Mat) (hA : A.length = 6) :
    ∀ k, toMat 6 6 (pow A k) = toMat 6 6 A ^ k
  | 0 => by simpa [pow] using toMat_one
  | k + 1 => by
    rw [pow, toMat_mul 6 6 6 A _ hA, toMat_pow A hA k, pow_succ']

theorem getD_add (A B : Mat) (hAB : A.length = B.length) (j : ℕ) :
    (add A B).getD j 0 = A.getD j 0 ^^^ B.getD j 0 := by
  simp only [add, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  by_cases hj : j < A.length
  · have hj' : j < B.length := hAB ▸ hj
    simp [hj, hj']
  · have hj' : ¬ j < B.length := hAB ▸ hj
    simp [hj, hj']

theorem toMat_add (m p : ℕ) (A B : Mat) (hAB : A.length = B.length) :
    toMat m p (add A B) = toMat m p A + toMat m p B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.add_apply, getD_add A B hAB, bitVec_xor, Pi.add_apply]

@[expose] def Bnd (A : Mat) : Prop := ∀ x ∈ A, x < 64

theorem bnd_mulVec : ∀ (A : Mat), Bnd A → ∀ v, mulVec A v < 64
  | [], _, v => by simp [mulVec]
  | a :: as, hA, v => by
    have ha : a < 64 := hA a (List.mem_cons_self ..)
    have has : Bnd as := fun x hx => hA x (List.mem_cons_of_mem _ hx)
    have h2 := bnd_mulVec as has (v / 2)
    simp only [mulVec]
    have : (if v % 2 = 1 then a else 0) < 64 := by split <;> omega
    exact Nat.xor_lt_two_pow (n := 6) this h2

theorem bnd_mul (A B : Mat) (hA : Bnd A) : Bnd (mul A B) := by
  intro x hx
  simp only [mul, List.mem_map] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact bnd_mulVec A hA v

theorem bnd_one : Bnd one := by
  intro x hx
  simp only [one, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem bnd_add : ∀ (A B : Mat), Bnd A → Bnd B → Bnd (add A B)
  | [], _, _, _ => by
    intro x hx
    simp [add] at hx
  | _ :: _, [], _, _ => by
    intro x hx
    simp [add] at hx
  | a :: as, b :: bs, hA, hB => by
    intro x hx
    simp only [add, List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.xor_lt_two_pow (n := 6) (hA a (List.mem_cons_self ..))
        (hB b (List.mem_cons_self ..))
    · exact bnd_add as bs (fun x hx => hA x (List.mem_cons_of_mem _ hx))
        (fun x hx => hB x (List.mem_cons_of_mem _ hx)) x (by simpa [add] using hx)

theorem bnd_chartY (φ : ℕ) : Bnd (chartY φ) := by
  intro x hx
  simp only [chartY, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem bnd_chartD (ψ : ℕ) : Bnd (chartD ψ) := by
  intro x hx
  simp only [chartD, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem bnd_chartT : Bnd chartT := by
  intro x hx
  simp only [chartT, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem bnd_gen (φ ψ l : ℕ) : Bnd (gen φ ψ l) := by
  unfold gen
  split
  · exact bnd_chartY φ
  · exact bnd_chartD ψ
  · exact bnd_chartT
  · exact bnd_mul _ _ (bnd_chartY φ)
  · exact bnd_mul _ _ (bnd_chartD ψ)

theorem bnd_pow (A : Mat) (hA : Bnd A) : ∀ k, Bnd (pow A k)
  | 0 => bnd_one
  | _ + 1 => bnd_mul _ _ hA

theorem bnd_foldl (φ ψ : ℕ) : ∀ (w : List ℕ) (A : Mat), Bnd A →
    Bnd (w.foldl (fun acc l => mul acc (gen φ ψ l)) A)
  | [], _, hA => hA
  | _ :: w, _, hA => bnd_foldl φ ψ w _ (bnd_mul _ _ hA)

theorem bnd_evalW (φ ψ : ℕ) (w : List ℕ) : Bnd (evalW φ ψ w) := bnd_foldl φ ψ w _ bnd_one

theorem length_foldl (φ ψ : ℕ) : ∀ (w : List ℕ) (A : Mat), A.length = 6 →
    (w.foldl (fun acc l => mul acc (gen φ ψ l)) A).length = 6
  | [], _, hA => hA
  | _ :: w, _, _ => length_foldl φ ψ w _ (by simp [length_gen])

theorem length_evalW (φ ψ : ℕ) (w : List ℕ) : (evalW φ ψ w).length = 6 :=
  length_foldl φ ψ w _ length_one

theorem toMat_foldl (φ ψ : ℕ) : ∀ (w : List ℕ) (A : Mat), A.length = 6 →
    toMat 6 6 (w.foldl (fun acc l => mul acc (gen φ ψ l)) A) =
      w.foldl (fun acc l => acc * toMat 6 6 (gen φ ψ l)) (toMat 6 6 A)
  | [], _, _ => rfl
  | _ :: w, A, hA => by
    simp only [List.foldl_cons]
    rw [toMat_foldl φ ψ w _ (by simp [length_gen]), toMat_mul 6 6 6 A _ hA]

theorem foldl_mul_intertwine {n : ℕ} (E : Matrix (Fin n) (Fin 6) (ZMod 2))
    (Gm : ℕ → Matrix (Fin n) (Fin n) (ZMod 2)) (φ ψ : ℕ)
    (hG : ∀ l, Gm l * E = E * toMat 6 6 (gen φ ψ l)) :
    ∀ (w : List ℕ) (A : Mat) (X : Matrix (Fin n) (Fin n) (ZMod 2)), A.length = 6 →
      X * E = E * toMat 6 6 A →
      (w.foldl (fun acc l => acc * Gm l) X) * E =
        E * toMat 6 6 (w.foldl (fun acc l => mul acc (gen φ ψ l)) A)
  | [], _, _, _, h => h
  | l :: w, A, X, hA, h => by
    simp only [List.foldl_cons]
    refine foldl_mul_intertwine E Gm φ ψ hG w _ _ (by simp [length_gen]) ?_
    rw [Matrix.mul_assoc, hG l, ← Matrix.mul_assoc, h, Matrix.mul_assoc,
      toMat_mul 6 6 6 A _ hA]

theorem vec_eq_of_add_eq_zero {n : ℕ} {u v : Fin n → ZMod 2} (h : u + v = 0) : u = v := by
  funext i
  have := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  revert this
  generalize u i = a
  generalize v i = b
  revert a b
  decide

@[expose] def KRel {n : ℕ} (E : Matrix (Fin n) (Fin 6) (ZMod 2)) (Kels : List ℕ) : Prop :=
  (∀ x ∈ Kels, E.mulVec (bitVec 6 x) = 0) ∧
    ∀ x, x < 64 → E.mulVec (bitVec 6 x) = 0 → x ∈ Kels

theorem getD_of_lt (A : List ℕ) (j : ℕ) (hj : j < A.length) : A.getD j 0 = A[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem getD_mem (A : List ℕ) (j : ℕ) (hj : j < A.length) : A.getD j 0 ∈ A := by
  rw [getD_of_lt A j hj]
  exact List.getElem_mem hj

theorem mem_add_iff (A B : Mat) (hAB : A.length = B.length) (x : ℕ) :
    x ∈ add A B ↔ ∃ j, j < A.length ∧ x = A.getD j 0 ^^^ B.getD j 0 := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have hlen : (add A B).length = A.length := by simp [add, hAB]
    refine ⟨j, hlen ▸ hj, ?_⟩
    rw [← getD_add A B hAB j]
    simp [List.getD_eq_getElem?_getD, hj]
  · rintro ⟨j, hj, rfl⟩
    rw [← getD_add A B hAB j]
    have hlen : (add A B).length = A.length := by simp [add, hAB]
    have : j < (add A B).length := hlen ▸ hj
    rw [getD_of_lt _ _ this]
    exact List.getElem_mem this

theorem mul_toMat_apply {n : ℕ} (E : Matrix (Fin n) (Fin 6) (ZMod 2)) (A : Mat) (i : Fin n)
    (j : Fin 6) : (E * toMat 6 6 A) i j = E.mulVec (bitVec 6 (A.getD j 0)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, toMat]

theorem KRel.eqMod_iff {n : ℕ} {E : Matrix (Fin n) (Fin 6) (ZMod 2)} {Kels : List ℕ}
    (hK : KRel E Kels) (A B : Mat) (hA : A.length = 6) (hB : B.length = 6) (hbA : Bnd A)
    (hbB : Bnd B) :
    eqMod Kels A B = true ↔ E * toMat 6 6 A = E * toMat 6 6 B := by
  have hAB : A.length = B.length := by rw [hA, hB]
  have col : ∀ j : ℕ, j < 6 → (E.mulVec (bitVec 6 (A.getD j 0)) = E.mulVec (bitVec 6 (B.getD j 0)) ↔
      (A.getD j 0 ^^^ B.getD j 0) ∈ Kels) := by
    intro j hj
    have hA' : A.getD j 0 < 64 := hbA _ (getD_mem A j (by rw [hA]; exact hj))
    have hB' : B.getD j 0 < 64 := hbB _ (getD_mem B j (by rw [hB]; exact hj))
    have hx : A.getD j 0 ^^^ B.getD j 0 < 64 := Nat.xor_lt_two_pow (n := 6) hA' hB'
    constructor
    · intro h
      apply hK.2 _ hx
      rw [bitVec_xor, Matrix.mulVec_add, h]
      funext i
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize E.mulVec (bitVec 6 (B.getD j 0)) i = b
      revert b
      decide
    · intro h
      have h0 := hK.1 _ h
      rw [bitVec_xor, Matrix.mulVec_add] at h0
      exact vec_eq_of_add_eq_zero h0
  constructor
  · intro h
    ext i j
    rw [mul_toMat_apply, mul_toMat_apply]
    have hmem : (A.getD j 0 ^^^ B.getD j 0) ∈ add A B := by
      rw [mem_add_iff A B hAB]
      exact ⟨j, by rw [hA]; exact j.2, rfl⟩
    simp only [eqMod, List.all_eq_true, List.contains_iff_mem] at h
    rw [(col j j.2).2 (h _ hmem)]
  · intro h
    simp only [eqMod, List.all_eq_true, List.contains_iff_mem]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (mem_add_iff A B hAB x).mp hx
    have hj6 : j < 6 := hA ▸ hj
    refine (col j hj6).1 ?_
    funext i
    have := congrFun (congrFun h i) ⟨j, hj6⟩
    rw [mul_toMat_apply, mul_toMat_apply] at this
    exact this

@[expose] def spanBits (m : ℕ) (L : List ℕ) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) (bitVec m '' {x | x ∈ L})

theorem mem_spanBits_of_mem {m : ℕ} {L : List ℕ} {x : ℕ} (hx : x ∈ L) :
    bitVec m x ∈ spanBits m L :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem mem_spanBits_of_mem_spanList {m : ℕ} : ∀ {L : List ℕ} {x : ℕ}, x ∈ spanList L →
    bitVec m x ∈ spanBits m L
  | [], x, hx => by
    simp only [spanList, List.mem_singleton] at hx
    subst hx
    rw [bitVec_zero]
    exact Submodule.zero_mem _
  | b :: bs, x, hx => by
    simp only [spanList, List.mem_append, List.mem_map] at hx
    have hle : spanBits m bs ≤ spanBits m (b :: bs) :=
      Submodule.span_mono (Set.image_mono fun y hy => List.mem_cons_of_mem _ hy)
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hle (mem_spanBits_of_mem_spanList hx)
    · rw [bitVec_xor]
      exact Submodule.add_mem _ (hle (mem_spanBits_of_mem_spanList hy))
        (mem_spanBits_of_mem (List.mem_cons_self ..))

theorem toMat_mulVec_mem_spanBits (A : Mat) (hA : A.length = 6) (Wb : List ℕ)
    (h : ∀ b ∈ Wb, mulVec A b ∈ spanList Wb) :
    ∀ z ∈ spanBits 6 Wb, (toMat 6 6 A).mulVec z ∈ spanBits 6 Wb := by
  intro z hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨b, hb, rfl⟩
    have := mulVec_spec 6 A b
    rw [hA] at this
    rw [← this]
    exact mem_spanBits_of_mem_spanList (h b hb)
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

theorem toMat_mulVec_mem_of_cols {p : ℕ} (A : Mat) (S : Submodule (ZMod 2) (Fin 6 → ZMod 2))
    (h : ∀ j : Fin p, bitVec 6 (A.getD j 0) ∈ S) (z : Fin p → ZMod 2) :
    (toMat 6 p A).mulVec z ∈ S := by
  have : (toMat 6 p A).mulVec z = ∑ j : Fin p, z j • bitVec 6 (A.getD j 0) := by
    funext i
    simp [Matrix.mulVec, dotProduct, toMat, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h j)

theorem bitVec_eq_zero_iff {m x : ℕ} (hx : x < 2 ^ m) : bitVec m x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.zero_testBit]
    by_cases hi : i < m
    · have := congrFun h ⟨i, hi⟩
      simp only [bitVec, Pi.zero_apply] at this
      by_contra hb
      simp only [Bool.not_eq_false] at hb
      simp [hb] at this
    · simp only [not_lt] at hi
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi))
  · rintro rfl
    exact bitVec_zero m

theorem bitVec_surj : ∀ {m : ℕ} (z : Fin m → ZMod 2), ∃ x, x < 2 ^ m ∧ bitVec m x = z
  | 0, z => ⟨0, by norm_num, funext fun i => i.elim0⟩
  | m + 1, z => by
    obtain ⟨x', hx', hbx'⟩ := bitVec_surj (m := m) fun i => z i.succ
    have hz0 : (z 0).val < 2 := (z 0).val_lt
    refine ⟨(z 0).val + 2 * x', ?_, ?_⟩
    · rw [pow_succ]
      omega
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [bitVec, Fin.val_zero, Nat.testBit_zero]
        have h2 : ((z 0).val + 2 * x') % 2 = (z 0).val := by omega
        rw [h2]
        generalize z 0 = a
        revert a
        decide
      · simp only [bitVec, Fin.val_succ, Nat.testBit_succ]
        have h2 : ((z 0).val + 2 * x') / 2 = x' := by omega
        rw [h2]
        exact congrFun hbx' j

theorem zero_mem_spanList : ∀ L : List ℕ, 0 ∈ spanList L
  | [] => by simp [spanList]
  | b :: bs => by
    simp only [spanList, List.mem_append]
    exact Or.inl (zero_mem_spanList bs)

theorem mem_spanList_of_mem : ∀ {L : List ℕ} {b : ℕ}, b ∈ L → b ∈ spanList L
  | [], _, h => by simp at h
  | c :: cs, b, h => by
    simp only [spanList, List.mem_append, List.mem_map]
    rcases List.mem_cons.mp h with rfl | hb
    · exact Or.inr ⟨0, by simp [zero_mem_spanList cs], Nat.zero_xor _⟩
    · exact Or.inl (by
        have := mem_spanList_of_mem hb
        exact this)

theorem bitVec_inj {m x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) (h : bitVec m x = bitVec m y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · have := congrFun h ⟨i, hi⟩
    simp only [bitVec] at this
    cases hxi : x.testBit i <;> cases hyi : y.testBit i <;> simp [hxi, hyi] at this ⊢
  · simp only [not_lt] at hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hi))]

theorem mem_spanList_of_mem_spanBits {m : ℕ} : ∀ {L : List ℕ}, (∀ b ∈ L, b < 2 ^ m) →
    ∀ {x : ℕ}, x < 2 ^ m → bitVec m x ∈ spanBits m L → x ∈ spanList L
  | [], _, x, hx, h => by
    have hset : bitVec m '' {x | x ∈ ([] : List ℕ)} = ∅ := by
      ext z
      simp
    unfold spanBits at h
    rw [hset, Submodule.span_empty, Submodule.mem_bot] at h
    have := (bitVec_eq_zero_iff hx).mp h
    simp [spanList, this]
  | b :: bs, hb, x, hx, h => by
    have hset : bitVec m '' {x | x ∈ b :: bs} = insert (bitVec m b) (bitVec m '' {x | x ∈ bs}) := by
      ext z
      simp [eq_comm]
    unfold spanBits at h
    rw [hset, Submodule.mem_span_insert] at h
    obtain ⟨a, z, hz, hzx⟩ := h
    obtain ⟨x', hx', rfl⟩ := bitVec_surj z
    have hbs : ∀ c ∈ bs, c < 2 ^ m := fun c hc => hb c (List.mem_cons_of_mem _ hc)
    have hx'mem : x' ∈ spanList bs := mem_spanList_of_mem_spanBits hbs hx' hz
    have ha : a = 0 ∨ a = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) a
    simp only [spanList, List.mem_append, List.mem_map]
    rcases ha with rfl | rfl
    · rw [zero_smul, zero_add] at hzx
      exact Or.inl ((bitVec_inj hx hx' hzx) ▸ hx'mem)
    · rw [one_smul, ← bitVec_xor] at hzx
      have hlt : b ^^^ x' < 2 ^ m := Nat.xor_lt_two_pow (hb b (List.mem_cons_self ..)) hx'
      have := bitVec_inj hx hlt hzx
      exact Or.inr ⟨x', hx'mem, by rw [this, Nat.xor_comm]⟩

end CFSG.CGT.PushingUpLit.CGT6.RouteC

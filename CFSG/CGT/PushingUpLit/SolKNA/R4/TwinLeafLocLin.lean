module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocCrit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocLinCheck
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open Matrix

theorem sumLt_cast {R : Type*} [Semiring R] (n : ℕ) (f : ℕ → ℕ) :
    ((sumLt n f : ℕ) : R) = ∑ l : Fin n, ((f l : ℕ) : R) := by
  rw [sumLt, Fin.sum_univ_eq_sum_range (fun l => ((f l : ℕ) : R)) n]
  induction n with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
      Nat.cast_add, ih]; simp

section Spec

variable (n : ℕ) (K : Type*) [Field K] [CharP K 3]

@[expose] def mA (x : Array ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => ((eA n x i j : ℕ) : K)

@[expose] def mB (x : Array ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => ((eB n x i j : ℕ) : K)

variable {n}

theorem index_div_mod {i j : ℕ} (hn : 0 < n) (hj : j < n) :
    (n * i + j) / n = i ∧ (n * i + j) % n = j := by
  constructor
  · rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

theorem lt_mul_of_lt {i j : ℕ} (hi : i < n) (hj : j < n) : n * i + j < n * n := by
  calc n * i + j < n * i + n := by omega
    _ = n * (i + 1) := by ring
    _ ≤ n * n := Nat.mul_le_mul_left n hi

theorem size_eltMul (x y : Array ℕ) : (eltMul n x y).size = 2 * (n * n) + 1 := by
  simp [eltMul]

theorem eltMul_get {x y : Array ℕ} {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltMul n x y)[k]! = if k < n * n then
      sumLt n (fun l => eA n x (k / n) l *
        (if eE n x = 1 then eB n y l (k % n) else eA n y l (k % n))) % 3
    else if k < 2 * (n * n) then
      sumLt n (fun l => eB n x ((k - n * n) / n) l *
        (if eE n x = 1 then eA n y l ((k - n * n) % n) else eB n y l ((k - n * n) % n))) % 3
    else (eE n x + eE n y) % 2 := by
  rw [getElem!_pos _ _ (by rw [size_eltMul]; exact hk)]
  simp [eltMul]

theorem mA_eltMul (hn : 0 < n) (x y : Array ℕ) :
    mA n K (eltMul n x y) = mA n K x * (if eE n x = 1 then mB n K y else mA n K y) := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  have hget : eA n (eltMul n x y) i j = sumLt n (fun l => eA n x (i : ℕ) l *
      (if eE n x = 1 then eB n y l (j : ℕ) else eA n y l (j : ℕ))) % 3 := by
    rw [eA, eltMul_get (by omega), if_pos hk, hd, hm]
  simp only [mA, Matrix.of_apply]
  rw [hget, ← CharP.natCast_eq_natCast_mod K 3, sumLt_cast]
  by_cases h1 : eE n x = 1
  · simp [h1, Matrix.mul_apply, mB]
  · simp [h1, Matrix.mul_apply]

theorem mB_eltMul (hn : 0 < n) (x y : Array ℕ) :
    mB n K (eltMul n x y) = mB n K x * (if eE n x = 1 then mA n K y else mB n K y) := by
  ext i j
  have hk : n * n + (n * (i : ℕ) + (j : ℕ)) < 2 * (n * n) := by
    have := lt_mul_of_lt (n := n) i.2 j.2
    omega
  have hk' : ¬ (n * n + (n * (i : ℕ) + (j : ℕ)) < n * n) := by omega
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  have hsub : n * n + (n * (i : ℕ) + (j : ℕ)) - n * n = n * (i : ℕ) + (j : ℕ) := by omega
  have hget : eB n (eltMul n x y) i j = sumLt n (fun l => eB n x (i : ℕ) l *
      (if eE n x = 1 then eA n y l (j : ℕ) else eB n y l (j : ℕ))) % 3 := by
    rw [eB, eltMul_get (by omega), if_neg hk', if_pos hk, hsub, hd, hm]
  simp only [mB, Matrix.of_apply]
  rw [hget, ← CharP.natCast_eq_natCast_mod K 3, sumLt_cast]
  by_cases h1 : eE n x = 1
  · simp [h1, Matrix.mul_apply, mA]
  · simp [h1, Matrix.mul_apply]

theorem eE_eltMul (hn : 0 < n) (x y : Array ℕ) :
    eE n (eltMul n x y) = (eE n x + eE n y) % 2 := by
  have h1 : ¬ (2 * (n * n) < n * n) := by
    have := Nat.mul_pos hn hn
    omega
  rw [eE, eltMul_get (by omega), if_neg h1, if_neg (lt_irrefl _)]

end Spec

section Spec2

variable {n : ℕ} (K : Type*) [Field K] [CharP K 3]

theorem size_eltOne : (eltOne n).size = 2 * (n * n) + 1 := by simp [eltOne]

theorem size_eltInv (x : Array ℕ) : (eltInv n x).size = 2 * (n * n) + 1 := by simp [eltInv]

theorem eltOne_get {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltOne n)[k]! = if k < 2 * (n * n) then
      (if (k % (n * n)) / n = (k % (n * n)) % n then 1 else 0) else 0 := by
  rw [getElem!_pos _ _ (by rw [size_eltOne]; exact hk)]
  simp [eltOne]

theorem eltInv_get {x : Array ℕ} {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltInv n x)[k]! = if k < n * n then
      (if eE n x = 1 then eA n x (k % n) (k / n) else eB n x (k % n) (k / n))
    else if k < 2 * (n * n) then
      (if eE n x = 1 then eB n x ((k - n * n) % n) ((k - n * n) / n)
        else eA n x ((k - n * n) % n) ((k - n * n) / n))
    else eE n x := by
  rw [getElem!_pos _ _ (by rw [size_eltInv]; exact hk)]
  simp [eltInv]

theorem mA_eltOne (hn : 0 < n) : mA n K (eltOne n) = 1 := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  simp only [mA, Matrix.of_apply, eA]
  rw [eltOne_get (by omega), if_pos (by omega), Nat.mod_eq_of_lt hk, hd, hm]
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij]
  · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [Matrix.one_apply, hij, this]

theorem mB_eltOne (hn : 0 < n) : mB n K (eltOne n) = 1 := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  simp only [mB, Matrix.of_apply, eB]
  rw [eltOne_get (by omega), if_pos (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt hk, hd, hm]
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij]
  · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [Matrix.one_apply, hij, this]

theorem eE_eltOne (hn : 0 < n) : eE n (eltOne n) = 0 := by
  rw [eE, eltOne_get (by omega), if_neg (lt_irrefl _)]

theorem mA_eltInv (hn : 0 < n) (x : Array ℕ) :
    mA n K (eltInv n x) = if eE n x = 1 then (mA n K x)ᵀ else (mB n K x)ᵀ := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  simp only [mA, Matrix.of_apply, eA]
  have := eltInv_get (n := n) (x := x) (k := n * (i : ℕ) + (j : ℕ)) (by omega)
  rw [this, if_pos hk, hd, hm]
  by_cases h1 : eE n x = 1
  · simp [h1, mA, eA]
  · simp [h1, mB, eB]

theorem mB_eltInv (hn : 0 < n) (x : Array ℕ) :
    mB n K (eltInv n x) = if eE n x = 1 then (mB n K x)ᵀ else (mA n K x)ᵀ := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  have hk2 : n * n + (n * (i : ℕ) + (j : ℕ)) < 2 * (n * n) := by omega
  have hk' : ¬ (n * n + (n * (i : ℕ) + (j : ℕ)) < n * n) := by omega
  have hsub : n * n + (n * (i : ℕ) + (j : ℕ)) - n * n = n * (i : ℕ) + (j : ℕ) := by omega
  simp only [mB, Matrix.of_apply, eB]
  have := eltInv_get (n := n) (x := x) (k := n * n + (n * (i : ℕ) + (j : ℕ))) (by omega)
  rw [this, if_neg hk', if_pos hk2, hsub, hd, hm]
  by_cases h1 : eE n x = 1
  · simp [h1, mB, eB]
  · simp [h1, mA, eA]

theorem eE_eltInv (hn : 0 < n) (x : Array ℕ) : eE n (eltInv n x) = eE n x := by
  have h1 : ¬ (2 * (n * n) < n * n) := by
    have := Nat.mul_pos hn hn
    omega
  rw [eE, eltInv_get (by omega), if_neg h1, if_neg (lt_irrefl _)]

theorem cast_eq_iff {a b : ℕ} (hb : b < 3) : ((a : ℕ) : K) = (b : K) ↔ a % 3 = b := by
  rw [CharP.natCast_eq_natCast K 3]
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt hb]

theorem mul_entry (x : Array ℕ) (i j : Fin n) :
    (mA n K x * (mB n K x)ᵀ) i j = ((sumLt n (fun l => eA n x i l * eB n x j l) : ℕ) : K) := by
  simp [Matrix.mul_apply, mA, mB, sumLt_cast]

theorem eltValid_iff (x : Array ℕ) :
    eltValid n x = true ↔ x.size = 2 * (n * n) + 1 ∧ (∀ k < 2 * (n * n), x[k]! < 3) ∧
      x[2 * (n * n)]! < 2 ∧ mA n K x * (mB n K x)ᵀ = 1 := by
  simp only [eltValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    ext i j
    rw [mul_entry, CharP.natCast_eq_natCast_mod K 3, h i i.2 j j.2, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, this]
  · intro hM i hi j hj
    have := congrFun (congrFun hM ⟨i, hi⟩) ⟨j, hj⟩
    rw [mul_entry, Matrix.one_apply] at this
    by_cases hij : i = j
    · have h1 : ((sumLt n (fun l => eA n x i l * eB n x j l) : ℕ) : K) = ((1 : ℕ) : K) := by
        simpa [hij] using this
      rw [if_pos hij]
      exact (cast_eq_iff K (b := 1) (by norm_num)).1 h1
    · have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
      have h0 : ((sumLt n (fun l => eA n x i l * eB n x j l) : ℕ) : K) = ((0 : ℕ) : K) := by
        simpa [hne] using this
      rw [if_neg hij]
      exact (cast_eq_iff K (b := 0) (by norm_num)).1 h0

theorem eA_lt {x : Array ℕ} (h : ∀ k < 2 * (n * n), x[k]! < 3) {i j : ℕ} (hi : i < n)
    (hj : j < n) : eA n x i j < 3 := by
  have := lt_mul_of_lt (n := n) hi hj
  exact h _ (by omega)

theorem eB_lt {x : Array ℕ} (h : ∀ k < 2 * (n * n), x[k]! < 3) {i j : ℕ} (hi : i < n)
    (hj : j < n) : eB n x i j < 3 := by
  have := lt_mul_of_lt (n := n) hi hj
  exact h _ (by omega)

theorem eltValid_eltOne (hn : 0 < n) : eltValid n (eltOne n) = true := by
  rw [eltValid_iff (ZMod 3)]
  refine ⟨size_eltOne, ?_, ?_, ?_⟩
  · intro k hk
    rw [eltOne_get (by omega), if_pos hk]
    split_ifs <;> norm_num
  · rw [eltOne_get (by omega), if_neg (lt_irrefl _)]
    norm_num
  · rw [mA_eltOne (ZMod 3) hn, mB_eltOne (ZMod 3) hn, Matrix.transpose_one, Matrix.mul_one]

theorem mB_mul_transpose {x : Array ℕ} (h : mA n K x * (mB n K x)ᵀ = 1) :
    mB n K x * (mA n K x)ᵀ = 1 := by
  have := congrArg Matrix.transpose h
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem eltValid_eltMul (hn : 0 < n) {x y : Array ℕ} (hx : eltValid n x = true)
    (hy : eltValid n y = true) : eltValid n (eltMul n x y) = true := by
  rw [eltValid_iff (ZMod 3)] at hx hy ⊢
  obtain ⟨hxs, hxb, hxe, hxm⟩ := hx
  obtain ⟨hys, hyb, hye, hym⟩ := hy
  refine ⟨size_eltMul x y, ?_, ?_, ?_⟩
  · intro k hk
    rw [eltMul_get (by omega)]
    by_cases h1 : k < n * n
    · rw [if_pos h1]; exact Nat.mod_lt _ (by norm_num)
    · rw [if_neg h1, if_pos hk]; exact Nat.mod_lt _ (by norm_num)
  · have h1 : ¬ (2 * (n * n) < n * n) := by
      have := Nat.mul_pos hn hn
      omega
    rw [eltMul_get (by omega), if_neg h1, if_neg (lt_irrefl _)]
    exact Nat.mod_lt _ (by norm_num)
  · rw [mA_eltMul (ZMod 3) hn, mB_eltMul (ZMod 3) hn]
    by_cases h1 : eE n x = 1
    · rw [if_pos h1, if_pos h1, Matrix.transpose_mul]
      calc mA n (ZMod 3) x * mB n (ZMod 3) y * ((mA n (ZMod 3) y)ᵀ * (mB n (ZMod 3) x)ᵀ) =
          mA n (ZMod 3) x * (mB n (ZMod 3) y * (mA n (ZMod 3) y)ᵀ) * (mB n (ZMod 3) x)ᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [mB_mul_transpose (ZMod 3) hym, Matrix.mul_one]; exact hxm
    · rw [if_neg h1, if_neg h1, Matrix.transpose_mul]
      calc mA n (ZMod 3) x * mA n (ZMod 3) y * ((mB n (ZMod 3) y)ᵀ * (mB n (ZMod 3) x)ᵀ) =
          mA n (ZMod 3) x * (mA n (ZMod 3) y * (mB n (ZMod 3) y)ᵀ) * (mB n (ZMod 3) x)ᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hym, Matrix.mul_one]; exact hxm

theorem eltValid_eltInv (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) :
    eltValid n (eltInv n x) = true := by
  rw [eltValid_iff (ZMod 3)] at hx ⊢
  obtain ⟨hxs, hxb, hxe, hxm⟩ := hx
  refine ⟨size_eltInv x, ?_, ?_, ?_⟩
  · intro k hk
    rw [eltInv_get (by omega)]
    by_cases h1 : k < n * n
    · have hd : k / n < n := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h1)
      have hm : k % n < n := Nat.mod_lt _ hn
      rw [if_pos h1]
      split_ifs
      · exact eA_lt hxb hm hd
      · exact eB_lt hxb hm hd
    · have h2 : k - n * n < n * n := by omega
      have hd : (k - n * n) / n < n := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      have hm : (k - n * n) % n < n := Nat.mod_lt _ hn
      rw [if_neg h1, if_pos hk]
      split_ifs
      · exact eB_lt hxb hm hd
      · exact eA_lt hxb hm hd
  · have h1 : ¬ (2 * (n * n) < n * n) := by
      have := Nat.mul_pos hn hn
      omega
    rw [eltInv_get (by omega), if_neg h1, if_neg (lt_irrefl _)]
    exact hxe
  · rw [mA_eltInv (ZMod 3) hn, mB_eltInv (ZMod 3) hn]
    have hc : (mB n (ZMod 3) x)ᵀ * mA n (ZMod 3) x = 1 := mul_eq_one_comm.1 hxm
    have hc' : (mA n (ZMod 3) x)ᵀ * mB n (ZMod 3) x = 1 := mul_eq_one_comm.1 (mB_mul_transpose (ZMod 3) hxm)
    by_cases h1 : eE n x = 1
    · rw [if_pos h1, if_pos h1, Matrix.transpose_transpose]
      exact hc'
    · rw [if_neg h1, if_neg h1, Matrix.transpose_transpose]
      exact hc

end Spec2

section Ev

variable (n : ℕ) (K : Type) [Field K] [CharP K 3]

@[expose] noncomputable def unitA (x : Array ℕ) : GL (Fin n) K :=
  if h : eltValid n x = true then
    ⟨mA n K x, (mB n K x)ᵀ, ((eltValid_iff K x).1 h).2.2.2,
      mul_eq_one_comm.1 ((eltValid_iff K x).1 h).2.2.2⟩
  else 1

@[expose] noncomputable def ev (x : Array ℕ) : MulAut (projectiveSL n K) :=
  conjAut n K (unitA n K x) * dualAut n K ^ (eE n x)

variable {n K}

theorem unitA_val {x : Array ℕ} (h : eltValid n x = true) :
    ((unitA n K x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = mA n K x := by
  unfold unitA
  rw [dif_pos h]

theorem unitA_inv_val {x : Array ℕ} (h : eltValid n x = true) :
    (((unitA n K x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (mB n K x)ᵀ := by
  unfold unitA
  rw [dif_pos h]
  rfl

theorem eE_lt_two {x : Array ℕ} (h : eltValid n x = true) : eE n x < 2 :=
  ((eltValid_iff (ZMod 3) x).1 h).2.2.1

theorem dualAut_mul_self' : dualAut n K * dualAut n K = 1 := by
  obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
  exact hdd

theorem unitA_eltMul (hn : 0 < n) {x y : Array ℕ} (hx : eltValid n x = true)
    (hy : eltValid n y = true) :
    unitA n K (eltMul n x y) = unitA n K x *
      (if eE n x = 1 then Matrix.GeneralLinearGroup.inverseTranspose (unitA n K y)
        else unitA n K y) := by
  apply Units.ext
  rw [unitA_val (eltValid_eltMul (n := n) hn hx hy), Units.val_mul, unitA_val hx,
    mA_eltMul K hn]
  by_cases h1 : eE n x = 1
  · rw [if_pos h1, if_pos h1, Matrix.GeneralLinearGroup.coe_inverseTranspose, unitA_inv_val hy,
      Matrix.transpose_transpose]
  · rw [if_neg h1, if_neg h1, unitA_val hy]

theorem ev_eltMul (hn : 0 < n) {x y : Array ℕ} (hx : eltValid n x = true)
    (hy : eltValid n y = true) : ev n K (eltMul n x y) = ev n K x * ev n K y := by
  have hxe := eE_lt_two hx
  have hye := eE_lt_two hy
  have hδ := dualAut_mul_self' (n := n) (K := K)
  have hcomm : ∀ A : GL (Fin n) K, dualAut n K * conjAut n K A =
      conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose A) * dualAut n K :=
    fun A => dualAut_mul_conjAut A
  unfold ev
  rw [eE_eltMul hn, unitA_eltMul hn hx hy, map_mul]
  rcases (by omega : eE n x = 0 ∨ eE n x = 1) with h0 | h1
  · rcases (by omega : eE n y = 0 ∨ eE n y = 1) with k0 | k1
    · simp [h0, k0]
    · simp [h0, k1, mul_assoc]
  · rcases (by omega : eE n y = 0 ∨ eE n y = 1) with k0 | k1
    · simp only [h1, k0, if_true, map_mul]
      calc conjAut n K (unitA n K x) *
            conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose (unitA n K y)) *
            dualAut n K ^ ((1 + 0) % 2) =
          conjAut n K (unitA n K x) *
            (conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose (unitA n K y)) *
              dualAut n K) := by simp [mul_assoc]
        _ = conjAut n K (unitA n K x) * (dualAut n K * conjAut n K (unitA n K y)) := by
          rw [hcomm]
        _ = _ := by simp [mul_assoc]
    · simp only [h1, k1, if_true, map_mul]
      calc conjAut n K (unitA n K x) *
            conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose (unitA n K y)) *
            dualAut n K ^ ((1 + 1) % 2) =
          conjAut n K (unitA n K x) *
            (conjAut n K (Matrix.GeneralLinearGroup.inverseTranspose (unitA n K y)) *
              dualAut n K * dualAut n K) := by
            simp [mul_assoc, hδ]
        _ = conjAut n K (unitA n K x) * (dualAut n K * conjAut n K (unitA n K y) *
            dualAut n K) := by rw [hcomm]
        _ = _ := by simp [mul_assoc, pow_one]

theorem ev_eltOne (hn : 0 < n) : ev n K (eltOne n) = 1 := by
  have hu : unitA n K (eltOne n) = 1 := by
    apply Units.ext
    rw [unitA_val (eltValid_eltOne (n := n) hn), mA_eltOne K hn]
    rfl
  unfold ev
  rw [hu, eE_eltOne hn]
  simp

theorem ev_eltInv (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) :
    ev n K (eltInv n x) = (ev n K x)⁻¹ := by
  have hxi := eltValid_eltInv (n := n) hn hx
  have hxm := ((eltValid_iff K x).1 hx).2.2.2
  have hz : ev n K (eltMul n x (eltInv n x)) = 1 := by
    have hzv := eltValid_eltMul (n := n) hn hx hxi
    have hu : unitA n K (eltMul n x (eltInv n x)) = 1 := by
      apply Units.ext
      rw [unitA_val hzv, mA_eltMul K hn, mA_eltInv K hn]
      by_cases h1 : eE n x = 1
      · rw [if_pos h1, mB_eltInv K hn, if_pos h1, Units.val_one]
        exact hxm
      · rw [if_neg h1, if_neg h1, Units.val_one]
        exact hxm
    unfold ev
    rw [hu, eE_eltMul hn, eE_eltInv hn]
    have := eE_lt_two hx
    have h2 : (eE n x + eE n x) % 2 = 0 := by omega
    rw [h2]
    simp
  rw [ev_eltMul hn hx hxi] at hz
  exact eq_inv_of_mul_eq_one_right hz

theorem eltValid_ePow (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) (m : ℕ) :
    eltValid n (ePow n x m) = true := by
  induction m with
  | zero => exact eltValid_eltOne (n := n) hn
  | succ m ih => exact eltValid_eltMul (n := n) hn ih hx

theorem ev_ePow (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) (m : ℕ) :
    ev n K (ePow n x m) = (ev n K x) ^ m := by
  induction m with
  | zero => exact ev_eltOne hn
  | succ m ih =>
    rw [ePow, ev_eltMul hn (eltValid_ePow hn hx m) hx, ih, pow_succ]

end Ev

section EqSpec

variable {n : ℕ} (K : Type*) [Field K] [CharP K 3]

theorem eA_index {k : ℕ} (hn : 0 < n) (hk : k < n * n) :
    ∃ i j : Fin n, n * (i : ℕ) + (j : ℕ) = k := by
  refine ⟨⟨k / n, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hk)⟩, ⟨k % n, Nat.mod_lt _ hn⟩, ?_⟩
  show n * (k / n) + k % n = k
  exact Nat.div_add_mod k n

theorem mA_eq_iff (hn : 0 < n) (x y : Array ℕ) :
    mA n K x = mA n K y ↔ ∀ k < n * n, x[k]! % 3 = y[k]! % 3 := by
  constructor
  · intro h k hk
    obtain ⟨i, j, hij⟩ := eA_index hn hk
    have := congrFun (congrFun h i) j
    simp only [mA, Matrix.of_apply, eA, hij] at this
    exact (CharP.natCast_eq_natCast K 3).1 this
  · intro h
    ext i j
    simp only [mA, Matrix.of_apply, eA]
    exact (CharP.natCast_eq_natCast K 3).2 (h _ (lt_mul_of_lt i.2 j.2))

theorem mA_eq_neg_iff (hn : 0 < n) (x y : Array ℕ) :
    mA n K x = - mA n K y ↔ ∀ k < n * n, (x[k]! + y[k]!) % 3 = 0 := by
  constructor
  · intro h k hk
    obtain ⟨i, j, hij⟩ := eA_index hn hk
    have := congrFun (congrFun h i) j
    simp only [mA, Matrix.of_apply, eA, hij, Matrix.neg_apply] at this
    have h2 : ((x[k]! + y[k]! : ℕ) : K) = 0 := by
      rw [Nat.cast_add, this]; ring
    exact Nat.mod_eq_zero_of_dvd ((CharP.cast_eq_zero_iff K 3 _).1 h2)
  · intro h
    ext i j
    simp only [mA, Matrix.of_apply, eA, Matrix.neg_apply]
    have h2 := h _ (lt_mul_of_lt i.2 j.2)
    have h3 : ((x[n * (i : ℕ) + (j : ℕ)]! + y[n * (i : ℕ) + (j : ℕ)]! : ℕ) : K) = 0 :=
      (CharP.cast_eq_zero_iff K 3 _).2 (Nat.dvd_of_mod_eq_zero h2)
    rw [Nat.cast_add] at h3
    exact eq_neg_of_add_eq_zero_left h3

theorem eltEq_iff (hn : 0 < n) (x y : Array ℕ) :
    eltEq n x y = true ↔
      eE n x = eE n y ∧ (mA n K x = mA n K y ∨ mA n K x = - mA n K y) := by
  simp only [eltEq, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
    List.mem_range]
  rw [mA_eq_iff K hn, mA_eq_neg_iff K hn]

end EqSpec

section Ker

variable {n : ℕ} (K : Type) [Field K] [CharP K 3]

theorem exists_cast_lt_three [Finite K] (hK : Nat.card K = 3) (u : K) :
    ∃ a : ℕ, a < 3 ∧ ((a : ℕ) : K) = u := by
  let f : Fin 3 → K := fun i => ((i : ℕ) : K)
  have hinj : Function.Injective f := by
    intro i j hij
    have := (CharP.natCast_eq_natCast K 3).1 hij
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
    exact Fin.ext this
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hK]⟩
  obtain ⟨i, hi⟩ := hbij.2 u
  exact ⟨i, i.2, hi⟩

theorem unit_eq_one_or_neg [Finite K] (hK : Nat.card K = 3) (u : Kˣ) :
    (u : K) = 1 ∨ (u : K) = -1 := by
  obtain ⟨a, ha, hau⟩ := exists_cast_lt_three K hK (u : K)
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  interval_cases a
  · exact (u.ne_zero (by simpa using hau.symm)).elim
  · left
    simpa using hau.symm
  · right
    rw [← hau]
    have : (2 : K) = -1 := by linear_combination h3
    simpa using this

theorem ev_eq_of_eltEq (hn : 0 < n) {x y : Array ℕ} (hx : eltValid n x = true)
    (hy : eltValid n y = true) (h : eltEq n x y = true) : ev n K x = ev n K y := by
  rw [eltEq_iff K hn] at h
  obtain ⟨hε, hA | hA⟩ := h
  · have hu : unitA n K x = unitA n K y := by
      apply Units.ext
      rw [unitA_val hx, unitA_val hy, hA]
    unfold ev
    rw [hu, hε]
  · have hu : unitA n K x = unitA n K y * GeneralLinearGroup.scalar (Fin n) (-1 : Kˣ) := by
      apply Units.ext
      rw [unitA_val hx, Units.val_mul, unitA_val hy, hA, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
        Units.val_neg, Units.val_one, neg_one_smul]
    unfold ev
    rw [hu, map_mul, conjAut_scalar, mul_one, hε]

theorem eltEq_of_ev_eq (hn3 : 3 ≤ n) [Finite K] (hK : Nat.card K = 3) {x y : Array ℕ}
    (hx : eltValid n x = true) (hy : eltValid n y = true) (h : ev n K x = ev n K y) :
    eltEq n x y = true := by
  have hn : 0 < n := by omega
  rw [eltEq_iff K hn]
  have hxe := eE_lt_two hx
  have hye := eE_lt_two hy
  have hform : ∀ z : Array ℕ, ev n K z =
      conjAut n K (unitA n K z) * fieldAut n K 1 * dualAut n K ^ (eE n z) := by
    intro z
    unfold ev
    rw [map_one, mul_one]
  rw [hform x, hform y] at h
  obtain ⟨-, hε⟩ := standard_form_unique hn3 (by omega : eE n x ≤ 1) (by omega : eE n y ≤ 1) h
  refine ⟨hε, ?_⟩
  rw [← hε] at h
  have hc : conjAut n K (unitA n K x) = conjAut n K (unitA n K y) := by
    have := mul_right_cancel h
    simpa using this
  have hc1 : conjAut n K ((unitA n K y)⁻¹ * unitA n K x) = 1 := by
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  obtain ⟨u, hu⟩ := (conjAut_eq_one_iff hn3 _).1 hc1
  have hx' : unitA n K x = unitA n K y * GeneralLinearGroup.scalar (Fin n) u := by
    rw [← hu]; group
  have hxy : mA n K x = (u : K) • mA n K y := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, unitA_val hx, unitA_val hy] at this
    rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rcases unit_eq_one_or_neg K hK u with h1 | h1
  · left
    rw [hxy, h1, one_smul]
  · right
    rw [hxy, h1, neg_one_smul]

end Ker

section Order

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem fieldAut_eq_one (hK : Nat.card K = 3) [CharP K 3] (σ : K ≃+* K) :
    fieldAut n K σ = 1 := by
  have hσ : σ = 1 := by
    ext a
    obtain ⟨m, -, rfl⟩ := exists_cast_lt_three K hK a
    simp
  rw [hσ, map_one]

theorem card_mulAut_dvd (hn3 : 3 ≤ n) [CharP K 3] (hK : Nat.card K = 3) :
    Nat.card (MulAut (projectiveSL n K)) ∣ Nat.card (GL (Fin n) K) := by
  classical
  have hn : 0 < n := by omega
  set W := MulAut (projectiveSL n K) with hW
  set D : Subgroup W := (conjAut n K).range with hD
  have hker : (conjAut n K).ker =
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range := by
    ext A
    rw [MonoidHom.mem_ker, conjAut_eq_one_iff hn3, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨u, hu.symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, hu.symm⟩
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
    intro u v huv
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) huv
    exact Units.ext (by simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this)
  have hkc : Nat.card (conjAut n K).ker = 2 := by
    rw [hker, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_units, hK]
  have h1 := Subgroup.card_ker_mul_card_range (conjAut n K)
  rw [hkc] at h1
  have hsurj : Function.Surjective (fun p : D × Bool =>
      (p.1 : W) * dualAut n K ^ (cond p.2 1 0)) := by
    intro w
    obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn3
    obtain ⟨A, σ, ε, hε, hw⟩ := hform w
    rw [fieldAut_eq_one hK σ, mul_one] at hw
    refine ⟨(⟨conjAut n K A, A, rfl⟩, decide (ε = 1)), ?_⟩
    simp only
    rw [hw]
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl <;> simp
  have h2 : Nat.card W ≤ Nat.card D * 2 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  have h3 := Subgroup.index_mul_card D
  have hidx : D.index ∣ 2 := by
    have hpos : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hle : D.index ≤ 2 := by
      have : D.index * Nat.card D ≤ 2 * Nat.card D := by rw [h3]; linarith
      exact Nat.le_of_mul_le_mul_right this Nat.card_pos
    interval_cases (D.index)
    · exact one_dvd _
    · exact dvd_rfl
  rw [← h3]
  have h4 : 2 * Nat.card D = Nat.card (GL (Fin n) K) := h1
  rw [← h4]
  exact Nat.mul_dvd_mul hidx dvd_rfl

end Order

section Words

variable {n : ℕ} {K : Type} [Field K] [CharP K 3]

theorem evalWord_foldl (hn : 0 < n) {ws : Array (Array ℕ)} {H : Subgroup (MulAut (projectiveSL n K))}
    (hws : ∀ i < 3, eltValid n ws[i]! = true) (hH : ∀ i < 3, ev n K ws[i]! ∈ H)
    {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 3) :
    ∀ acc : Array ℕ, eltValid n acc = true → ev n K acc ∈ H →
      eltValid n (w.foldl (fun acc l => eltMul n acc
        (if l.2 then eltInv n ws[l.1]! else ws[l.1]!)) acc) = true ∧
      ev n K (w.foldl (fun acc l => eltMul n acc
        (if l.2 then eltInv n ws[l.1]! else ws[l.1]!)) acc) ∈ H := by
  induction w with
  | nil => intro acc h1 h2; exact ⟨h1, h2⟩
  | cons l w ih =>
    intro acc h1 h2
    have hl : l.1 < 3 := hw l (by simp)
    have hvl : eltValid n (if l.2 then eltInv n ws[l.1]! else ws[l.1]!) = true := by
      split_ifs
      · exact eltValid_eltInv (n := n) hn (hws _ hl)
      · exact hws _ hl
    have hel : ev n K (if l.2 then eltInv n ws[l.1]! else ws[l.1]!) ∈ H := by
      split_ifs
      · rw [ev_eltInv hn (hws _ hl)]
        exact H.inv_mem (hH _ hl)
      · exact hH _ hl
    simp only [List.foldl_cons]
    exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
      _ (eltValid_eltMul (n := n) hn h1 hvl) (by rw [ev_eltMul hn h1 hvl]; exact H.mul_mem h2 hel)

theorem evalWord_spec (hn : 0 < n) {ws : Array (Array ℕ)}
    (hws : ∀ i < 3, eltValid n ws[i]! = true) {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, l.1 < 3) :
    eltValid n (evalWord n ws w) = true ∧
      ev n K (evalWord n ws w) ∈ Subgroup.closure
        ({ev n K ws[0]!, ev n K ws[1]!, ev n K ws[2]!} : Set (MulAut (projectiveSL n K))) := by
  refine evalWord_foldl hn hws ?_ hw _ (eltValid_eltOne (n := n) hn) ?_
  · intro i hi
    apply Subgroup.subset_closure
    interval_cases i <;> simp
  · rw [ev_eltOne hn]
    exact Subgroup.one_mem _

end Words

section Rep

variable {n : ℕ} {K : Type} [Field K] [CharP K 3]

theorem even_orderOf_of {G : Type*} [Group G] {u : G} {j : ℕ} (h2 : u ^ (2 * j) = 1)
    (h1 : u ^ j ≠ 1) : Even (orderOf u) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hd : orderOf u ∣ 2 * j := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (orderOf u) 2 := (Nat.coprime_two_right).2 hodd
  exact h1 (orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hd))

theorem odd_orderOf_of {G : Type*} [Group G] {u : G} {m : ℕ} (h : u ^ m = 1) (hm : m % 2 = 1) :
    Odd (orderOf u) :=
  Odd.of_dvd_nat (Nat.odd_iff.2 hm) (orderOf_dvd_of_pow_eq_one h)

theorem ev_eltConj (hn : 0 < n) {s x : Array ℕ} (hs : eltValid n s = true)
    (hx : eltValid n x = true) :
    ev n K (eltConj n s x) = ev n K s * ev n K x * (ev n K s)⁻¹ := by
  have hsx := eltValid_eltMul (n := n) hn hs hx
  have hsi := eltValid_eltInv (n := n) hn hs
  rw [eltConj, ev_eltMul hn hsx hsi, ev_eltMul hn hs hx, ev_eltInv hn hs]

theorem eltValid_eltConj (hn : 0 < n) {s x : Array ℕ} (hs : eltValid n s = true)
    (hx : eltValid n x = true) : eltValid n (eltConj n s x) = true :=
  eltValid_eltMul (n := n) hn (eltValid_eltMul (n := n) hn hs hx) (eltValid_eltInv (n := n) hn hs)

theorem repOK_pairWit (hn3 : 3 ≤ n) [Finite K] (hK : Nat.card K = 3) {inF : Array ℕ → Bool}
    (hInF : ∀ g : Array ℕ, eltValid n g = true → eE n g = 0 → inF g = true →
      ∃ G : SpecialLinearGroup (Fin n) K, ev n K g = MulAut.conj (proj n K G))
    {r : LocRep} (h : repOK n inF r = true) :
    PairWit (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
      (ev n K r.x) (ev n K r.t) := by
  have hn : 0 < n := by omega
  unfold repOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hvx, hvt, hv1, hv2, hin1, hin2, he1, he2, hc1, hc2, hwa, hwb, hma, hmb, ha, hb, hab,
    hab'⟩ := h
  have hEq : ∀ {u v : Array ℕ}, eltValid n u = true → eltValid n v = true →
      eltEq n u v = true → ev n K u = ev n K v :=
    fun hu hv huv => ev_eq_of_eltEq K hn hu hv huv
  have hg1 : ev n K r.g₁ ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    obtain ⟨G, hG⟩ := hInF _ hv1 he1 hin1
    exact ⟨proj n K G, hG.symm⟩
  have hg2 : ev n K r.g₂ ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    obtain ⟨G, hG⟩ := hInF _ hv2 he2 hin2
    exact ⟨proj n K G, hG.symm⟩
  have hcomm1 : ev n K r.g₁ * ev n K r.t = ev n K r.t * ev n K r.g₁ := by
    have := hEq (eltValid_eltMul (n := n) hn hv1 hvt) (eltValid_eltMul (n := n) hn hvt hv1) hc1
    rwa [ev_eltMul hn hv1 hvt, ev_eltMul hn hvt hv1] at this
  have hcomm2 : ev n K r.g₂ * ev n K r.t = ev n K r.t * ev n K r.g₂ := by
    have := hEq (eltValid_eltMul (n := n) hn hv2 hvt) (eltValid_eltMul (n := n) hn hvt hv2) hc2
    rwa [ev_eltMul hn hv2 hvt, ev_eltMul hn hvt hv2] at this
  have hc1v := eltValid_eltConj (n := n) hn hv1 hvx
  have hc2v := eltValid_eltConj (n := n) hn hv2 hvx
  set ws : Array (Array ℕ) := #[r.x, eltConj n r.g₁ r.x, eltConj n r.g₂ r.x] with hws
  have hwsv : ∀ i < 3, eltValid n ws[i]! = true := by
    intro i hi
    interval_cases i
    · simpa [hws] using hvx
    · simpa [hws] using hc1v
    · simpa [hws] using hc2v
  have hset : ({ev n K ws[0]!, ev n K ws[1]!, ev n K ws[2]!} : Set (MulAut (projectiveSL n K))) =
      {ev n K r.x, ev n K r.g₁ * ev n K r.x * (ev n K r.g₁)⁻¹,
        ev n K r.g₂ * ev n K r.x * (ev n K r.g₂)⁻¹} := by
    simp [hws, ev_eltConj hn hv1 hvx, ev_eltConj hn hv2 hvx]
  obtain ⟨hva, hmema⟩ := evalWord_spec (K := K) hn hwsv hwa
  obtain ⟨hvb, hmemb⟩ := evalWord_spec (K := K) hn hwsv hwb
  rw [hset] at hmema hmemb
  set a := evalWord n ws r.wa with hadef
  set b := evalWord n ws r.wb with hbdef
  refine ⟨ev n K r.g₁, hg1, ev n K r.g₂, hg2, hcomm1, hcomm2, ev n K a, hmema, ev n K b, hmemb,
    ?_, ?_, ?_⟩
  · have := hEq (eltValid_ePow hn hva r.ma) (eltValid_eltOne (n := n) hn) ha
    rw [ev_ePow hn hva, ev_eltOne hn] at this
    exact odd_orderOf_of this (by simpa using hma)
  · have := hEq (eltValid_ePow hn hvb r.mb) (eltValid_eltOne (n := n) hn) hb
    rw [ev_ePow hn hvb, ev_eltOne hn] at this
    exact odd_orderOf_of this (by simpa using hmb)
  · have hvab := eltValid_eltMul (n := n) hn hva hvb
    have h2 := hEq (eltValid_ePow hn hvab (2 * r.j)) (eltValid_eltOne (n := n) hn) hab
    rw [ev_ePow hn hvab, ev_eltOne hn, ev_eltMul hn hva hvb] at h2
    have h1 : (ev n K a * ev n K b) ^ r.j ≠ 1 := by
      intro h1
      have hvj := eltValid_ePow hn hvab r.j
      have : eltEq n (ePow n (eltMul n a b) r.j) (eltOne n) = true := by
        refine eltEq_of_ev_eq K hn3 hK hvj (eltValid_eltOne (n := n) hn) ?_
        rw [ev_ePow hn hvab, ev_eltOne hn, ev_eltMul hn hva hvb]
        exact h1
      rw [this] at hab'
      exact absurd hab' (by decide)
    exact even_orderOf_of h2 h1

end Rep

theorem eltKey_eq_of_eltEq {n : ℕ} {x y : Array ℕ} (h : eltEq n x y = true) :
    eltKey n x = eltKey n y := by
  simp only [eltEq, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨hε, h | h⟩ := h
  · have h' : ∀ k < n * n, x[k]! % 3 = y[k]! % 3 := fun k hk => by simpa using h k hk
    have e1 : kA n x = kA n y := by
      unfold kA
      congr 1
      exact List.map_congr_left fun k hk => h' k (List.mem_range.1 hk)
    have e2 : kN n x = kN n y := by
      unfold kN
      congr 1
      exact List.map_congr_left fun k hk => by rw [h' k (List.mem_range.1 hk)]
    unfold eltKey
    rw [e1, e2, hε]
  · have h' : ∀ k < n * n, (x[k]! + y[k]!) % 3 = 0 := fun k hk => by simpa using h k hk
    have e1 : kA n x = kN n y := by
      unfold kA kN
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have := h' k (List.mem_range.1 hk)
      omega
    have e2 : kN n x = kA n y := by
      unfold kA kN
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have := h' k (List.mem_range.1 hk)
      omega
    unfold eltKey
    rw [e1, e2, hε, min_comm]

section Norm

variable {n : ℕ} (K : Type*) [Field K] [CharP K 3]

theorem size_eltMinusOne : (eltMinusOne n).size = 2 * (n * n) + 1 := by simp [eltMinusOne]

theorem eltMinusOne_get {k : ℕ} (hk : k < 2 * (n * n) + 1) :
    (eltMinusOne n)[k]! = if k < 2 * (n * n) then
      (if (k % (n * n)) / n = (k % (n * n)) % n then 2 else 0) else 0 := by
  rw [getElem!_pos _ _ (by rw [size_eltMinusOne]; exact hk)]
  simp [eltMinusOne]

theorem two_eq_neg_one : (2 : K) = -1 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  linear_combination h3

theorem mA_eltMinusOne (hn : 0 < n) : mA n K (eltMinusOne n) = -1 := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  simp only [mA, Matrix.of_apply, eA]
  rw [eltMinusOne_get (by omega), if_pos (by omega), Nat.mod_eq_of_lt hk, hd, hm]
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij, two_eq_neg_one K]
  · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [Matrix.one_apply, hij, this]

theorem mB_eltMinusOne (hn : 0 < n) : mB n K (eltMinusOne n) = -1 := by
  ext i j
  have hk : n * (i : ℕ) + (j : ℕ) < n * n := lt_mul_of_lt i.2 j.2
  obtain ⟨hd, hm⟩ := index_div_mod (i := (i : ℕ)) hn j.2
  simp only [mB, Matrix.of_apply, eB]
  rw [eltMinusOne_get (by omega), if_pos (by omega), Nat.add_mod_left, Nat.mod_eq_of_lt hk, hd, hm]
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij, two_eq_neg_one K]
  · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [Matrix.one_apply, hij, this]

theorem eE_eltMinusOne (hn : 0 < n) : eE n (eltMinusOne n) = 0 := by
  rw [eE, eltMinusOne_get (by omega), if_neg (lt_irrefl _)]

theorem eltValid_eltMinusOne (hn : 0 < n) : eltValid n (eltMinusOne n) = true := by
  rw [eltValid_iff (ZMod 3)]
  refine ⟨size_eltMinusOne, ?_, ?_, ?_⟩
  · intro k hk
    rw [eltMinusOne_get (by omega), if_pos hk]
    split_ifs <;> norm_num
  · rw [eltMinusOne_get (by omega), if_neg (lt_irrefl _)]
    norm_num
  · rw [mA_eltMinusOne (ZMod 3) hn, mB_eltMinusOne (ZMod 3) hn, Matrix.transpose_neg,
      Matrix.transpose_one, neg_mul_neg, Matrix.mul_one]

end Norm

section Ev2

variable {n : ℕ} {K : Type} [Field K] [CharP K 3]

theorem ev_eltMinusOne (hn : 0 < n) : ev n K (eltMinusOne n) = 1 := by
  have hu : unitA n K (eltMinusOne n) = GeneralLinearGroup.scalar (Fin n) (-1 : Kˣ) := by
    apply Units.ext
    rw [unitA_val (eltValid_eltMinusOne (n := n) hn), mA_eltMinusOne K hn,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      Units.val_neg, Units.val_one, neg_smul, one_smul]
  unfold ev
  rw [hu, conjAut_scalar, eE_eltMinusOne hn]
  simp

theorem eltValid_eltNorm (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) :
    eltValid n (eltNorm n x) = true := by
  unfold eltNorm
  split_ifs
  · exact eltValid_eltMul (n := n) hn (eltValid_eltMinusOne (n := n) hn) hx
  · exact hx

theorem ev_eltNorm (hn : 0 < n) {x : Array ℕ} (hx : eltValid n x = true) :
    ev n K (eltNorm n x) = ev n K x := by
  unfold eltNorm
  split_ifs
  · rw [ev_eltMul hn (eltValid_eltMinusOne (n := n) hn) hx, ev_eltMinusOne hn, one_mul]
  · rfl

end Ev2

section InF

variable {n : ℕ} {K : Type} [Field K] [CharP K 3]

theorem inF_of_unit_pow (hn : 0 < n) {g : Array ℕ} (hv : eltValid n g = true) (he : eE n g = 0)
    (μ : Kˣ) (hdet : (mA n K g).det = (μ : K) ^ n) :
    ∃ G : SpecialLinearGroup (Fin n) K, ev n K g = MulAut.conj (proj n K G) := by
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  have hdet' : (((μ : K)⁻¹) • mA n K g).det = 1 := by
    rw [Matrix.det_smul, hdet, Fintype.card_fin, ← mul_pow, inv_mul_cancel₀ hμ, one_pow]
  obtain ⟨G, hG⟩ : ∃ G : SpecialLinearGroup (Fin n) K,
      (G : Matrix (Fin n) (Fin n) K) = ((μ : K)⁻¹) • mA n K g := ⟨⟨_, hdet'⟩, rfl⟩
  refine ⟨G, ?_⟩
  have hu : unitA n K g = SpecialLinearGroup.toGL G * GeneralLinearGroup.scalar (Fin n) μ := by
    apply Units.ext
    rw [unitA_val hv, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    show mA n K g = (μ : K) • (G : Matrix (Fin n) (Fin n) K)
    rw [hG, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  unfold ev
  rw [he, pow_zero, mul_one, hu, map_mul, conjAut_scalar, mul_one, conjAut_toGL]

theorem mA_det4 (x : Array ℕ) : (mA 4 K x).det = ((det4Z x : ℤ) : K) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.sum_univ_zero, mA, Matrix.of_apply,
    Matrix.submatrix_apply, det4Z, eA]
  simp [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.lt_def]
  ring

theorem inF4_spec {g : Array ℕ} (hv : eltValid 4 g = true) (he : eE 4 g = 0) (h : inF4 g = true) :
    ∃ G : SpecialLinearGroup (Fin 4) K, ev 4 K g = MulAut.conj (proj 4 K G) := by
  refine inF_of_unit_pow (by norm_num) hv he 1 ?_
  rw [mA_det4, Units.val_one, one_pow]
  have h1 : det4Z g % 3 = 1 := by simpa [inF4] using h
  have : ((det4Z g : ℤ) : K) = ((det4Z g % 3 : ℤ) : K) := by
    apply (CharP.intCast_eq_intCast K 3).2
    exact (Int.emod_emod_of_dvd _ (dvd_refl 3)).symm
  rw [this, h1]
  simp

theorem inF5_spec [Finite K] (hK : Nat.card K = 3) {g : Array ℕ} (hv : eltValid 5 g = true)
    (he : eE 5 g = 0) (_ : inF5 g = true) :
    ∃ G : SpecialLinearGroup (Fin 5) K, ev 5 K g = MulAut.conj (proj 5 K G) := by
  have hu : IsUnit (mA 5 K g).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← unitA_val hv]
    exact (unitA 5 K g).isUnit
  obtain ⟨μ, hμ⟩ := hu
  refine inF_of_unit_pow (by norm_num) hv he μ ?_
  rw [← hμ]
  rcases unit_eq_one_or_neg K hK μ with h | h <;> rw [h] <;> norm_num

end InF

open CFSG.Monster.B.Fischer

section Sound

variable {n : ℕ} {K : Type} [Field K] [CharP K 3] [Finite K]

theorem isO8_of_orderOf (hn3 : 3 ≤ n) (hK : Nat.card K = 3) {x : Array ℕ}
    (hx : eltValid n x = true) (h : orderOf (ev n K x) = 8) : isO8 n x = true := by
  have hn : 0 < n := by omega
  have hv8 := eltValid_ePow hn hx 8
  have hv4 := eltValid_ePow hn hx 4
  have h8 : (ev n K x) ^ 8 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h4 : (ev n K x) ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h]; norm_num)
  unfold isO8
  rw [Bool.and_eq_true]
  constructor
  · exact eltEq_of_ev_eq K hn3 hK hv8 (eltValid_eltOne (n := n) hn)
      (by rw [ev_ePow hn hx, ev_eltOne hn]; exact h8)
  · rw [Bool.not_eq_true']
    by_contra hcon
    have h1 : eltEq n (ePow n x 4) (eltOne n) = true := by simpa using hcon
    have h2 := ev_eq_of_eltEq K hn hv4 (eltValid_eltOne (n := n) hn) h1
    rw [ev_ePow hn hx, ev_eltOne hn] at h2
    exact h4 h2

theorem isO2_of_orderOf (hn3 : 3 ≤ n) (hK : Nat.card K = 3) {x : Array ℕ}
    (hx : eltValid n x = true) (h : orderOf (ev n K x) = 2) : isO2 n x = true := by
  have hn : 0 < n := by omega
  have hv2 := eltValid_ePow hn hx 2
  have h2 : (ev n K x) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h1 : ev n K x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    omega
  unfold isO2
  rw [Bool.and_eq_true]
  constructor
  · exact eltEq_of_ev_eq K hn3 hK hv2 (eltValid_eltOne (n := n) hn)
      (by rw [ev_ePow hn hx, ev_eltOne hn]; exact h2)
  · rw [Bool.not_eq_true']
    by_contra hcon
    have h3 : eltEq n x (eltOne n) = true := by simpa using hcon
    have h4 := ev_eq_of_eltEq K hn hx (eltValid_eltOne (n := n) hn) h3
    rw [ev_eltOne hn] at h4
    exact h1 h4

theorem locCover_sound (hn3 : 3 ≤ n) (hK : Nat.card K = 3) {pts : Array (Array ℕ)}
    {reps : Array LocRep} (hpts : ∀ i < pts.size, eltValid n pts[i]! = true)
    (hreps : ∀ ri < reps.size, eltValid n reps[ri]!.x = true ∧ eltValid n reps[ri]!.t = true)
    (h : locCover n pts reps = true) {i j : ℕ} (hi : i < pts.size) (hj : j < pts.size)
    (h8 : orderOf (ev n K pts[i]!) = 8) (h2 : orderOf (ev n K pts[j]!) = 2)
    (hc : ev n K pts[i]! * ev n K pts[j]! = ev n K pts[j]! * ev n K pts[i]!) :
    ∃ ri < reps.size, ∃ si < pts.size,
      ev n K pts[i]! = ev n K pts[si]! * ev n K reps[ri]!.x * (ev n K pts[si]!)⁻¹ ∧
      ev n K pts[j]! = ev n K pts[si]! * ev n K reps[ri]!.t * (ev n K pts[si]!)⁻¹ := by
  have hn : 0 < n := by omega
  unfold locCover at h
  simp only [List.all_eq_true, List.mem_filter, List.mem_range] at h
  have h := h i ⟨hi, isO8_of_orderOf hn3 hK (hpts i hi) h8⟩ j
    ⟨hj, isO2_of_orderOf hn3 hK (hpts j hj) h2⟩
  have hcomm : eltEq n (eltMul n pts[i]! pts[j]!) (eltMul n pts[j]! pts[i]!) = true := by
    refine eltEq_of_ev_eq K hn3 hK (eltValid_eltMul (n := n) hn (hpts i hi) (hpts j hj))
      (eltValid_eltMul (n := n) hn (hpts j hj) (hpts i hi)) ?_
    rw [ev_eltMul hn (hpts i hi) (hpts j hj), ev_eltMul hn (hpts j hj) (hpts i hi)]
    exact hc
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · simp [hcomm] at h
  · split at h
    · rename_i ri si hsome
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hri, hsi⟩, hx⟩, ht⟩ := h
      obtain ⟨hrx, hrt⟩ := hreps ri hri
      refine ⟨ri, hri, si, hsi, ?_, ?_⟩
      · have := ev_eq_of_eltEq K hn (eltValid_eltConj (n := n) hn (hpts si hsi) hrx) (hpts i hi) hx
        rw [← this, ev_eltConj hn (hpts si hsi) hrx]
      · have := ev_eq_of_eltEq K hn (eltValid_eltConj (n := n) hn (hpts si hsi) hrt) (hpts j hj) ht
        rw [← this, ev_eltConj hn (hpts si hsi) hrt]
    · exact absurd h (by simp)

theorem repOK_valid {inF : Array ℕ → Bool} {r : LocRep} (h : repOK n inF r = true) :
    eltValid n r.x = true ∧ eltValid n r.t = true := by
  unfold repOK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact ⟨h.1, h.2.1⟩

theorem normal_inn {F : Type*} [Group F] :
    (MulAut.conj : F →* MulAut F).range.Normal := by
  refine ⟨fun a ha b => ?_⟩
  obtain ⟨f, rfl⟩ := ha
  refine ⟨b f, ?_⟩
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem locCheck_sound (hn3 : 3 ≤ n) (hK : Nat.card K = 3) {inF : Array ℕ → Bool}
    (hInF : ∀ g : Array ℕ, eltValid n g = true → eE n g = 0 → inF g = true →
      ∃ G : SpecialLinearGroup (Fin n) K, ev n K g = MulAut.conj (proj n K G))
    {d : LocData} (h : locCheck n inF d = true) {m : ℕ} (hm : ¬ 2 ∣ m)
    (hGL : Nat.card (GL (Fin n) K) = 2 ^ d.k * m) {x t : MulAut (projectiveSL n K)}
    (hx : orderOf x = 8) (ht : orderOf t = 2) (hxt : x * t = t * x) :
    PairWit (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range x t := by
  have hn : 0 < n := by omega
  unfold locCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, and_assoc] at h
  obtain ⟨hgens, hcert, hsize, hrepsOK, hcover⟩ := h
  have hgv : ∀ k < d.gens.size, eltValid n d.gens[k]! = true := hgens
  have hact : ∀ k < d.gens.size, ∀ a, eltValid n a = true →
      ev n K (locAct n d.gens k a) = ev n K d.gens[k]! * ev n K a := by
    intro k hk a ha
    unfold locAct
    rw [ev_eltNorm hn (eltValid_eltMul (n := n) hn (hgv k hk) ha),
      ev_eltMul hn (hgv k hk) ha]
  have hkey : ∀ a b, eltValid n a = true → eltValid n b = true → ev n K a = ev n K b →
      eltKey n a = eltKey n b := fun a b ha hb hab =>
    eltKey_eq_of_eltEq (eltEq_of_ev_eq K hn3 hK ha hb hab)
  obtain ⟨hmem, hcard⟩ := card_closure_of_arrCertOK (G := MulAut (projectiveSL n K))
    (dec := ev n K) (gens := fun k => ev n K d.gens[k]!) hcert hact hkey (ev_eltOne hn)
  set S := Subgroup.closure ((fun k => ev n K d.gens[k]!) '' {k | k < d.gens.size}) with hS
  have hSsize : Nat.card S = 2 ^ d.k := by rw [hcard]; exact hsize
  have hSp : IsPGroup 2 S := IsPGroup.of_card hSsize
  have hidx : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    have h2 := card_mulAut_dvd (n := n) (K := K) hn3 hK
    rw [← h1, hSsize, hGL] at h2
    have h3 : S.index ∣ m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
    exact fun h4 => hm (h4.trans h3)
  have hpts : ∀ i < (locBfs n d).pts.size, eltValid n (locBfs n d).pts[i]! = true :=
    fun i hi => arrCertOK_valid hcert hi
  have hreps : ∀ ri < d.reps.size, eltValid n d.reps[ri]!.x = true ∧
      eltValid n d.reps[ri]!.t = true := by
    intro ri hri
    have hmemr : d.reps[ri]! ∈ d.reps.toList := by
      rw [getElem!_pos d.reps ri hri]
      exact Array.getElem_mem_toList hri
    exact repOK_valid (hrepsOK _ hmemr)
  refine pairWit_of_sylow normal_inn hSp hidx ?_ hx ht hxt
  intro x hxS t htS hx8 ht2 hc
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hxS
  obtain ⟨j, hj, rfl⟩ := (hmem t).1 htS
  obtain ⟨ri, hri, si, hsi, hxeq, hteq⟩ :=
    locCover_sound hn3 hK hpts hreps hcover hi hj hx8 ht2 hc
  have hmemr : d.reps[ri]! ∈ d.reps.toList := by
    rw [getElem!_pos d.reps ri hri]
    exact Array.getElem_mem_toList hri
  have hw := repOK_pairWit hn3 hK hInF (hrepsOK _ hmemr)
  have := hw.conj normal_inn (ev n K (locBfs n d).pts[si]!)
  rw [hxeq, hteq]
  exact this

end Sound

theorem charP_three_of_card {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    CharP K 3 := by
  have h : (3 : K) = 0 := by
    haveI := Fintype.ofFinite K
    have := card_nsmul_eq_zero (G := K) (x := (1 : K))
    rw [← Nat.card_eq_fintype_card, hK] at this
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 (by exact_mod_cast h)

theorem card_GL_three {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) (n : ℕ) :
    Nat.card (GL (Fin n) K) = ∏ i : Fin n, (3 ^ n - 3 ^ (i : ℕ)) := by
  haveI := Fintype.ofFinite K
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field, hc]

theorem card_GL4 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nat.card (GL (Fin 4) K) = 2 ^ 9 * 47385 := by
  rw [card_GL_three hK, Fin.prod_univ_four]
  norm_num

theorem card_GL5 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3) :
    Nat.card (GL (Fin 5) K) = 2 ^ 10 * 464420385 := by
  rw [card_GL_three hK, Fin.prod_univ_five]
  norm_num

theorem pairWit_of_locCheck {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {inF : Array ℕ → Bool}
    (hInF : ∀ [CharP K 3] (g : Array ℕ), eltValid n g = true → eE n g = 0 → inF g = true →
      ∃ G : SpecialLinearGroup (Fin n) K, ev n K g = MulAut.conj (proj n K G))
    {d : LocData} (h : locCheck n inF d = true) {m : ℕ} (hm : ¬ 2 ∣ m)
    (hGL : Nat.card (GL (Fin n) K) = 2 ^ d.k * m) :
    ∀ x t : MulAut (projectiveSL n K), orderOf x = 8 → orderOf t = 2 → x * t = t * x →
      PairWit (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range x t := by
  haveI := charP_three_of_card hK
  intro x t hx ht hxt
  exact locCheck_sound hn3 hK (hInF) h hm hGL hx ht hxt

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

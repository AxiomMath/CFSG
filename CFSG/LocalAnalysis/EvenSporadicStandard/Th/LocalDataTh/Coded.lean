module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open scoped Matrix

@[expose] def bitZ (n i : ℕ) : ZMod 2 := if n.testBit i then 1 else 0

@[expose] def codeVec (m n : ℕ) : Fin m → ZMod 2 := fun i => bitZ n i

@[expose] def applyCols (m : ℕ) (cs : List ℕ) (v : ℕ) : ℕ :=
  (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ cs.getD j 0 else acc) 0

@[expose] def mulCols (m : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range m).map fun k => applyCols m a (b.getD k 0)

@[expose] def matOfCols (m : ℕ) (cs : List ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => bitZ (cs.getD j 0) i

@[expose] def idCols (m : ℕ) : List ℕ := (List.range m).map fun j => 2 ^ j

theorem bitZ_xor (a b i : ℕ) : bitZ (a ^^^ b) i = bitZ a i + bitZ b i := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bitZ_zero (i : ℕ) : bitZ 0 i = 0 := by simp [bitZ]

theorem bitZ_inj {a b i : ℕ} (h : bitZ a i = bitZ b i) : a.testBit i = b.testBit i := by
  unfold bitZ at h
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem sum_range_map (f : ℕ → ZMod 2) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem foldl_bit (v : ℕ) (cs : List ℕ) (i : ℕ) (l : List ℕ) (a : ℕ) :
    bitZ (l.foldl (fun acc j => if v.testBit j then acc ^^^ cs.getD j 0 else acc) a) i =
      bitZ a i + (l.map fun j => bitZ v j * bitZ (cs.getD j 0) i).sum := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    by_cases hj : v.testBit j = true
    · have h1 : bitZ v j = 1 := by simp [bitZ, hj]
      rw [ite_eq_left hj, bitZ_xor, h1, one_mul, add_assoc]
    · have h0 : bitZ v j = 0 := by simp [bitZ, hj]
      rw [ite_eq_right hj, h0, zero_mul, zero_add]

theorem bitZ_applyCols (m : ℕ) (cs : List ℕ) (v i : ℕ) :
    bitZ (applyCols m cs v) i = ∑ j ∈ Finset.range m, bitZ v j * bitZ (cs.getD j 0) i := by
  unfold applyCols
  rw [foldl_bit, bitZ_zero, zero_add, sum_range_map]

theorem matOfCols_mulVec (m : ℕ) (cs : List ℕ) (v : ℕ) :
    matOfCols m cs *ᵥ codeVec m v = codeVec m (applyCols m cs v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, matOfCols, codeVec, Matrix.of_apply]
  rw [bitZ_applyCols, ← Fin.sum_univ_eq_sum_range (fun j => bitZ v j * bitZ (cs.getD j 0) i) m]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem getD_mulCols (m : ℕ) (a b : List ℕ) {k : ℕ} (hk : k < m) :
    (mulCols m a b).getD k 0 = applyCols m a (b.getD k 0) := by
  simp [mulCols, List.getD_eq_getElem?_getD, hk]

theorem matOfCols_mulCols (m : ℕ) (a b : List ℕ) :
    matOfCols m (mulCols m a b) = matOfCols m a * matOfCols m b := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [matOfCols, Matrix.of_apply]
  rw [getD_mulCols m a b k.2, bitZ_applyCols,
    ← Fin.sum_univ_eq_sum_range (fun j => bitZ (b.getD k 0) j * bitZ (a.getD j 0) i) m]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem codeVec_xor (m a b : ℕ) : codeVec m (a ^^^ b) = codeVec m a + codeVec m b := by
  funext i
  exact bitZ_xor a b i

theorem codeVec_zero (m : ℕ) : codeVec m 0 = 0 := by
  funext i
  exact bitZ_zero i

theorem codeVec_injOn (m : ℕ) {a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : codeVec m a = codeVec m b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitZ_inj (congrFun h ⟨i, hi⟩)
  · have h2 : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha h2),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h2)]

theorem exists_codeVec (m : ℕ) (v : Fin m → ZMod 2) : ∃ c < 2 ^ m, codeVec m c = v := by
  have hinj : Function.Injective fun c : Fin (2 ^ m) => codeVec m c.val :=
    fun a b h => Fin.ext (codeVec_injOn m a.2 b.2 h)
  have hcard : Fintype.card (Fin (2 ^ m)) = Fintype.card (Fin m → ZMod 2) := by
    simp
  obtain ⟨c, hc⟩ := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩ |>.2 v
  exact ⟨c.val, c.2, hc⟩

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh

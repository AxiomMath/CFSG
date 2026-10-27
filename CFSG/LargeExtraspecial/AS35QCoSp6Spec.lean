module

public import CFSG.LargeExtraspecial.AS35QCoNative
public import CFSG.Sporadic.Co2Smith.Defs

public section

namespace CFSG.LargeExtraspecial.AS35QCo

open Native Matrix CFSG.Assembly.LowTwoRank CFSG.Sporadic.Co2Smith

theorem testBit_ofBitsN (n : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (ofBitsN n f).testBit i = (decide (i < n) && f i) := by
  unfold ofBitsN
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with hf
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1, Ne.symm him]
    · rw [ih]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1]

theorem ofBitsN_lt (n : ℕ) (f : ℕ → Bool) : ofBitsN n f < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_ofBitsN]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

theorem mulc_lt (c d : ℕ) : mulc c d < 2 ^ 36 := ofBitsN_lt _ _

theorem transc_lt (c : ℕ) : transc c < 2 ^ 36 := ofBitsN_lt _ _

theorem foldl_xor_eq_sum (f : ℕ → Bool) (m : ℕ) (init : Bool) :
    (if (List.range m).foldl (fun acc j => acc ^^ f j) init then (1 : ZMod 2) else 0) =
      (if init then 1 else 0) + ∑ j ∈ Finset.range m, if f j then (1 : ZMod 2) else 0 := by
  induction m generalizing init with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, add_zero]
    cases init <;> rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc]
    set b := (List.range m).foldl (fun acc j => acc ^^ f j) init with hb
    have key : (if b then (1 : ZMod 2) else 0) =
        (if init then 1 else 0) + ∑ j ∈ Finset.range m, if f j then (1 : ZMod 2) else 0 := ih init
    rw [← key]
    cases b <;> cases f m <;> decide

abbrev ix (x : Fin 3 ⊕ Fin 3) : ℕ := (finSumFinEquiv x : ℕ)

theorem ix_lt (x : Fin 3 ⊕ Fin 3) : ix x < 6 := (finSumFinEquiv x).isLt

@[expose] def decode (c : ℕ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun x y => if c.testBit (6 * ix x + ix y) then 1 else 0

theorem decode_apply (c : ℕ) (x y : Fin 3 ⊕ Fin 3) :
    decode c x y = if c.testBit (6 * ix x + ix y) then 1 else 0 := rfl

theorem div_six (a b : ℕ) (hb : b < 6) : (6 * a + b) / 6 = a := by omega

theorem mod_six (a b : ℕ) (hb : b < 6) : (6 * a + b) % 6 = b := by omega

theorem sum_sumFin (g : ℕ → ZMod 2) :
    ∑ z : Fin 3 ⊕ Fin 3, g (ix z) = ∑ j ∈ Finset.range 6, g j := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv finSumFinEquiv _ _ fun z => rfl

theorem ite_mul_ite (a b : Bool) :
    ((if a then (1 : ZMod 2) else 0) * if b then 1 else 0) = if (a && b) then 1 else 0 := by
  cases a <;> cases b <;> decide

theorem decode_mulc (c d : ℕ) : decode (mulc c d) = decode c * decode d := by
  ext x y
  rw [Matrix.mul_apply, decode_apply, mulc, testBit_ofBitsN]
  have hx := ix_lt x
  have hy := ix_lt y
  have h36 : 6 * ix x + ix y < 36 := by omega
  rw [decide_eq_true h36, Bool.true_and, div_six _ _ hy, mod_six _ _ hy, dotc,
    foldl_xor_eq_sum]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  have e : ∀ z : Fin 3 ⊕ Fin 3, decode c x z * decode d z y =
      (fun j => if (ent c (ix x) j && ent d j (ix y)) then (1 : ZMod 2) else 0) (ix z) := by
    intro z
    simp only [decode_apply, ent]
    exact ite_mul_ite _ _
  rw [Finset.sum_congr rfl fun z _ => e z]
  exact (sum_sumFin (fun j => if (ent c (ix x) j && ent d j (ix y)) then (1 : ZMod 2) else 0)).symm

theorem decode_transc (c : ℕ) : decode (transc c) = (decode c)ᵀ := by
  ext x y
  rw [Matrix.transpose_apply, decode_apply, decode_apply, transc, testBit_ofBitsN]
  have hx := ix_lt x
  have hy := ix_lt y
  have h36 : 6 * ix x + ix y < 36 := by omega
  rw [decide_eq_true h36, Bool.true_and, div_six _ _ hy, mod_six _ _ hy, ent]

theorem decode_idc : decode idc = 1 := by
  ext x y
  rw [decode_apply, Matrix.one_apply]
  revert x y
  decide

theorem decode_jc : decode jc = Matrix.fromBlocks 0 1 (-1) 0 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [decode_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply,
      Matrix.neg_apply] <;> revert x y <;> decide

theorem decode_injective {c d : ℕ} (hc : c < 2 ^ 36) (hd : d < 2 ^ 36)
    (h : decode c = decode d) : c = d := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 36
  · have ha : i / 6 < 6 := by omega
    have hb : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
    set x : Fin 3 ⊕ Fin 3 := finSumFinEquiv.symm ⟨i / 6, ha⟩ with hxdef
    set y : Fin 3 ⊕ Fin 3 := finSumFinEquiv.symm ⟨i % 6, hb⟩ with hydef
    have hix : ix x = i / 6 := by rw [ix, hxdef, Equiv.apply_symm_apply]
    have hiy : ix y = i % 6 := by rw [ix, hydef, Equiv.apply_symm_apply]
    have hi' : 6 * ix x + ix y = i := by rw [hix, hiy]; omega
    have e := congrFun (congrFun h x) y
    rw [decode_apply, decode_apply, hi'] at e
    cases hcb : c.testBit i <;> cases hdb : d.testBit i <;> simp_all
  · have h1 : 2 ^ 36 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h1),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hd h1)]

@[expose] def Rep (c : ℕ) (g : Sp62) : Prop :=
  ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = decode c

theorem Rep.mul {c d : ℕ} {g h : Sp62} (hg : Rep c g) (hh : Rep d h) : Rep (mulc c d) (g * h) := by
  unfold Rep at *
  rw [decode_mulc, ← hg, ← hh]
  rfl

theorem Rep.one : Rep idc (1 : Sp62) := by
  unfold Rep
  rw [decode_idc]
  rfl

theorem Rep.unique {c : ℕ} {g h : Sp62} (hg : Rep c g) (hh : Rep c h) : g = h := by
  apply Subtype.ext
  apply Units.ext
  exact hg.trans hh.symm

theorem Rep.code_eq {c d : ℕ} {g : Sp62} (hc : Rep c g) (hd : Rep d g) (hc' : c < 2 ^ 36)
    (hd' : d < 2 ^ 36) : c = d :=
  decode_injective hc' hd' (hc.symm.trans hd)

theorem exists_rep {c ci : ℕ} (h1 : mulc c ci = idc) (h2 : mulc ci c = idc)
    (hsp : isSp c = true) : ∃ g : Sp62, Rep c g ∧ Rep ci g⁻¹ := by
  let u : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
    ⟨decode c, decode ci, by rw [← decode_mulc, h1, decode_idc], by
      rw [← decode_mulc, h2, decode_idc]⟩
  have hmem : u ∈ StatedSp 3 (ZMod 2) := by
    apply Subgroup.subset_closure
    show (decode c)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * decode c = Matrix.fromBlocks 0 1 (-1) 0
    have e := congrArg decode (beq_iff_eq.mp hsp)
    rw [decode_mulc, decode_mulc, decode_transc, decode_jc] at e
    exact e
  exact ⟨⟨u, hmem⟩, rfl, rfl⟩

end CFSG.LargeExtraspecial.AS35QCo

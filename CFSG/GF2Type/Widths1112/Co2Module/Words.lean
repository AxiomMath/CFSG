module

public import CFSG.GF2Type.Widths1112.Co2Setup
public import CFSG.GF2Type.Widths1112.Co2Module.RowsOf
public import Certificates.Data.GF2W1112Co2U
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open CFSG.Blueprint CFSG.Sporadic CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co2.Native CFSG.GF2W1112 Matrix

abbrev G2 : Type := NativeSporadic.Co2

abbrev mat2 (g : G2) : Matrix (Fin 22) (Fin 22) (ZMod 2) := (g : Matrix (Fin 22) (Fin 22) (ZMod 2))

theorem mat2_mul (g h : G2) : mat2 (g * h) = mat2 g * mat2 h := rfl

theorem mat2_one : mat2 (1 : G2) = 1 := rfl

theorem mat2_pow (g : G2) (n : ℕ) : mat2 (g ^ n) = mat2 g ^ n := by
  induction n with
  | zero => simp only [pow_zero, mat2_one]
  | succ n ih => rw [pow_succ, pow_succ, mat2_mul, ih]

theorem mat2_injective : Function.Injective mat2 := by
  intro g h e
  exact Units.ext (Subtype.ext e)

set_option maxRecDepth 4000 in
noncomputable def genA2 : NativeSporadic.Co2 :=
  (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.a (co2Data ()))

set_option maxRecDepth 4000 in
noncomputable def genB2 : NativeSporadic.Co2 :=
  (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.b (co2Data ()))

theorem mat2_genA2 :
    mat2 genA2 = rowsMatrix 22 (w12Co2RowsA ()) := by
  have h1 := unitsEquiv_val_gen (D := co2Data ()) co2BaseFacts
    ((unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.a (co2Data ())))
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm.trans ((SmallF2.a_val co2BaseFacts).trans
    (SmallF2.rowsMatrix_rowsA (co2Data ())).symm)

theorem mat2_genB2 :
    mat2 genB2 = rowsMatrix 22 (w12Co2RowsB ()) := by
  have h1 := unitsEquiv_val_gen (D := co2Data ()) co2BaseFacts
    ((unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.b (co2Data ())))
  rw [MulEquiv.apply_symm_apply] at h1
  exact h1.symm.trans ((SmallF2.b_val co2BaseFacts).trans
    (SmallF2.rowsMatrix_rowsB (co2Data ())).symm)

theorem closure_genAB :
    Subgroup.closure ({genA2, genB2} : Set G2) = ⊤ := by
  have hA : (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.a (co2Data ())) =
      genA2 := rfl
  have hB : (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm (SmallF2.b (co2Data ())) =
      genB2 := rfl
  rw [eq_top_iff]
  intro u _
  have hx : (unitsEquiv_gen (D := co2Data ()) co2BaseFacts) u ∈ Subgroup.closure
      ({SmallF2.a (co2Data ()), SmallF2.b (co2Data ())} : Set (SmallF2.J (co2Data ()))) := by
    rw [SmallF2.closure_ab]
    trivial
  have key : ∀ x ∈ Subgroup.closure
      ({SmallF2.a (co2Data ()), SmallF2.b (co2Data ())} : Set (SmallF2.J (co2Data ()))),
      (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm x ∈
        Subgroup.closure ({genA2, genB2} : Set G2) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · rw [hA]; exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [hB]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    | one => rw [map_one]; exact one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact inv_mem hx
  have := key _ hx
  have e1 : (unitsEquiv_gen (D := co2Data ()) co2BaseFacts).symm
      ((unitsEquiv_gen (D := co2Data ()) co2BaseFacts) u) = u :=
    MulEquiv.symm_apply_apply _ u
  rw [e1] at this
  exact this

@[expose] noncomputable def wd (w : List Bool) : G2 :=
  w.foldl (fun acc b => acc * (if b then genA2 else genB2)) 1

theorem mat2_letter (b : Bool) :
    mat2 (if b then genA2 else genB2) =
      rowsMatrix 22 (if b then w12Co2RowsA () else w12Co2RowsB ()) := by
  cases b
  · exact mat2_genB2
  · exact mat2_genA2

theorem mat2_fold_aux (w : List Bool) :
    ∀ (acc : G2) (accRows : Array ℕ), mat2 acc = rowsMatrix 22 accRows →
      mat2 (w.foldl (fun acc b => acc * (if b then genA2 else genB2)) acc) =
        rowsMatrix 22 (w.foldl (fun acc b =>
          mulRows 22 acc (if b then w12Co2RowsA () else w12Co2RowsB ())) accRows) := by
  induction w with
  | nil => intro acc accRows h; exact h
  | cons b w ih =>
    intro acc accRows h
    simp only [List.foldl_cons]
    apply ih
    rw [mat2_mul, h, mat2_letter, rowsMatrix_mulRows]

theorem mat2_wd (w : List Bool) :
    mat2 (wd w) = rowsMatrix 22 (w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) w) := by
  unfold wd w12WordRows
  exact mat2_fold_aux w 1 (idRows 22) (by rw [mat2_one, rowsMatrix_idRows])

@[expose] noncomputable def gen (i : ℕ) : G2 :=
  wd (w12UParse (w12UWords.getD i ""))

private theorem getD_map_lt {α β : Type} (f : α → β) (a : Array α) (i : ℕ) (h : i < a.size)
    (d : α) (e : β) : (a.map f).getD i e = f (a.getD i d) := by
  simp [Array.getD, h]

theorem mat2_gen (i : ℕ) (hi : i < 33) :
    mat2 (gen i) = rowsMatrix 22 ((w12URows ()).getD i #[]) := by
  have hsz : w12UWords.size = 33 := rfl
  have hs : i < w12UWords.size := by omega
  have hget : (w12URows ()).getD i #[] =
      w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) (w12UParse (w12UWords.getD i "")) := by
    unfold w12URows
    rw [getD_map_lt _ _ _ hs "" #[]]
  rw [hget]
  unfold gen
  exact mat2_wd _

@[expose] noncomputable def evalE (L : List (ℕ × ℕ)) : G2 :=
  (L.map fun q => gen q.1 ^ q.2).prod

theorem evalE_nil : evalE [] = 1 := rfl

theorem evalE_cons (q : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    evalE (q :: L) = gen q.1 ^ q.2 * evalE L := by
  simp [evalE]

theorem evalE_append (L L' : List (ℕ × ℕ)) :
    evalE (L ++ L') = evalE L * evalE L' := by
  simp only [evalE, List.map_append, List.prod_append]

private theorem prod_map_foldl {M : Type} [Monoid M] (f : ℕ × ℕ → M) (L : List (ℕ × ℕ)) :
    ∀ acc : M, acc * (L.map f).prod = L.foldl (fun acc q => acc * f q) acc := by
  induction L with
  | nil => intro acc; simp
  | cons q L ih =>
    intro acc
    rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
    exact ih (acc * f q)

private theorem evalE_foldl (L : List (ℕ × ℕ)) :
    evalE L = L.foldl (fun acc q => acc * gen q.1 ^ q.2) 1 := by
  have h := prod_map_foldl (fun q : ℕ × ℕ => gen q.1 ^ q.2) L 1
  rw [one_mul] at h
  exact h

private theorem mat2_gen_pow (q : ℕ × ℕ) (hq : q.1 < 33) :
    mat2 (gen q.1 ^ q.2) = rowsMatrix 22 (powRows 22 ((w12URows ())[q.1]!) q.2) := by
  rw [mat2_pow, mat2_gen q.1 hq, rowsMatrix_powRows]
  rfl

private theorem mat2_foldl_aux (L : List (ℕ × ℕ))
    (hL : ∀ q ∈ L, q.1 < 33) :
    ∀ (acc : G2) (accRows : Array ℕ), mat2 acc = rowsMatrix 22 accRows →
      mat2 (L.foldl (fun acc q => acc * gen q.1 ^ q.2) acc) =
        rowsMatrix 22 (L.foldl (fun acc q =>
          mulRows 22 acc (powRows 22 ((w12URows ())[q.1]!) q.2)) accRows) := by
  induction L with
  | nil => intro acc accRows h; exact h
  | cons q L ih =>
    intro acc accRows h
    simp only [List.foldl_cons]
    apply ih (fun q' hq' => hL q' (List.mem_cons.2 (Or.inr hq')))
    rw [mat2_mul, h, mat2_gen_pow q (hL q (List.mem_cons.2 (Or.inl rfl))), rowsMatrix_mulRows]

theorem mat2_evalE (L : List (ℕ × ℕ)) (hL : ∀ q ∈ L, q.1 < 33) :
    mat2 (evalE L) = rowsMatrix 22 (w12UEvalE (w12URows ()) L) := by
  rw [evalE_foldl]
  unfold w12UEvalE
  exact mat2_foldl_aux L hL 1 (idRows 22) (by rw [mat2_one, rowsMatrix_idRows])

private theorem idx_of_ok (L : List (ℕ × ℕ)) (h : w12UIdxOk L = true) : ∀ r ∈ L, r.1 < 33 := by
  intro r hr
  unfold w12UIdxOk at h
  have := List.all_eq_true.1 h r hr
  simpa using this

theorem eqCheck_sound
    {eqs : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (h : w12UEqCheck (w12URows ()) eqs = true) : ∀ q ∈ eqs, evalE q.1 = evalE q.2 := by
  intro q hq
  have hq' := List.all_eq_true.1 h q hq
  simp only [Bool.and_eq_true] at hq'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hq'
  apply mat2_injective
  rw [mat2_evalE q.1 (idx_of_ok q.1 h1), mat2_evalE q.2 (idx_of_ok q.2 h2)]
  exact w12UEqR_iff.1 h3

theorem powCheck_sound
    {ps : List (List (ℕ × ℕ) × ℕ)}
    (h : w12UPowCheck (w12URows ()) ps = true) : ∀ q ∈ ps, evalE q.1 ^ q.2 = 1 := by
  intro q hq
  have hq' := List.all_eq_true.1 h q hq
  simp only [Bool.and_eq_true] at hq'
  obtain ⟨h1, h2⟩ := hq'
  have h3 := w12UEqR_iff.1 h2
  rw [rowsMatrix_powRows, rowsMatrix_idRows] at h3
  apply mat2_injective
  rw [mat2_pow, mat2_evalE q.1 (idx_of_ok q.1 h1), mat2_one]
  exact h3

private theorem pow_eq_pow_mod' {M : Type} [Monoid M] {x : M} {n : ℕ} (m : ℕ) (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) := by
  conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, h, one_pow, one_mul]

private theorem gen_pow_inv (i e : ℕ)
    (hord : gen i ^ w12UOrd i = 1) (hpos : 0 < w12UOrd i) :
    gen i ^ (w12UOrd i - e % w12UOrd i) = (gen i ^ e)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [pow_eq_pow_mod' e hord, ← pow_add, Nat.add_sub_of_le (Nat.mod_lt e hpos).le, hord]

private theorem w12UInv_cons (q : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    w12UInv (q :: L) = w12UInv L ++ [(q.1, w12UOrd q.1 - q.2 % w12UOrd q.1)] := by
  unfold w12UInv
  simp [List.reverse_cons, List.map_append]

theorem evalE_inv (hord : ∀ i, gen i ^ w12UOrd i = 1)
    (hpos : ∀ i, 0 < w12UOrd i) (L : List (ℕ × ℕ)) :
    evalE (w12UInv L) = (evalE L)⁻¹ := by
  induction L with
  | nil =>
    show evalE [] = (evalE [])⁻¹
    rw [evalE_nil, inv_one]
  | cons q L ih =>
    rw [w12UInv_cons, evalE_append, ih, evalE_cons, evalE_cons, evalE_nil, mul_one,
      _root_.mul_inv_rev]
    congr 1
    exact gen_pow_inv q.1 q.2 (hord q.1) (hpos q.1)

end CFSG.GF2Type.Widths1112.Co2Module

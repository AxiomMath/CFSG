module

public import Certificates.Data.CFSGNative.F3.Sep
public import CFSG.F3.Spec

public section

namespace CFSG.F3.Native

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def vecOf (d : ℕ) (v : V) : Fin d → ZMod 3 := fun j => v.val j.val

theorem vecOf_mulVecM {d : ℕ} (M : Array V) {v : V} (hv : v.wf = true) :
    vecOf d (mulVecM d M v) = (toMat d M).mulVec (vecOf d v) := by
  funext r
  unfold vecOf mulVecM
  rw [V.val_comb d _ v (RowsWF.transpose d M) hv, mulVec, dotProduct,
    Finset.sum_range (fun j => v.val j * (transpose d M)[j]!.val r.val)]
  apply Finset.sum_congr rfl
  intro j _
  have := congrFun (congrFun (toMat_transpose (d := d) M) j) r
  rw [toMat_apply, Matrix.transpose_apply, toMat_apply] at this
  rw [this, mul_comm]
  rfl

theorem V.wf_mulVecM {d : ℕ} (M : Array V) {v : V} (hv : v.wf = true) :
    (mulVecM d M v).wf = true :=
  V.wf_comb d _ v (RowsWF.transpose d M) hv

theorem RowsWF.zeroM (d : ℕ) : RowsWF (zeroM d) := by
  intro j
  unfold Native.zeroM
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]; exact V.wf_zero
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

theorem toMat_zeroM (d : ℕ) : toMat d (zeroM d) = 0 := by
  ext i j
  rw [toMat_apply]
  unfold Native.zeroM
  rw [getElem!_pos _ i.val (by simp), Array.getElem_replicate, V.val_zero]
  rfl

theorem zeroM_size (d : ℕ) : (zeroM d).size = d := by unfold Native.zeroM; simp

theorem RowsWF.addM (d : ℕ) {X Y : Array V} (hX : RowsWF X) (hY : RowsWF Y) :
    RowsWF (addM d X Y) := by
  intro j
  unfold Native.addM
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]; exact V.wf_add (hX j) (hY j)
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

theorem addM_size (d : ℕ) (X Y : Array V) : (addM d X Y).size = d := by
  unfold Native.addM; simp

theorem toMat_addM (d : ℕ) {X Y : Array V} (hX : RowsWF X) (hY : RowsWF Y) :
    toMat d (addM d X Y) = toMat d X + toMat d Y := by
  ext i j
  rw [Matrix.add_apply, toMat_apply, toMat_apply, toMat_apply]
  unfold Native.addM
  rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn, V.val_add (hX _) (hY _)]

theorem RowsWF.negM {X : Array V} (hX : RowsWF X) : RowsWF (negM X) := by
  intro j
  unfold Native.negM
  by_cases hj : j < X.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map]
    have := hX j
    rw [getElem!_pos X j hj] at this
    exact V.wf_neg this
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

theorem toMat_negM {d : ℕ} {X : Array V} (hXs : X.size = d) (hX : RowsWF X) :
    toMat d (negM X) = -toMat d X := by
  ext i j
  rw [Matrix.neg_apply, toMat_apply, toMat_apply]
  unfold Native.negM
  have hi : i.val < X.size := by rw [hXs]; exact i.isLt
  rw [getElem!_pos _ i.val (by simpa using hi), Array.getElem_map]
  have := hX i.val
  rw [getElem!_pos X i.val hi] at this ⊢
  exact V.val_neg _ _ this

theorem negM_size (X : Array V) : (negM X).size = X.size := by unfold Native.negM; simp

theorem idM_size (d : ℕ) : (idM d).size = d := by unfold Native.idM; simp

theorem mul_size (d : ℕ) (X Y : Array V) : (mul d X Y).size = X.size := by
  unfold Native.mul; simp

section Algebra

variable {d : ℕ} (mats : Array (Array V))

@[expose] noncomputable def matsAlgebra : Subalgebra (ZMod 3) (Matrix (Fin d) (Fin d) (ZMod 3)) :=
  Algebra.adjoin (ZMod 3) {M | ∃ i < mats.size, M = toMat d mats[i]!}

variable {mats}

theorem prodM_spec (hm : ∀ i < mats.size, RowsWF mats[i]!) (w : List ℕ)
    (hw : ∀ x ∈ w, x < mats.size) :
    ∀ M0 : Array V, M0.size = d → RowsWF M0 → toMat d M0 ∈ matsAlgebra (d := d) mats →
      (w.foldl (fun M x => mul d M mats[x]!) M0).size = d ∧
        RowsWF (w.foldl (fun M x => mul d M mats[x]!) M0) ∧
        toMat d (w.foldl (fun M x => mul d M mats[x]!) M0) ∈ matsAlgebra (d := d) mats := by
  induction w with
  | nil => intro M0 h1 h2 h3; exact ⟨h1, h2, h3⟩
  | cons x w ih =>
    intro M0 h1 h2 h3
    have hx : x < mats.size := hw x (List.mem_cons_self ..)
    rw [List.foldl_cons]
    refine ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) _ (by rw [mul_size, h1])
      (RowsWF.mul _ d h2 (hm x hx)) ?_
    rw [toMat_mul h1 h2 (hm x hx)]
    exact Subalgebra.mul_mem _ h3 (Algebra.subset_adjoin ⟨x, hx, rfl⟩)

theorem combM_spec (hm : ∀ i < mats.size, RowsWF mats[i]!) (terms : List (ℕ × List ℕ))
    (ht : ∀ t ∈ terms, ∀ x ∈ t.2, x < mats.size) :
    ∀ M0 : Array V, M0.size = d → RowsWF M0 → toMat d M0 ∈ matsAlgebra (d := d) mats →
      RowsWF (terms.foldl (fun acc t => let M := prodM d mats t.2
          addM d acc (if t.1 == 2 then negM M else M)) M0) ∧
        toMat d (terms.foldl (fun acc t => let M := prodM d mats t.2
          addM d acc (if t.1 == 2 then negM M else M)) M0) ∈ matsAlgebra (d := d) mats := by
  induction terms with
  | nil => intro M0 _ h2 h3; exact ⟨h2, h3⟩
  | cons t terms ih =>
    intro M0 h1 h2 h3
    rw [List.foldl_cons]
    obtain ⟨hps, hpw, hpm⟩ := prodM_spec hm t.2 (ht t (List.mem_cons_self ..)) (idM d)
      (idM_size d) (RowsWF.idM d) (by rw [toMat_idM]; exact Subalgebra.one_mem _)
    change (prodM d mats t.2).size = d at hps
    change RowsWF (prodM d mats t.2) at hpw
    change toMat d (prodM d mats t.2) ∈ matsAlgebra mats at hpm
    have hP : RowsWF (if t.1 == 2 then negM (prodM d mats t.2) else prodM d mats t.2) ∧
        toMat d (if t.1 == 2 then negM (prodM d mats t.2) else prodM d mats t.2) ∈
          matsAlgebra (d := d) mats := by
      split_ifs
      · refine ⟨RowsWF.negM hpw, ?_⟩
        rw [toMat_negM hps hpw]
        exact Subalgebra.neg_mem _ hpm
      · exact ⟨hpw, hpm⟩
    refine ih (fun s hs => ht s (List.mem_cons_of_mem _ hs)) _ (addM_size d _ _)
      (RowsWF.addM d h2 hP.1) ?_
    rw [toMat_addM d h2 hP.1]
    exact Subalgebra.add_mem _ h3 hP.2

end Algebra

theorem V.val_unit (i j : ℕ) : (⟨1 <<< i, 0⟩ : V).val j = if j = i then 1 else 0 := by
  rw [V.val_eq_bitVal]
  simp only [testBit_one_shiftLeft, Nat.zero_testBit, bitVal]
  by_cases h : j = i <;> simp [h]

theorem V.wf_unit (i : ℕ) : (⟨1 <<< i, 0⟩ : V).wf = true := by
  apply V.wf_of_bits; intro j; simp

theorem V.val_unit2 (i j : ℕ) : (⟨0, 1 <<< i⟩ : V).val j = if j = i then 2 else 0 := by
  rw [V.val_eq_bitVal]
  simp only [testBit_one_shiftLeft, Nat.zero_testBit, bitVal]
  by_cases h : j = i <;> simp [h]

theorem V.val_outerRow {v : V} (hv : v.wf = true) (k i j : ℕ) :
    (outerRow v k i).val j = v.val i * (if j = k then 1 else 0) := by
  have hb := V.not_both hv i
  have hvi : v.val i = (v.get i : ZMod 3) := rfl
  unfold outerRow
  rw [hvi]
  unfold V.get
  rcases hp : v.p.testBit i <;> rcases hm : v.m.testBit i
  · simp only [Bool.false_eq_true, ite_false]
    rw [ite_eq_right (by decide : (0 : ℕ) ≠ 1), ite_eq_right (by decide : (0 : ℕ) ≠ 2)]
    rw [V.val_zero]; simp
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1), V.val_unit2]
    by_cases hjk : j = k <;> simp [hjk]
  · simp only [ite_true]
    rw [V.val_unit]
    by_cases hjk : j = k <;> simp [hjk]
  · rw [hp, hm] at hb; exact absurd hb (by decide)

theorem V.wf_outerRow (v : V) (k i : ℕ) : (outerRow v k i).wf = true := by
  unfold outerRow
  split_ifs
  · apply V.wf_of_bits; intro j; simp
  · apply V.wf_of_bits; intro j; simp
  · exact V.wf_zero

theorem mulVec_projM {d : ℕ} {v : V} (hv : v.wf = true) {k : ℕ} (hk : k < d)
    (y : Fin d → ZMod 3) :
    (toMat d (projM d v k)).mulVec y = y - y ⟨k, hk⟩ • vecOf d v := by
  funext r
  rw [mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hrow : ∀ j : Fin d, toMat d (projM d v k) r j =
      (if j = r then 1 else 0) - v.val r.val * (if j = ⟨k, hk⟩ then 1 else 0) := by
    intro j
    rw [toMat_apply]
    unfold projM
    rw [getElem!_pos _ r.val (by simp), Array.getElem_ofFn,
      V.val_sub (V.wf_unit _) (V.wf_outerRow v k _), V.val_unit, V.val_outerRow hv]
    congr 1
    · by_cases h : j = r
      · subst h; simp
      · have : j.val ≠ r.val := fun e => h (Fin.ext e)
        simp [h, this]
    · congr 1
      by_cases h : j = ⟨k, hk⟩
      · subst h; simp
      · have : j.val ≠ k := fun e => h (Fin.ext e)
        simp [h, this]
  simp only [hrow, sub_mul, ite_mul, one_mul, zero_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ r, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin d)]
  simp only [Finset.mem_univ, ite_true]
  unfold vecOf
  rw [mul_comm (y ⟨k, hk⟩)]

theorem getElem!_push' {α : Type*} [Inhabited α] (a : Array α) (x : α) (i : ℕ) :
    (a.push x)[i]! = if i < a.size then a[i]! else if i = a.size then x else default := by
  by_cases h1 : i < a.size
  · rw [ite_eq_left h1, getElem!_pos _ i (by simp; omega), getElem!_pos a i h1,
      Array.getElem_push_lt h1]
  · rw [ite_eq_right h1]
    by_cases h2 : i = a.size
    · subst h2; rw [ite_eq_left rfl, getElem!_pos _ _ (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h2, getElem!_neg _ i (by simp; omega)]

theorem spin_spec {d : ℕ} {mats : Array (Array V)} {v : V} (tree : List (ℕ × ℕ)) :
    ∀ S : Array V, (∀ i : ℕ, (S[i]!).wf = true ∧
        ∃ N ∈ matsAlgebra (d := d) mats, vecOf d S[i]! = N.mulVec (vecOf d v)) →
      ∀ i : ℕ, ((tree.foldl (fun S t => S.push (mulVecM d mats[t.2]! S[t.1]!)) S)[i]!).wf = true ∧
        ∃ N ∈ matsAlgebra (d := d) mats,
          vecOf d (tree.foldl (fun S t => S.push (mulVecM d mats[t.2]! S[t.1]!)) S)[i]! =
            N.mulVec (vecOf d v) := by
  induction tree with
  | nil => intro S hS; exact hS
  | cons t tree ih =>
    intro S hS
    rw [List.foldl_cons]
    apply ih
    intro i
    rw [getElem!_push']
    split_ifs with h1 h2
    · exact hS i
    · obtain ⟨hw, N, hN, he⟩ := hS t.1
      refine ⟨V.wf_mulVecM _ hw, ?_⟩
      by_cases hr : t.2 < mats.size
      · refine ⟨toMat d mats[t.2]! * N, Subalgebra.mul_mem _
          (Algebra.subset_adjoin ⟨t.2, hr, rfl⟩) hN, ?_⟩
        rw [vecOf_mulVecM _ hw, he, mulVec_mulVec]
      · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
        rw [vecOf_mulVecM _ hw, getElem!_neg mats t.2 hr, zero_mulVec]
        have h0 : ∀ i : ℕ, ((default : Array V)[i]!).val = fun _ => 0 := fun i => by
          rw [getElem!_neg _ i (by exact Nat.not_lt_zero _)]
          funext j
          exact V.val_zero j
        funext r
        rw [mulVec, dotProduct]
        simp only [toMat_apply, h0, zero_mul, Finset.sum_const_zero]
        rfl
    · refine ⟨V.wf_zero, 0, Subalgebra.zero_mem _, ?_⟩
      funext r
      rw [zero_mulVec]
      exact V.val_zero _

theorem scalar_of_sepOK {d : ℕ} {mats : Array (Array V)} {terms : List (ℕ × List ℕ)} {v : V}
    {k : ℕ} {P Tinv : Array V} {tree : List (ℕ × ℕ)}
    (h : sepOK d mats terms v k P Tinv tree = true) (g : Matrix (Fin d) (Fin d) (ZMod 3))
    (hg : ∀ i < mats.size, g * toMat d mats[i]! = toMat d mats[i]! * g) :
    ∃ c : ZMod 3, g = c • 1 := by
  unfold sepOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hvc⟩, hvk⟩, hmats⟩, hPwf⟩, hTwf⟩, hPs⟩, hTs⟩, hterms⟩, hwv⟩, hPw⟩,
    -⟩, -⟩, hSs⟩, hTS⟩ := h
  have hv : v.wf = true := by
    unfold V.canon at hvc; simp only [Bool.and_eq_true] at hvc; exact hvc.1.1
  have hm : ∀ i < mats.size, RowsWF mats[i]! := fun i hi => by
    rw [getElem!_pos mats i hi]; exact rowsWF_of_wfM (hmats i hi)
  have hcomm : ∀ N ∈ matsAlgebra (d := d) mats, g * N = N * g := by
    intro N hN
    have hle : matsAlgebra (d := d) mats ≤ Subalgebra.centralizer (ZMod 3) {g} := by
      unfold matsAlgebra
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hg i hi
    have := hle hN
    rw [Subalgebra.mem_centralizer_iff] at this
    exact this g rfl
  set x := vecOf d v with hx
  obtain ⟨hwwf, hwmem⟩ := combM_spec hm terms (fun t ht y hy => hterms t ht y hy) (zeroM d)
    (zeroM_size d) (RowsWF.zeroM d) (by rw [toMat_zeroM]; exact Subalgebra.zero_mem _)
  change RowsWF (combM d mats terms) at hwwf
  change toMat d (combM d mats terms) ∈ matsAlgebra mats at hwmem
  set W := toMat d (combM d mats terms)
  have hWx : W.mulVec x = 0 := by
    have := vecOf_mulVecM (d := d) (combM d mats terms) hv
    rw [← this]
    funext r
    unfold V.isZero at hwv
    simp only [Bool.and_eq_true, beq_iff_eq] at hwv
    rw [vecOf, V.val_eq_bitVal, hwv.1, hwv.2]
    simp [bitVal]
  set y := g.mulVec x
  have hWy : W.mulVec y = 0 := by
    rw [mulVec_mulVec, ← hcomm W hwmem, ← mulVec_mulVec, hWx, mulVec_zero]
  have hPW := toMat_eq_of_eqM hPw
  rw [toMat_mul hPs (rowsWF_of_wfM hPwf) hwwf] at hPW
  have hy : y = y ⟨k, hk⟩ • x := by
    have h1 := mulVec_projM hv hk y
    rw [← hPW, ← mulVec_mulVec, hWy, mulVec_zero] at h1
    exact (sub_eq_zero.1 h1.symm)
  set c := y ⟨k, hk⟩
  set S := spinVecs d mats v tree
  have hS0 : ∀ i : ℕ, ((#[v] : Array V)[i]!).wf = true ∧
      ∃ N ∈ matsAlgebra (d := d) mats, vecOf d (#[v] : Array V)[i]! = N.mulVec x := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact ⟨hv, 1, Subalgebra.one_mem _, by simp [hx]⟩
    · rw [getElem!_neg _ i (by simp; omega)]
      refine ⟨V.wf_zero, 0, Subalgebra.zero_mem _, ?_⟩
      funext r
      rw [zero_mulVec]
      exact V.val_zero _
  have hSpec := spin_spec (d := d) tree #[v] hS0
  have hSc : ∀ i : ℕ, g.mulVec (vecOf d S[i]!) = c • vecOf d S[i]! := by
    intro i
    obtain ⟨-, N, hN, he⟩ := hSpec i
    change vecOf d S[i]! = N.mulVec x at he
    rw [he, mulVec_mulVec, hcomm N hN, ← mulVec_mulVec]
    change N.mulVec y = c • N.mulVec x
    rw [hy, mulVec_smul]
  set T := toMat d S
  have hTinv := toMat_eq_of_eqM hTS
  have hSwf : RowsWF S := fun i => (hSpec i).1
  rw [toMat_mul hTs (rowsWF_of_wfM hTwf) hSwf, toMat_idM] at hTinv
  have hgT : g * Tᵀ = c • Tᵀ := by
    ext r i
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply]
    have := congrFun (hSc i.val) r
    rw [mulVec, dotProduct, Pi.smul_apply] at this
    simpa [T, toMat_apply, vecOf] using this
  have hright : Tᵀ * (toMat d Tinv)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTinv, Matrix.transpose_one]
  refine ⟨c, ?_⟩
  calc g = g * (Tᵀ * (toMat d Tinv)ᵀ) := by rw [hright, mul_one]
    _ = (g * Tᵀ) * (toMat d Tinv)ᵀ := by rw [mul_assoc]
    _ = c • 1 := by rw [hgT, smul_mul_assoc, hright]

end CFSG.F3.Native

module

public import CFSG.Fischer.F4Code
public import CFSG.Fischer.UnitaryCounts
public import CFSG.Fischer.OrbitBound
import all CFSG.Fischer.F4
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Fischer

open Matrix

abbrev W := Fin 6 → F4

@[expose] def H0 : Matrix (Fin 6) (Fin 6) F4 := 1

@[expose] def herm (x y : W) : F4 := ∑ i, ∑ j, x i * H0 i j * (y j) ^ 2

theorem herm_eq (x y : W) : herm x y = ∑ i, x i * (y i) ^ 2 := by
  unfold herm
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [H0]
  · intro j _ hj
    simp [H0, Ne.symm hj]
  · simp

@[expose] def IsIsom (g : Matrix (Fin 6) (Fin 6) F4) : Prop :=
  ∀ x y : W, herm (g.mulVec x) (g.mulVec y) = herm x y

@[expose] def GU0 : Subgroup (GL (Fin 6) F4) where
  carrier := {g | IsIsom (g : Matrix (Fin 6) (Fin 6) F4)}
  mul_mem' := by
    intro g h hg hh x y
    simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hg, hh]
  one_mem' := by
    intro x y
    simp
  inv_mem' := by
    intro g hg x y
    have e : ∀ z : W, (g : Matrix (Fin 6) (Fin 6) F4).mulVec
        (((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec z) = z := by
      intro z
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have h2 := hg (((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec x)
      (((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec y)
    rw [e, e] at h2
    exact h2.symm

@[expose] def SU0 : Subgroup (GL (Fin 6) F4) :=
  Subgroup.closure {g | Matrix.GeneralLinearGroup.det g = 1 ∧
    ∀ x y : W, herm ((g : Matrix (Fin 6) (Fin 6) F4).mulVec x)
      ((g : Matrix (Fin 6) (Fin 6) F4).mulVec y) = herm x y}

theorem SU0_le_GU0 : SU0 ≤ GU0 := by
  rw [SU0, Subgroup.closure_le]
  rintro g ⟨-, hg⟩
  exact hg

@[expose] def e (i : Fin 6) : W := Pi.single i 1

@[expose] def basisList : List W := List.ofFn e

@[expose] def cand (i : ℕ) : Finset W :=
  if h : i < 6 then
    Finset.univ.filter fun v : W => herm v v = herm (e ⟨i, h⟩) (e ⟨i, h⟩) ∧
      (∀ j : Fin 6, j.val < i → herm (e j) v = herm (e j) (e ⟨i, h⟩) ∧
        herm v (e j) = herm (e ⟨i, h⟩) (e j)) ∧
      ∃ k : Fin 6, i ≤ k.val ∧ v k ≠ 0
  else ∅

theorem herm_eq_std (x y : W) : herm x y = hermStd x y := by rw [herm_eq]; rfl

theorem codeOf_e (i : Fin 6) : codeOf (e i) = CFSG.F4.Native.eC i.val := by
  fin_cases i <;> decide

open CFSG.F4.Native in
theorem candC_codeOf {i : ℕ} (hi : i < 6) {v : W} (hv : v ∈ cand i) :
    candC i (codeOf v) = true := by
  unfold cand at hv
  rw [dite_eq_left hi, Finset.mem_filter] at hv
  obtain ⟨-, h1, h2, ⟨k, hk, hk0⟩⟩ := hv
  have hei : eC i = codeOf (e ⟨i, hi⟩) := (codeOf_e ⟨i, hi⟩).symm
  unfold candC
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.any_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hei, hermC_codeOf, hermC_codeOf, ← herm_eq_std, ← herm_eq_std, h1]
  · intro j hj
    have hj6 : j < 6 := by omega
    have hej : eC j = codeOf (e ⟨j, hj6⟩) := (codeOf_e ⟨j, hj6⟩).symm
    obtain ⟨h3, h4⟩ := h2 ⟨j, hj6⟩ hj
    rw [hej, hei, hermC_codeOf, hermC_codeOf, hermC_codeOf, hermC_codeOf, ← herm_eq_std,
      ← herm_eq_std, ← herm_eq_std, ← herm_eq_std, h3, h4]
    exact ⟨rfl, rfl⟩
  · refine ⟨k.val, k.isLt, hk, ?_⟩
    rw [coord_codeOf]
    intro h0
    exact hk0 (code_inj (by rw [h0]; rfl))

open CFSG.F4.Native in
theorem card_cand_le {i : ℕ} (hi : i < 6) : (cand i).card ≤ countC i := by
  have hsub :
      cand i ⊆ ((Finset.range 4096).filter (fun c => candC i c = true)).image vecOfCode := by
    intro v hv
    rw [Finset.mem_image]
    refine ⟨codeOf v, ?_, vecOfCode_codeOf v⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨codeOf_lt v, candC_codeOf hi hv⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq ?_))
  unfold countC
  rw [List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter, Finset.range, Multiset.range]

theorem basisList_length : basisList.length = 6 := by simp [basisList]

theorem basisList_getElem (i : ℕ) (hi : i < basisList.length) :
    basisList[i] = e ⟨i, by simpa [basisList_length] using hi⟩ := by
  simp only [basisList, List.getElem_ofFn]

theorem smul_eq_mulVec (g : GU0) (v : W) :
    g • v = ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).mulVec v := rfl

theorem mulVec_e (M : Matrix (Fin 6) (Fin 6) F4) (j : Fin 6) : M.mulVec (e j) = M.col j :=
  Matrix.mulVec_single_one M j

theorem eq_one_of_fix_basis (g : GU0) (h : ∀ p ∈ basisList, g • p = p) : g = 1 := by
  have hcol : ∀ j : Fin 6, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).col j = e j := by
    intro j
    rw [← mulVec_e, ← smul_eq_mulVec]
    exact h (e j) (List.mem_ofFn.2 ⟨j, rfl⟩)
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (hcol j) i
  rw [Matrix.col_apply] at this
  rw [this]
  simp [e, Pi.single_apply, Matrix.one_apply]

theorem herm_e_left (j : Fin 6) (v : W) : herm (e j) v = (v j) ^ 2 := by
  rw [herm_eq, Finset.sum_eq_single j]
  · simp [e]
  · intro k _ hk; simp [e, hk]
  · simp

theorem cand_mem {i : ℕ} (hi : i < 6) (g : GU0)
    (hg : ∀ j : Fin 6, j.val < i → g • e j = e j) : g • e ⟨i, hi⟩ ∈ cand i := by
  have hisom := g.property
  change IsIsom _ at hisom
  unfold cand
  rw [dite_eq_left hi, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
  · rw [smul_eq_mulVec, hisom]
  · intro j hj
    have hfix := hg j hj
    rw [smul_eq_mulVec] at hfix ⊢
    constructor
    · conv_lhs => rw [← hfix]
      rw [hisom]
    · conv_lhs => rw [← hfix]
      rw [hisom]
  · by_contra hall
    push Not at hall
    set w := g • e ⟨i, hi⟩ with hw
    set u : W := ∑ j : Fin 6, if j.val < i then w j • e j else 0 with hu
    have huw : u = w := by
      funext k
      simp only [hu, Finset.sum_apply, e]
      rw [Finset.sum_eq_single k]
      · by_cases hk : k.val < i
        · simp [hk]
        · simp [hk, hall k (by omega)]
      · intro j _ hjk
        by_cases hj : j.val < i
        · simp [hj, Ne.symm hjk]
        · simp [hj]
      · simp
    have hgu : g • u = u := by
      rw [hu, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < i
      · simp only [hj, ite_true]
        rw [smul_comm, hg j hj]
      · simp [hj]
    have : u = e ⟨i, hi⟩ := by
      apply smul_left_cancel g
      rw [hgu, huw]
    have h1 := congrFun this ⟨i, hi⟩
    rw [hu, Finset.sum_apply] at h1
    have h0 : ∑ c : Fin 6, (if c.val < i then w c • e c else 0) ⟨i, hi⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val < i
      · have hne : (⟨i, hi⟩ : Fin 6) ≠ c := fun h => by rw [← h] at hc; exact lt_irrefl _ hc
        simp [hc, e, hne]
      · simp [hc]
    rw [h0] at h1
    have : (e ⟨i, hi⟩) ⟨i, hi⟩ = 1 := by simp [e]
    rw [this] at h1
    exact zero_ne_one h1

theorem card_GU0_le : Nat.card GU0 ≤ 82771476480 := by
  have h := card_le_prod_of_candidates (G := GU0) basisList eq_one_of_fix_basis cand
    (fun i hi g hg => by
      rw [basisList_getElem]
      apply cand_mem
      intro j hj
      rw [mem_fixFirst] at hg
      have := hg j.val (by rw [basisList_length] at hi ⊢; omega)
      rwa [basisList_getElem] at this)
  rw [basisList_length] at h
  have h0 : (cand 0).card ≤ 2016 := countC_0 ▸ card_cand_le (by norm_num)
  have h1 : (cand 1).card ≤ 528 := countC_1 ▸ card_cand_le (by norm_num)
  have h2 : (cand 2).card ≤ 120 := countC_2 ▸ card_cand_le (by norm_num)
  have h3 : (cand 3).card ≤ 36 := countC_3 ▸ card_cand_le (by norm_num)
  have h4 : (cand 4).card ≤ 6 := countC_4 ▸ card_cand_le (by norm_num)
  have h5 : (cand 5).card ≤ 3 := countC_5 ▸ card_cand_le (by norm_num)
  let bound : ℕ → ℕ := fun i => [2016, 528, 120, 36, 6, 3].getD i 0
  have hb : ∀ i ∈ Finset.range 6, (cand i).card ≤ bound i := by
    intro i hi
    rw [Finset.mem_range] at hi
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  have hprod : ∏ i ∈ Finset.range 6, bound i = 82771476480 := by decide
  calc Nat.card GU0 ≤ _ := h
    _ ≤ ∏ i ∈ Finset.range 6, bound i := Finset.prod_le_prod hb
    _ = 82771476480 := hprod

@[expose] def SU0' : Subgroup (GL (Fin 6) F4) where
  carrier := {g | Matrix.GeneralLinearGroup.det g = 1 ∧ IsIsom (g : Matrix (Fin 6) (Fin 6) F4)}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    exact ⟨by rw [map_mul, hg1, hh1, one_mul], (GU0.mul_mem hg2 hh2 : _)⟩
  one_mem' := ⟨map_one _, GU0.one_mem⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    exact ⟨by rw [map_inv, hg1, inv_one], (GU0.inv_mem hg2 : _)⟩

theorem SU0_eq : SU0 = SU0' := by
  unfold SU0
  exact Subgroup.closure_eq SU0'

theorem mem_SU0 {g : GL (Fin 6) F4} :
    g ∈ SU0 ↔ Matrix.GeneralLinearGroup.det g = 1 ∧ IsIsom (g : Matrix (Fin 6) (Fin 6) F4) := by
  rw [SU0_eq]; rfl

@[expose] noncomputable def detGU : GU0 →* F4ˣ := Matrix.GeneralLinearGroup.det.comp GU0.subtype

theorem ker_detGU : detGU.ker = SU0.subgroupOf GU0 := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_SU0]
  exact ⟨fun h => ⟨h, g.property⟩, fun h => h.1⟩

@[expose] noncomputable def diagGL (c : F4ˣ) : GL (Fin 6) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => if i = 0 then (c : F4) else 1)
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_six]
      simp only [Fin.isValue, ite_true, show (1 : Fin 6) ≠ 0 by decide,
        show (2 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 0 by decide,
        show (4 : Fin 6) ≠ 0 by decide, show (5 : Fin 6) ≠ 0 by decide, ite_false, mul_one]
      exact c.ne_zero)

private theorem unit_cube : ∀ c : F4, c ≠ 0 → c * c ^ 2 = 1 := by decide

theorem diagGL_val (c : F4ˣ) : ((diagGL c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
    Matrix.diagonal fun i => if i = 0 then (c : F4) else 1 :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem diagGL_isom (c : F4ˣ) :
    IsIsom ((diagGL c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  intro x y
  rw [herm_eq, herm_eq, diagGL_val]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    rw [mul_pow, mul_mul_mul_comm, unit_cube _ c.ne_zero, one_mul]
  · simp [hi]

theorem det_diagGL (c : F4ˣ) : Matrix.GeneralLinearGroup.det (diagGL c) = c := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagGL_val, Matrix.det_diagonal, Fin.prod_univ_six]
  simp

@[expose] def unitOf (x : F4) (h : x ≠ 0) : F4ˣ := Units.mk0 x h

theorem three_le_card_range : 3 ≤ Nat.card detGU.range := by
  classical
  have hmem : ∀ c : F4ˣ, c ∈ detGU.range := by
    intro c
    exact ⟨⟨diagGL c, diagGL_isom c⟩, det_diagGL c⟩
  have : detGU.range = ⊤ := by
    rw [eq_top_iff]; intro c _; exact hmem c
  rw [this, Subgroup.card_top, Nat.card_units, Nat.card_eq_fintype_card, F4.card]

theorem card_SU0_mul_three_le : Nat.card SU0 * 3 ≤ Nat.card GU0 := by
  have h1 := Subgroup.card_mul_index detGU.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card detGU.ker = Nat.card SU0 := by
    rw [ker_detGU]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe SU0_le_GU0).toEquiv
  rw [← h1, h2]
  exact Nat.mul_le_mul_left _ three_le_card_range

@[expose] noncomputable def scalarGL (c : F4ˣ) : GL (Fin 6) F4 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((c : F4) • 1) (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero _ c.ne_zero)

private theorem unit_pow_six : ∀ c : F4, c ≠ 0 → c ^ 6 = 1 := by decide

theorem scalarGL_val (c : F4ˣ) :
    ((scalarGL c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = (c : F4) • 1 :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem scalarGL_mem (c : F4ˣ) : scalarGL c ∈ SU0 := by
  rw [mem_SU0]
  refine ⟨?_, ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_val, Matrix.det_smul, Matrix.det_one,
      mul_one, Fintype.card_fin, Units.val_one]
    exact unit_pow_six _ c.ne_zero
  · intro x y
    rw [scalarGL_val, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, herm_eq, herm_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_pow, mul_mul_mul_comm, unit_cube _ c.ne_zero, one_mul]

theorem scalarGL_central (c : F4ˣ) (g : GL (Fin 6) F4) : scalarGL c * g = g * scalarGL c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalarGL_val, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    mul_one]

theorem scalarGL_injective : Function.Injective scalarGL := by
  intro c d h
  have := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) 0 0) h
  simp only [scalarGL_val, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  exact Units.ext this

theorem three_le_card_center : 3 ≤ Nat.card (Subgroup.center SU0) := by
  classical
  let f : F4ˣ → Subgroup.center SU0 := fun c => ⟨⟨scalarGL c, scalarGL_mem c⟩, by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (scalarGL_central c g).symm⟩
  have hf : Function.Injective f := by
    intro c d h
    apply scalarGL_injective
    have := congrArg (fun z : Subgroup.center SU0 => ((z : SU0) : GL (Fin 6) F4)) h
    exact this
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_units] at this
  have h3 : Nat.card F4 - 1 = 3 := by rw [Nat.card_eq_fintype_card, F4.card]
  omega

theorem card_psu_le : Nat.card (SU0 ⧸ Subgroup.center SU0) ≤ 9196830720 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SU0)
  have h2 := card_SU0_mul_three_le
  have h3 := card_GU0_le
  have h4 := three_le_card_center
  have : Nat.card (SU0 ⧸ Subgroup.center SU0) * 9 ≤ 82771476480 := by nlinarith
  omega

end CFSG.Fischer

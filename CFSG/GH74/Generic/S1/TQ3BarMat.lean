module

public import CFSG.GH74.Generic.S1.BlkSplit

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def reflCent (F : Type) [Field F] (c : Fin 4) : Subgroup ↥(StatedSL 4 F) :=
  (Subgroup.centralizer ({reflDiag F c} : Set (GL (Fin 4) F))).comap (StatedSL 4 F).subtype

theorem mem_reflCent {c : Fin 4} {g : ↥(StatedSL 4 F)} :
    g ∈ reflCent F c ↔ (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) := by
  unfold reflCent
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  rfl

theorem entry_eq_zero_of_comm_refl (h2 : (2 : F) ≠ 0) {c : Fin 4} {g : GL (Fin 4) F}
    (h : g * reflDiag F c = reflDiag F c * g) {i j : Fin 4} (hij : i ≠ j) (hc : i = c ∨ j = c) :
    (g : Matrix (Fin 4) (Fin 4) F) i j = 0 := by
  have h0 := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul] at h0
  have h1 := congrFun (congrFun h0 i) j
  simp only [reflDiag, reflDiagMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  rcases hc with rfl | rfl
  · have hj : j ≠ i := hij.symm
    simp only [hj, ite_false, ite_true] at h1
    have : (2 : F) * (g : Matrix (Fin 4) (Fin 4) F) i j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left h2
  · simp only [hij, ite_false, ite_true] at h1
    have : (2 : F) * (g : Matrix (Fin 4) (Fin 4) F) i j = 0 := by linear_combination -h1
    exact (mul_eq_zero.1 this).resolve_left h2

theorem submatrix_mul_of_col_zero {c : Fin 4} {M N : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ i, i ≠ c → M i c = 0) :
    (M * N).submatrix c.succAbove c.succAbove =
      M.submatrix c.succAbove c.succAbove * N.submatrix c.succAbove c.succAbove := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fin.sum_univ_succAbove _ c, hM (c.succAbove i) (Fin.succAbove_ne c i), zero_mul, zero_add]

@[expose] noncomputable def toGL3 (h2 : (2 : F) ≠ 0) (c : Fin 4) (g : reflCent F c) :
    GL (Fin 3) F :=
  ⟨((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val.submatrix c.succAbove c.succAbove,
   ((g.1⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F).val.submatrix c.succAbove c.succAbove,
   by
     have hg : ∀ i, i ≠ c → ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val i c = 0 := fun i hi =>
       entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 g.2) hi (Or.inr rfl)
     rw [← submatrix_mul_of_col_zero hg]
     have : ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val *
         ((g.1⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F).val = 1 := by
       have := congrArg Units.val (mul_inv_cancel ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F))
       simp
     rw [this]
     ext i j
     simp [Matrix.one_apply, (Fin.succAbove_right_injective (p := c)).eq_iff],
   by
     have hg : ∀ i, i ≠ c → ((g.1⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F).val i c = 0 := fun i hi =>
       entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 (g⁻¹).2) hi (Or.inr rfl)
     rw [← submatrix_mul_of_col_zero hg]
     have : ((g.1⁻¹ : ↥(StatedSL 4 F)) : GL (Fin 4) F).val *
         ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val = 1 := by
       have := congrArg Units.val (inv_mul_cancel ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F))
       simp
     rw [this]
     ext i j
     simp [Matrix.one_apply, (Fin.succAbove_right_injective (p := c)).eq_iff]⟩

theorem det_eq_of_row_zero {c : Fin 4} {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ j, j ≠ c → M c j = 0) :
    M.det = M c c * (M.submatrix c.succAbove c.succAbove).det := by
  rw [Matrix.det_succ_row M c, Finset.sum_eq_single c]
  · have : ((-1 : F) ^ ((c : ℕ) + (c : ℕ))) = 1 := by
      rw [← two_mul]
      exact Even.neg_one_pow (even_two_mul _)
    rw [this, one_mul]
  · intro j _ hj
    rw [hM j hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem det_stated_eq_one (g : ↥(StatedSL 4 F)) :
    (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det = 1 := by
  have h1 : (g : GL (Fin 4) F) ∈ detOne F 4 := by
    rw [← statedSL_eq_detOne]
    exact g.2
  rw [mem_detOne] at h1
  exact h1

theorem toGL3_injective (h2 : (2 : F) ≠ 0) (c : Fin 4) : Function.Injective (toGL3 h2 c) := by
  intro g h hgh
  have hsub : ∀ i j : Fin 3,
      ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val (c.succAbove i) (c.succAbove j) =
        ((h.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val (c.succAbove i) (c.succAbove j) := by
    intro i j
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F) i j) hgh
    simpa [toGL3] using this
  have hgrow : ∀ j, j ≠ c → ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val c j = 0 := fun j hj =>
    entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 g.2) hj.symm (Or.inl rfl)
  have hhrow : ∀ j, j ≠ c → ((h.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val c j = 0 := fun j hj =>
    entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 h.2) hj.symm (Or.inl rfl)
  have hdg := det_eq_of_row_zero hgrow
  have hdh := det_eq_of_row_zero hhrow
  rw [det_stated_eq_one g.1] at hdg
  rw [det_stated_eq_one h.1] at hdh
  have hm : ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val.submatrix c.succAbove c.succAbove =
      ((h.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val.submatrix c.succAbove c.succAbove := by
    ext i j
    exact hsub i j
  have hcc : ((g.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val c c =
      ((h.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val c c := by
    rw [hm] at hdg
    set d : F :=
      (((h.1 : ↥(StatedSL 4 F)) : GL (Fin 4) F).val.submatrix c.succAbove c.succAbove).det
      with hd_def
    have hd : d ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdh
      exact one_ne_zero hdh
    exact mul_right_cancel₀ hd (hdg.symm.trans hdh)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext a b
  by_cases ha : a = c
  · by_cases hb : b = c
    · subst ha; subst hb; exact hcc
    · subst ha
      rw [hgrow b hb, hhrow b hb]
  · by_cases hb : b = c
    · subst hb
      rw [entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 g.2) ha (Or.inr rfl),
        entry_eq_zero_of_comm_refl h2 (mem_reflCent.1 h.2) ha (Or.inr rfl)]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq ha
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hb
      exact hsub i j

theorem card_reflCent_le [Finite F] (h2 : (2 : F) ≠ 0) (c : Fin 4) :
    Nat.card (reflCent F c) ≤ Nat.card (GL (Fin 3) F) :=
  Nat.card_le_card_of_injective _ (toGL3_injective h2 c)

theorem perfect_le_of_card_le_two_mul {X : Type*} [Group X] [Finite X] {C N P : Subgroup X}
    (hNC : N ≤ C) (hcard : Nat.card C ≤ 2 * Nat.card N) (hPC : P ≤ C) (hP : ⁅P, P⁆ = P) :
    P ≤ N := by
  set N' : Subgroup ↥C := N.subgroupOf C with hN'
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  have hpos : 0 < Nat.card N' := Nat.card_pos
  have hmul : N'.index * Nat.card N' = Nat.card C := Subgroup.index_mul_card N'
  have hidx : N'.index ≤ 2 := by
    by_contra h
    push Not at h
    have : 3 * Nat.card N' ≤ N'.index * Nat.card N' := Nat.mul_le_mul_right _ h
    rw [hmul] at this
    omega
  have hidx0 : N'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have key : ∀ a b : ↥C, ⁅a, b⁆ ∈ N' := by
    intro a b
    have h12 : N'.index = 1 ∨ N'.index = 2 := by omega
    rcases h12 with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      trivial
    · rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ N := Subgroup.commutator_le.2 fun a ha b hb => key ⟨a, hPC ha⟩ ⟨b, hPC hb⟩

theorem mat_eq_zblk_of_mem_blkLin (h2 : (2 : F) ≠ 0) {c d : Fin 4} (hcd : c ≠ d)
    {z : ↥(StatedSL 4 F)} (hz : z ∈ blkLin (F := F) c d) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F c d := by
  refine eq_zblk_of_involution h2 hcd (fun i j hij => hz i j hij) ?_ (det_stated_eq_one z) ?_
  · have := congrArg
      (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hz2
    simpa using this
  · intro h
    apply hz1
    exact Subtype.ext (Units.ext (by simpa using h))

end CFSG.GH74.Generic.S1

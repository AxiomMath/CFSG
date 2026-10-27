module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsSp4
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatalogueBSymplecticTwo

variable {F : Type} [Field F]

theorem exists_conj_field_of_odd [Finite F] {β : MulAut (StatedProj (StatedSp 2 F))} (hβ : Odd (orderOf β)) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), β = conjAut 2 F A * fieldAut 2 F σ := by
  obtain ⟨hTE, hform, hnorm, hindex⟩ := kernel_generation (K := F)
  have hfin : Finite (MulAut (StatedProj (StatedSp 2 F))) := finite_mulAut F
  have hmem : β ∈ spSemilinearAutGroup 2 F := by
    have := hnorm
    have hdvd : orderOf (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F) ∣ orderOf β :=
      orderOf_map_dvd (QuotientGroup.mk' (spSemilinearAutGroup 2 F)) β
    have hcard : orderOf (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F) ∣
        (spSemilinearAutGroup 2 F).index := orderOf_dvd_natCard _
    have hodd1 : Odd (orderOf (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F)) :=
      Odd.of_dvd_nat hβ hdvd
    have hone : orderOf (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F) = 1 := by
      have hpos : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hle : orderOf (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F) ≤ 2 :=
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hcard).trans hindex
      have hpos2 := orderOf_pos (QuotientGroup.mk β : MulAut (StatedProj (StatedSp 2 F)) ⧸ spSemilinearAutGroup 2 F)
      obtain ⟨k, hk⟩ := hodd1
      omega
    rw [orderOf_eq_one_iff] at hone
    exact (QuotientGroup.eq_one_iff β).1 hone
  rw [← hTE] at hmem
  exact hform β hmem

theorem trace_blk_two (g h : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (blk g h) = g 0 0 + g 1 1 + h 0 0 + h 1 1 := by
  simp [Matrix.trace, blk, diag2, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem conjField_apply_proj (A : gsp 2 F) (σ : F ≃+* F) (x : StatedSp 2 F) :
    (conjAut 2 F A * fieldAut 2 F σ) (proj 2 F x) = proj 2 F (conjSp 2 F A (fieldSp 2 F σ x)) := rfl

theorem coe_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (x : StatedSp 2 F) :
    (((conjSp 2 F A (fieldSp 2 F σ x) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [coe_conjSp, Units.val_mul, Units.val_mul]
  rfl


theorem ringEquiv_eq_one_of_trace (σ : F ≃+* F) (h2 : (2 : F) ≠ 0)
    (h : ∀ τ : F, σ τ = τ ∨ σ τ = -τ - 4) : σ = 1 := by
  ext τ
  by_contra hne
  have hστ : σ τ = -τ - 4 := (h τ).resolve_left hne
  have h22 : σ (τ + 2) = -τ - 2 := by
    rw [map_add, hστ, map_ofNat]
    ring
  have hne2 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  rcases h (τ + 2) with h3 | h3
  · rw [h22] at h3
    have h4 : (2 : F) * (τ + 2) = 0 := by linear_combination -h3
    have h5 : τ + 2 = 0 := (mul_eq_zero.1 h4).resolve_left h2
    have h6 : τ = -2 := by linear_combination h5
    apply hne
    rw [h6, map_neg, map_ofNat]
    rfl
  · rw [h22] at h3
    apply hne2
    linear_combination h3

theorem trace_conj_map (A : GL (Fin 2 ⊕ Fin 2) F) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (σ : F ≃+* F) :
    Matrix.trace ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * M.map σ *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = σ (Matrix.trace M) := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]
  simp [Matrix.trace]

theorem fieldAut_eq_one_of_fix (h2 : (2 : F) ≠ 0) (A : gsp 2 F) (σ : F ≃+* F)
    (hfix : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (conjAut 2 F A * fieldAut 2 F σ) (proj 2 F (blkSL F (g, 1))) = proj 2 F (blkSL F (g, 1))) :
    σ = 1 := by
  apply ringEquiv_eq_one_of_trace σ h2
  intro τ
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![τ, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have h := hfix g
  rw [conjField_apply_proj] at h
  have htr : Matrix.trace (((blkSL F (g, 1) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = τ + 2 := by
    rw [coe_blkSL, trace_blk_two]
    simp [g]
    ring
  have htr' := trace_conj_map (A : GL (Fin 2 ⊕ Fin 2) F)
    (((blkSL F (g, 1) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) σ
  rw [htr, ← coe_conjSp_fieldSp] at htr'
  rcases eq_or_eq_neg_of_proj_eq h with h1 | h1
  · left
    have := congrArg Matrix.trace h1
    rw [htr, htr', map_add, map_ofNat] at this
    linear_combination -this
  · right
    have := congrArg Matrix.trace h1
    rw [htr, Matrix.trace_neg, htr', map_add, map_ofNat] at this
    linear_combination this


theorem not_conj_eq_neg_unipotent (h2 : (2 : F) ≠ 0)
    (A : GL (Fin 2 ⊕ Fin 2) F) (E : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hE : E * E = 0)
    (h : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -(1 + E)) : False := by
  have hAA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * E * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hX
  have hXX : X * X = 0 := by
    have : X * X = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (E * E) * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      rw [hX]
      calc (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * E * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * E * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
          = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * E * (((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) * E * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
            simp only [Matrix.mul_assoc]
        _ = (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (E * E) * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    rw [this, hE, Matrix.mul_zero, Matrix.zero_mul]
  have hX2 : X = -(1 + 1 + E) := by
    have h' : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 + X := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hAA]
    rw [h'] at h
    have : X = -(1 + E) - 1 := by rw [← h]; abel
    rw [this]
    abel
  have h5 : (1 + 1 + E) * (1 + 1 + E) = 0 := by
    have : (1 + 1 + E) * (1 + 1 + E) = X * X := by rw [hX2]; noncomm_ring
    rw [this, hXX]
  have h4 : (1 - E) * ((1 + 1 + E) * (1 + 1 + E)) =
      (1 + 1) * (1 + 1) - (1 + 1 + 1) * (E * E) - E * (E * E) := by noncomm_ring
  rw [h5, Matrix.mul_zero, hE] at h4
  have h6 := congrFun (congrFun h4 (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h6
  apply h2
  linear_combination h6


theorem entries_of_commute_single {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    {a b : Fin 2 ⊕ Fin 2} (h : A * Matrix.single a b (1 : F) = Matrix.single a b (1 : F) * A) :
    (∀ i, i ≠ a → A i a = 0) ∧ (∀ j, j ≠ b → A b j = 0) ∧ A a a = A b b := by
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · have := congrFun (congrFun h i) b
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hi] at this
    simpa using this
  · have := congrFun (congrFun h a) j
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, Matrix.single_mul_apply_same] at this
    simpa using this.symm
  · have := congrFun (congrFun h a) b
    rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at this
    simpa using this

theorem eq_diagonal_of_commute_units {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h1 : A * Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) = Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) * A)
    (h2 : A * Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) = Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) * A)
    (h3 : A * Matrix.single (Sum.inl 1) (Sum.inr 1) (1 : F) = Matrix.single (Sum.inl 1) (Sum.inr 1) (1 : F) * A)
    (h4 : A * Matrix.single (Sum.inr 1) (Sum.inl 1) (1 : F) = Matrix.single (Sum.inr 1) (Sum.inl 1) (1 : F) * A) :
    ∃ a₁ a₂ : F, A = Matrix.diagonal (Sum.elim ![a₁, a₂] ![a₁, a₂]) := by
  obtain ⟨c1, -, e1⟩ := entries_of_commute_single h1
  obtain ⟨c2, -, e2⟩ := entries_of_commute_single h2
  obtain ⟨c3, -, e3⟩ := entries_of_commute_single h3
  obtain ⟨c4, -, e4⟩ := entries_of_commute_single h4
  refine ⟨A (Sum.inl 0) (Sum.inl 0), A (Sum.inl 1) (Sum.inl 1), ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rcases i with ⟨i, hi⟩ | ⟨i, hi⟩
    · interval_cases i
      · rfl
      · rfl
    · interval_cases i
      · exact e1.symm
      · exact e3.symm
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases j with ⟨j, hj⟩ | ⟨j, hj⟩
    · interval_cases j
      · exact c1 i (fun h => hij (by rw [h]; rfl))
      · exact c3 i (fun h => hij (by rw [h]; rfl))
    · interval_cases j
      · exact c2 i (fun h => hij (by rw [h]; rfl))
      · exact c4 i (fun h => hij (by rw [h]; rfl))


theorem commute_of_conjAut_fix (h2 : (2 : F) ≠ 0) (A : gsp 2 F) {x : StatedSp 2 F}
    {E : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hE : E * E = 0)
    (hx : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 + E)
    (hfix : conjAut 2 F A (proj 2 F x) = proj 2 F x) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * E =
      E * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [conjAut_proj] at hfix
  have hAi : (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (((conjSp 2 F A x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [coe_conjSp, Units.val_mul, Units.val_mul]
  rcases eq_or_eq_neg_of_proj_eq hfix with h1 | h1
  · rw [hc, hx] at h1
    have h3 : (1 + E) * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) := by
      calc (1 + E) * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
          = (((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) *
            (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *
            ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by rw [← h1]
        _ = ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) := by
            rw [Matrix.mul_assoc, hAi, Matrix.mul_one]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h3
    exact (add_left_cancel h3).symm
  · exfalso
    rw [hc, hx] at h1
    refine not_conj_eq_neg_unipotent h2 (A : GL (Fin 2 ⊕ Fin 2) F) E hE ?_
    calc ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) *
          (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        = -(-(((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (1 + E) *
          (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))) := (neg_neg _).symm
      _ = -(1 + E) := by rw [← h1]


theorem blk_transv_inl0 :
    blk (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : F) := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [blk, diag2]

theorem blk_transv_inr0 :
    blk (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (Sum.inr 0) (Sum.inl 0) (1 : F) := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [blk, diag2]

theorem blk_transv_inl1 :
    blk (1 : Matrix (Fin 2) (Fin 2) F) (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (Sum.inl 1) (Sum.inr 1) (1 : F) := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [blk, diag2]

theorem blk_transv_inr1 :
    blk (1 : Matrix (Fin 2) (Fin 2) F) (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) =
      1 + Matrix.single (Sum.inr 1) (Sum.inl 1) (1 : F) := by
  ext (x | x) (y | y) <;> fin_cases x <;> fin_cases y <;>
    simp [blk, diag2]


theorem single_sq_zero {a b : Fin 2 ⊕ Fin 2} (h : b ≠ a) :
    (Matrix.single a b (1 : F)) * Matrix.single a b (1 : F) = 0 := by
  simp [h]

theorem sq_eq_of_gsp_diagonal (A : gsp 2 F) {a₁ a₂ : F}
    (hAd : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Matrix.diagonal (Sum.elim ![a₁, a₂] ![a₁, a₂])) : a₁ * a₁ = a₂ * a₂ := by
  obtain ⟨μ, hμ⟩ := A.2
  have e1 := congrFun (congrFun hμ (Sum.inl 0)) (Sum.inr 0)
  have e2 := congrFun (congrFun hμ (Sum.inl 1)) (Sum.inr 1)
  rw [hAd] at e1 e2
  simp [formJ_eq_blk, blk, diag2, J₁, Matrix.mul_apply, Matrix.diagonal_apply] at e1 e2
  linear_combination e1 - e2

theorem conjAut_sq_eq_one (A : gsp 2 F) {a₁ a₂ : F}
    (hAd : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Matrix.diagonal (Sum.elim ![a₁, a₂] ![a₁, a₂])) : conjAut 2 F A * conjAut 2 F A = 1 := by
  have hsq := sq_eq_of_gsp_diagonal A hAd
  have hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (a₁ * a₁) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [hAd, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [hsq]
  rw [← map_mul]
  ext y
  obtain ⟨x, rfl⟩ := SymplecticHigher.proj_surjective (r := 2) (K := F) y
  rw [conjAut_proj]
  change proj 2 F (conjSp 2 F (A * A) x) = proj 2 F x
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have hcomm : ((A : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F)) * (x : GL (Fin 2 ⊕ Fin 2) F) =
      (x : GL (Fin 2 ⊕ Fin 2) F) * ((A : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F)) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hAA, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc (((A * A : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) * (x : GL (Fin 2 ⊕ Fin 2) F) *
        (((A * A : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F))⁻¹
      = (x : GL (Fin 2 ⊕ Fin 2) F) * ((A : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F)) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) * (A : GL (Fin 2 ⊕ Fin 2) F))⁻¹ := by
        rw [← hcomm]; rfl
    _ = x := mul_inv_cancel_right _ _

theorem odd_aut_fix_trivial [Finite F] (hodd : Odd (Nat.card F)) {β : MulAut (StatedProj (StatedSp 2 F))}
    (hβ : Odd (orderOf β)) (hfix1 : ∀ x ∈ E1 F, β x = x) (hfix2 : ∀ x ∈ E2 F, β x = x) : β = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨A, σ, hβeq⟩ := exists_conj_field_of_odd hβ
  have hσ : σ = 1 := by
    refine fieldAut_eq_one_of_fix h2 A σ fun g => ?_
    rw [← hβeq]
    exact hfix1 _ (mem_E1.2 ⟨g, rfl⟩)
  subst hσ
  rw [map_one, mul_one] at hβeq
  subst hβeq
  let g₁ : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let g₂ : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have c1 := commute_of_conjAut_fix h2 A (x := blkSL F (g₁, 1)) (E := Matrix.single (Sum.inl 0) (Sum.inr 0) 1)
    (single_sq_zero (by simp)) (by rw [coe_blkSL]; exact blk_transv_inl0) (hfix1 _ (mem_E1.2 ⟨g₁, rfl⟩))
  have c2 := commute_of_conjAut_fix h2 A (x := blkSL F (g₂, 1)) (E := Matrix.single (Sum.inr 0) (Sum.inl 0) 1)
    (single_sq_zero (by simp)) (by rw [coe_blkSL]; exact blk_transv_inr0) (hfix1 _ (mem_E1.2 ⟨g₂, rfl⟩))
  have c3 := commute_of_conjAut_fix h2 A (x := blkSL F (1, g₁)) (E := Matrix.single (Sum.inl 1) (Sum.inr 1) 1)
    (single_sq_zero (by simp)) (by rw [coe_blkSL]; exact blk_transv_inl1) (hfix2 _ (mem_E2.2 ⟨g₁, rfl⟩))
  have c4 := commute_of_conjAut_fix h2 A (x := blkSL F (1, g₂)) (E := Matrix.single (Sum.inr 1) (Sum.inl 1) 1)
    (single_sq_zero (by simp)) (by rw [coe_blkSL]; exact blk_transv_inr1) (hfix2 _ (mem_E2.2 ⟨g₂, rfl⟩))
  obtain ⟨a₁, a₂, hAd⟩ := eq_diagonal_of_commute_units c1 c2 c3 c4
  have hpow : conjAut 2 F A ^ 2 = 1 := by
    rw [pow_two]
    exact conjAut_sq_eq_one A hAd
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow) with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hβ
    exact absurd hβ (by decide)

end CFSG.GH74.GLS.Stage2.Local.P34

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

variable {k : Type*} [Field k]

section Paired

variable (σ : k →+* k) (m : ℕ)

theorem coe_mul_coe_inv_SL (g : SpecialLinearGroup (Fin m) k) :
    (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : SpecialLinearGroup (Fin m) k) :
      Matrix (Fin m) (Fin m) k) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]

theorem coe_inv_mul_coe_SL (g : SpecialLinearGroup (Fin m) k) :
    ((g⁻¹ : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) *
      (g : Matrix (Fin m) (Fin m) k) = 1 := by
  rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]

@[expose] def pairedSLUnit (g : SpecialLinearGroup (Fin m) k) : GL (Fin m ⊕ Fin m) k where
  val := fromBlocks (g : Matrix (Fin m) (Fin m) k) 0 0
    ((((SpecialLinearGroup.map σ g)⁻¹ : SpecialLinearGroup (Fin m) k) :
      Matrix (Fin m) (Fin m) k)ᵀ)
  inv := fromBlocks ((g⁻¹ : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) 0 0
    (((SpecialLinearGroup.map σ g : SpecialLinearGroup (Fin m) k) :
      Matrix (Fin m) (Fin m) k)ᵀ)
  val_inv := by
    simp only [fromBlocks_multiply, ← transpose_mul, coe_mul_coe_inv_SL]
    simp
  inv_val := by
    simp only [fromBlocks_multiply, ← transpose_mul, coe_inv_mul_coe_SL]
    simp

@[expose] def pairedSLHom : SpecialLinearGroup (Fin m) k →* GL (Fin m ⊕ Fin m) k :=
  MonoidHom.mk' (pairedSLUnit σ m) fun g h => Units.ext (by
    simp only [pairedSLUnit, Units.val_mul, fromBlocks_multiply, map_mul, _root_.mul_inv_rev,
      SpecialLinearGroup.coe_mul, transpose_mul]
    simp)

theorem pairedSLHom_coe (g : SpecialLinearGroup (Fin m) k) :
    ((pairedSLHom σ m g : GL (Fin m ⊕ Fin m) k) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k) =
      fromBlocks (g : Matrix (Fin m) (Fin m) k) 0 0
        ((((SpecialLinearGroup.map σ g)⁻¹ : SpecialLinearGroup (Fin m) k) :
          Matrix (Fin m) (Fin m) k)ᵀ) := rfl

variable {σ m}

theorem commute_fromBlocks_diag_iff (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k)
    (X Y : Matrix (Fin m) (Fin m) k) :
    fromBlocks X 0 0 Y * A = A * fromBlocks X 0 0 Y ↔
      X * A.toBlocks₁₁ = A.toBlocks₁₁ * X ∧ X * A.toBlocks₁₂ = A.toBlocks₁₂ * Y ∧
        Y * A.toBlocks₂₁ = A.toBlocks₂₁ * X ∧ Y * A.toBlocks₂₂ = A.toBlocks₂₂ * Y := by
  conv_lhs => rw [← fromBlocks_toBlocks A]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp

@[expose] def slTransvection {i j : Fin m} (hij : i ≠ j) (c : k) : SpecialLinearGroup (Fin m) k :=
  ⟨transvection i j c, det_transvection_of_ne i j hij c⟩

theorem coe_slTransvection {i j : Fin m} (hij : i ≠ j) (c : k) :
    ((slTransvection hij c : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      transvection i j c := rfl

theorem map_slTransvection {i j : Fin m} (hij : i ≠ j) (c : k) :
    SpecialLinearGroup.map σ (slTransvection hij c) = slTransvection hij (σ c) := by
  refine Subtype.ext ?_
  change σ.mapMatrix (transvection i j c) = transvection i j (σ c)
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all

theorem inv_slTransvection {i j : Fin m} (hij : i ≠ j) (c : k) :
    (slTransvection hij c)⁻¹ = slTransvection hij (-c) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change (slTransvection hij c : Matrix (Fin m) (Fin m) k) * slTransvection hij (-c) = 1
  rw [coe_slTransvection, coe_slTransvection, transvection_mul_transvection_same i j hij,
    add_neg_cancel, transvection_zero]

theorem transpose_transvection (i j : Fin m) (c : k) :
    (transvection i j c)ᵀ = transvection j i c := by
  rw [transvection, transpose_add, transpose_one, transpose_single, transvection]

theorem pairedSLHom_slTransvection_coe {i j : Fin m} (hij : i ≠ j) (c : k) :
    ((pairedSLHom σ m (slTransvection hij c) : GL (Fin m ⊕ Fin m) k) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k) =
      fromBlocks (transvection i j c) 0 0 (transvection j i (-σ c)) := by
  rw [pairedSLHom_coe, map_slTransvection, inv_slTransvection, coe_slTransvection,
    coe_slTransvection, transpose_transvection]

theorem block_eqs_of_mem_centralizer {A : GL (Fin m ⊕ Fin m) k}
    (hA : A ∈ Subgroup.centralizer ((pairedSLHom σ m).range : Set (GL (Fin m ⊕ Fin m) k)))
    {i j : Fin m} (hij : i ≠ j) (c : k) :
    transvection i j c * A.val.toBlocks₁₁ =
        A.val.toBlocks₁₁ * transvection i j c ∧
      transvection i j c * A.val.toBlocks₁₂ =
        A.val.toBlocks₁₂ * transvection j i (-σ c) ∧
      transvection j i (-σ c) * A.val.toBlocks₂₁ =
        A.val.toBlocks₂₁ * transvection i j c ∧
      transvection j i (-σ c) * A.val.toBlocks₂₂ =
        A.val.toBlocks₂₂ * transvection j i (-σ c) := by
  have h := Subgroup.mem_centralizer_iff.mp hA _ ⟨slTransvection hij c, rfl⟩
  have h' := congrArg (fun B : GL (Fin m ⊕ Fin m) k => B.val) h
  simp only [Units.val_mul, pairedSLHom_slTransvection_coe] at h'
  exact (commute_fromBlocks_diag_iff _ _ _).mp h'

theorem exists_eq_smul_one_of_commute_transvection {P : Matrix (Fin m) (Fin m) k}
    (hP : ∀ i j : Fin m, i ≠ j → transvection i j 1 * P = P * transvection i j 1) :
    ∃ a : k, P = a • (1 : Matrix (Fin m) (Fin m) k) := by
  obtain ⟨a, ha⟩ := mem_range_scalar_of_commute_single (M := P) fun i j hij => by
    have := hP i j hij
    simp only [transvection, add_mul, mul_add, one_mul, mul_one, add_right_inj] at this
    exact this
  exact ⟨a, by rw [← ha, smul_one_eq_diagonal, scalar_apply]⟩

theorem diag_blocks_scalar_of_mem_centralizer {A : GL (Fin m ⊕ Fin m) k}
    (hA : A ∈ Subgroup.centralizer ((pairedSLHom σ m).range : Set (GL (Fin m ⊕ Fin m) k))) :
    (∃ a : k, A.val.toBlocks₁₁ = a • 1) ∧
      ∃ b : k, A.val.toBlocks₂₂ = b • 1 := by
  refine ⟨exists_eq_smul_one_of_commute_transvection fun i j hij =>
      (block_eqs_of_mem_centralizer hA hij 1).1,
    exists_eq_smul_one_of_commute_transvection fun i j hij => ?_⟩
  have h := (block_eqs_of_mem_centralizer hA hij.symm 1).2.2.2
  have e : single i j (-σ 1) = -single i j (1 : k) := by
    rw [map_one, Matrix.single_neg]
  simp only [transvection, add_mul, mul_add, one_mul, mul_one, add_right_inj, e, neg_mul,
    mul_neg, neg_inj] at h ⊢
  exact h

theorem fromBlocks_smul_one_commute (a b : k) (X Y : Matrix (Fin m) (Fin m) k) :
    fromBlocks X 0 0 Y * fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) =
      fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) * fromBlocks X 0 0 Y := by
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem ne_zero_of_fromBlocks_smul_one {A : GL (Fin m ⊕ Fin m) k} (hm : 0 < m) {a b : k}
    (hA : A.val = fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1)) :
    a ≠ 0 ∧ b ≠ 0 := by
  have hdet : A.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  rw [hA, det_fromBlocks_zero₂₁, det_smul, det_smul, det_one, Fintype.card_fin, mul_one,
    mul_one] at hdet
  exact ⟨fun ha => hdet (by rw [ha, zero_pow hm.ne', zero_mul]),
    fun hb => hdet (by rw [hb, zero_pow hm.ne', mul_zero])⟩

end Paired

section Linear

variable (k) (m : ℕ)

theorem pairedSLHom_id_coe (g : SpecialLinearGroup (Fin m) k) :
    ((pairedSLHom (RingHom.id k) m g : GL (Fin m ⊕ Fin m) k) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k) =
      fromBlocks (g : Matrix (Fin m) (Fin m) k) 0 0
        (((g⁻¹ : SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ) := by
  rw [pairedSLHom_coe]
  congr

variable {k m}

theorem offdiag_blocks_zero_of_mem_centralizer_id (hm : 3 ≤ m) {A : GL (Fin m ⊕ Fin m) k}
    (hA : A ∈ Subgroup.centralizer
      ((pairedSLHom (RingHom.id k) m).range : Set (GL (Fin m ⊕ Fin m) k))) :
    A.val.toBlocks₁₂ = 0 ∧ A.val.toBlocks₂₁ = 0 := by
  have hthird : ∀ x y : Fin m, ∃ z : Fin m, z ≠ x ∧ z ≠ y := by
    intro x y
    by_contra! h
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {x, y} := fun z _ => by
      rcases eq_or_ne z x with hz | hz
      · simp [hz]
      · simp [h z hz]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have := Finset.card_le_two (a := x) (b := y)
    omega
  constructor
  · ext j l
    obtain ⟨i, hij, hil⟩ := hthird j l
    have h := congrFun₂ (block_eqs_of_mem_centralizer hA hij 1).2.1 i l
    rw [transvection_mul_apply_same, mul_transvection_apply_of_ne _ _ _ _ hil.symm] at h
    simpa using h
  · ext a i
    obtain ⟨j, hja, hji⟩ := hthird a i
    have h := congrFun₂ (block_eqs_of_mem_centralizer hA hji.symm 1).2.2.1 a j
    rw [transvection_mul_apply_of_ne _ _ _ _ hja.symm, mul_transvection_apply_same] at h
    simpa using h

theorem paired_special_linear_geq_three_linear_centralizer (hm : 3 ≤ m) :
    (Subgroup.centralizer ((pairedSLHom (RingHom.id k) m).range : Set (GL (Fin m ⊕ Fin m) k)) :
        Set (GL (Fin m ⊕ Fin m) k)) =
      {A : GL (Fin m ⊕ Fin m) k | ∃ a b : kˣ, A.val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((b : k) • 1)} ∧
    IsMulCommutative (Subgroup.centralizer
      ((pairedSLHom (RingHom.id k) m).range : Set (GL (Fin m ⊕ Fin m) k))) := by
  have hform : ∀ A ∈ Subgroup.centralizer
      ((pairedSLHom (RingHom.id k) m).range : Set (GL (Fin m ⊕ Fin m) k)),
      ∃ a b : kˣ, (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k) =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((b : k) • 1) := by
    intro A hA
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := diag_blocks_scalar_of_mem_centralizer hA
    obtain ⟨h12, h21⟩ := offdiag_blocks_zero_of_mem_centralizer_id hm hA
    have hAe : A.val = fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) := by
      rw [← fromBlocks_toBlocks A.val, ha, hb, h12, h21]
    obtain ⟨ha0, hb0⟩ := ne_zero_of_fromBlocks_smul_one (by omega) hAe
    exact ⟨Units.mk0 a ha0, Units.mk0 b hb0, hAe⟩
  have hmem : ∀ A : GL (Fin m ⊕ Fin m) k, (∃ a b : kˣ,
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k) =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((b : k) • 1)) →
      A ∈ Subgroup.centralizer
        ((pairedSLHom (RingHom.id k) m).range : Set (GL (Fin m ⊕ Fin m) k)) := by
    rintro A ⟨a, b, hAe⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hAe, pairedSLHom_coe]
    exact fromBlocks_smul_one_commute _ _ _ _
  refine ⟨Set.ext fun A => ⟨hform A, hmem A⟩, ⟨⟨fun x y => ?_⟩⟩⟩
  obtain ⟨a, b, hx⟩ := hform x x.2
  obtain ⟨a', b', hy⟩ := hform y y.2
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, hx, hy, fromBlocks_multiply]
  simp [smul_smul, mul_comm]

end Linear

section Unitary

variable (σ : k →+* k) (m : ℕ)

@[expose] def pairedHermForm (u v : Fin m ⊕ Fin m → k) : k :=
  (fun x => σ (u x)) ⬝ᵥ (fromBlocks (0 : Matrix (Fin m) (Fin m) k) 1 1 0 *ᵥ v)

theorem pairedHermForm_eq (u v : Fin m ⊕ Fin m → k) :
    pairedHermForm σ m u v =
      ∑ i, (σ (u (Sum.inl i)) * v (Sum.inr i) + σ (u (Sum.inr i)) * v (Sum.inl i)) := by
  simp [pairedHermForm, dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec,
    Finset.sum_add_distrib]

@[expose] def pairedUnitaryGroup : Subgroup (GL (Fin m ⊕ Fin m) k) where
  carrier := {A | ∀ u v, pairedHermForm σ m (A.val *ᵥ u) (A.val *ᵥ v) = pairedHermForm σ m u v}
  one_mem' u v := by simp
  mul_mem' {A B} hA hB u v := by
    change pairedHermForm σ m ((A * B).val *ᵥ u) ((A * B).val *ᵥ v) = _
    rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hA, hB]
  inv_mem' {A} hA u v := by
    have h := hA ((A⁻¹).val *ᵥ u) ((A⁻¹).val *ᵥ v)
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, one_mulVec] at h
    exact h.symm

theorem mem_pairedUnitaryGroup {A : GL (Fin m ⊕ Fin m) k} :
    A ∈ pairedUnitaryGroup σ m ↔
      ∀ u v, pairedHermForm σ m (A.val *ᵥ u) (A.val *ᵥ v) = pairedHermForm σ m u v :=
  Iff.rfl

variable {σ m}

theorem conj_mulVec_dotProduct (M : Matrix (Fin m) (Fin m) k) (a b : Fin m → k) :
    (fun i => σ ((M *ᵥ a) i)) ⬝ᵥ b = (fun i => σ (a i)) ⬝ᵥ ((M.map σ)ᵀ *ᵥ b) := by
  have h : (fun i => σ ((M *ᵥ a) i)) = M.map σ *ᵥ (fun i => σ (a i)) :=
    funext fun i => RingHom.map_mulVec σ M a i
  rw [h, dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem pairedHermForm_fromBlocks {X Y : Matrix (Fin m) (Fin m) k} (hXY : (X.map σ)ᵀ * Y = 1)
    (hYX : (Y.map σ)ᵀ * X = 1) (u v : Fin m ⊕ Fin m → k) :
    pairedHermForm σ m (fromBlocks X 0 0 Y *ᵥ u) (fromBlocks X 0 0 Y *ᵥ v) =
      pairedHermForm σ m u v := by
  have key : ∀ (M N : Matrix (Fin m) (Fin m) k), (M.map σ)ᵀ * N = 1 → ∀ a b : Fin m → k,
      ∑ i, σ ((M *ᵥ a) i) * (N *ᵥ b) i = ∑ i, σ (a i) * b i := by
    intro M N hMN a b
    have := conj_mulVec_dotProduct (σ := σ) M a (N *ᵥ b)
    rw [mulVec_mulVec, hMN, one_mulVec] at this
    exact this
  rw [pairedHermForm_eq, pairedHermForm_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_inl, Sum.elim_inr]
  rw [key X Y hXY, key Y X hYX]
  rfl

theorem map_map_of_involutive (hσ : ∀ c, σ (σ c) = c) (g : SpecialLinearGroup (Fin m) k) :
    SpecialLinearGroup.map σ (SpecialLinearGroup.map σ g) = g := by
  refine Subtype.ext ?_
  change ((g : Matrix (Fin m) (Fin m) k).map σ).map σ = g
  ext a b
  simp [hσ]

theorem pairedSLHom_range_le_pairedUnitaryGroup (hσ : ∀ c, σ (σ c) = c) :
    (pairedSLHom σ m).range ≤ pairedUnitaryGroup σ m := by
  rintro _ ⟨g, rfl⟩ u v
  rw [pairedSLHom_coe]
  refine pairedHermForm_fromBlocks ?_ ?_ u v
  · change ((SpecialLinearGroup.map σ g : SpecialLinearGroup (Fin m) k) :
      Matrix (Fin m) (Fin m) k)ᵀ * _ = 1
    rw [← transpose_mul, coe_inv_mul_coe_SL, transpose_one]
  · rw [transpose_map, transpose_transpose]
    change (((SpecialLinearGroup.map σ ((SpecialLinearGroup.map σ g)⁻¹)) :
      SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) * _ = 1
    rw [map_inv, map_map_of_involutive hσ, coe_inv_mul_coe_SL]

theorem pairedHermForm_smul_one (a b : k) (u v : Fin m ⊕ Fin m → k) :
    pairedHermForm σ m (fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) *ᵥ u)
      (fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) *ᵥ v) =
      ∑ i, (σ a * b * (σ (u (Sum.inl i)) * v (Sum.inr i)) +
        σ b * a * (σ (u (Sum.inr i)) * v (Sum.inl i))) := by
  rw [pairedHermForm_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_inl, Sum.elim_inr,
    smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_mul]
  ring

theorem offdiag_blocks_zero_of_mem_centralizer_conj (hm : 2 ≤ m) {c₀ : k} (hc₀ : σ c₀ ≠ c₀)
    {A : GL (Fin m ⊕ Fin m) k}
    (hA : A ∈ Subgroup.centralizer ((pairedSLHom σ m).range : Set (GL (Fin m ⊕ Fin m) k))) :
    A.val.toBlocks₁₂ = 0 ∧ A.val.toBlocks₂₁ = 0 := by
  have hother : ∀ x : Fin m, ∃ y : Fin m, y ≠ x := by
    intro x
    by_contra! h
    have : Fintype.card (Fin m) ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (h a).trans (h b).symm
    rw [Fintype.card_fin] at this
    omega
  have hsub : c₀ - σ c₀ ≠ 0 := sub_ne_zero.mpr hc₀.symm
  constructor
  · ext j l
    obtain ⟨i, hij⟩ := hother j
    rcases eq_or_ne l i with rfl | hli
    · have h1 := congrFun₂ (block_eqs_of_mem_centralizer hA hij 1).2.1 l l
      have h2 := congrFun₂ (block_eqs_of_mem_centralizer hA hij c₀).2.1 l l
      rw [transvection_mul_apply_same, mul_transvection_apply_same] at h1 h2
      rw [map_one] at h1
      have : (c₀ - σ c₀) * A.val.toBlocks₁₂ j l = 0 := by linear_combination h2 - σ c₀ * h1
      simpa [hsub] using this
    · have h := congrFun₂ (block_eqs_of_mem_centralizer hA hij 1).2.1 i l
      rw [transvection_mul_apply_same, mul_transvection_apply_of_ne _ _ _ _ hli] at h
      simpa using h
  · ext a i
    obtain ⟨j, hji⟩ := hother i
    rcases eq_or_ne a j with rfl | haj
    · have h1 := congrFun₂ (block_eqs_of_mem_centralizer hA hji.symm 1).2.2.1 a a
      have h2 := congrFun₂ (block_eqs_of_mem_centralizer hA hji.symm c₀).2.2.1 a a
      rw [transvection_mul_apply_same, mul_transvection_apply_same] at h1 h2
      rw [map_one] at h1
      have : (c₀ - σ c₀) * A.val.toBlocks₂₁ a i = 0 := by linear_combination -h2 + σ c₀ * h1
      simpa [hsub] using this
    · have h := congrFun₂ (block_eqs_of_mem_centralizer hA hji.symm 1).2.2.1 a j
      rw [transvection_mul_apply_of_ne _ _ _ _ haj, mul_transvection_apply_same] at h
      simpa using h

theorem pairedUnitary_centralizer (hσ : ∀ c, σ (σ c) = c) (hσ1 : ∃ c, σ c ≠ c) (hm : 2 ≤ m) :
    (Subgroup.centralizer (((pairedSLHom σ m).range.subgroupOf (pairedUnitaryGroup σ m)) :
        Set (pairedUnitaryGroup σ m)) : Set (pairedUnitaryGroup σ m)) =
      {x : pairedUnitaryGroup σ m | ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((σ (a : k))⁻¹ • 1)} ∧
    IsMulCommutative (Subgroup.centralizer
      (((pairedSLHom σ m).range.subgroupOf (pairedUnitaryGroup σ m)) :
        Set (pairedUnitaryGroup σ m))) := by
  obtain ⟨c₀, hc₀⟩ := hσ1
  have hle := pairedSLHom_range_le_pairedUnitaryGroup (m := m) hσ
  have hGL : ∀ x ∈ Subgroup.centralizer (((pairedSLHom σ m).range.subgroupOf
      (pairedUnitaryGroup σ m)) : Set (pairedUnitaryGroup σ m)),
      (x : GL (Fin m ⊕ Fin m) k) ∈
        Subgroup.centralizer ((pairedSLHom σ m).range : Set (GL (Fin m ⊕ Fin m) k)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro d hd
    have := hx ⟨d, hle hd⟩ (Subgroup.mem_subgroupOf.mpr hd)
    exact congrArg Subtype.val this
  have hform : ∀ x ∈ Subgroup.centralizer (((pairedSLHom σ m).range.subgroupOf
      (pairedUnitaryGroup σ m)) : Set (pairedUnitaryGroup σ m)),
      ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((σ (a : k))⁻¹ • 1) := by
    intro x hx
    have hA := hGL x hx
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := diag_blocks_scalar_of_mem_centralizer hA
    obtain ⟨h12, h21⟩ := offdiag_blocks_zero_of_mem_centralizer_conj hm hc₀ hA
    have hAe : (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) := by
      rw [← fromBlocks_toBlocks (x : GL (Fin m ⊕ Fin m) k).val, ha, hb, h12, h21]
    obtain ⟨ha0, -⟩ := ne_zero_of_fromBlocks_smul_one (by omega) hAe
    have i₀ : Fin m := ⟨0, by omega⟩
    have hunit := (mem_pairedUnitaryGroup σ m).mp x.2 (Pi.single (Sum.inl i₀) 1)
      (Pi.single (Sum.inr i₀) 1)
    rw [hAe, pairedHermForm_smul_one, pairedHermForm_eq] at hunit
    simp only [Pi.single_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte,
      mul_zero, add_zero, map_one, map_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ] at hunit
    have hb' : b = (σ a)⁻¹ := eq_inv_of_mul_eq_one_right hunit
    exact ⟨Units.mk0 a ha0, by rw [hAe, hb', Units.val_mk0]⟩
  have hmem : ∀ x : pairedUnitaryGroup σ m, (∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
      fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((σ (a : k))⁻¹ • 1)) →
      x ∈ Subgroup.centralizer (((pairedSLHom σ m).range.subgroupOf
        (pairedUnitaryGroup σ m)) : Set (pairedUnitaryGroup σ m)) := by
    rintro x ⟨a, hx⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro d hd
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hd
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hx, ← hg, pairedSLHom_coe]
    exact fromBlocks_smul_one_commute _ _ _ _
  refine ⟨Set.ext fun x => ⟨hform x, hmem x⟩, ⟨⟨fun x y => ?_⟩⟩⟩
  obtain ⟨a, hx⟩ := hform x x.2
  obtain ⟨a', hy⟩ := hform y y.2
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  simp only [Subgroup.coe_mul, Units.val_mul, hx, hy, fromBlocks_multiply]
  simp [smul_smul, mul_comm]

theorem paired_unitary_special_linear_centralizer_abelian {p f : ℕ}
    (h : UnitaryFieldData p f k) (hm : 2 ≤ m) :
    (pairedSLHom h.bar m).range ≤ pairedUnitaryGroup h.bar m ∧
    (Subgroup.centralizer (((pairedSLHom h.bar m).range.subgroupOf
        (pairedUnitaryGroup h.bar m)) : Set (pairedUnitaryGroup h.bar m)) :
        Set (pairedUnitaryGroup h.bar m)) =
      {x : pairedUnitaryGroup h.bar m | ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((h.bar (a : k))⁻¹ • 1)} ∧
    IsMulCommutative (Subgroup.centralizer
      (((pairedSLHom h.bar m).range.subgroupOf (pairedUnitaryGroup h.bar m)) :
        Set (pairedUnitaryGroup h.bar m))) :=
  ⟨pairedSLHom_range_le_pairedUnitaryGroup h.bar_bar,
    pairedUnitary_centralizer h.bar_bar h.exists_bar_ne hm⟩

end Unitary

end CFSG.LocalAnalysis.ComponentInitial

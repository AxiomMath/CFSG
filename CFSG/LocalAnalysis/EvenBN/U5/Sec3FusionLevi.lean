module

public import CFSG.RankThree.PartOne.U5K.Hyp.Aut

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K]

@[expose] def LeviOrbitsV (h : UnitaryFieldData 2 f K) : Prop :=
  2 ≤ f → center (hypPSU h 2 1) = ⊥ →
    ∀ X : Set (hypSU h 2 1), X ⊆ (Vsub h : Set (hypSU h 2 1)) \ {1} →
      (∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ v ∈ X,
        lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ ∈ X) →
      Nat.card X = 0 ∨ Nat.card X = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) ∨
        Nat.card X = (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) ∨ Nat.card X = (2 ^ f) ^ 4 - 1

section Herm

variable (h : UnitaryFieldData 2 f K)

theorem exists_mul_bar_eq {a : K} (ha : h.bar a = a) : ∃ c : K, c * h.bar c = a := by
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨a, h.mem_fixedField.2 ha⟩
  exact ⟨c, by simpa [UnitaryFieldData.norm] using congrArg Subtype.val hc⟩

theorem exists_vecMulVec_of_det_eq_zero {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hY0 : Y ≠ 0) (hdet : Y.det = 0) :
    ∃ w : Fin 2 → K, w ≠ 0 ∧ Y = vecMulVec w fun j => h.bar (w j) := by
  have := h.charP
  obtain ⟨h00, h11, h10⟩ := isHerm_iff.1 hY
  rw [Matrix.det_fin_two, h10] at hdet
  by_cases ha : Y 0 0 = 0
  ·
    have hb : Y 0 1 = 0 := by
      have h1 : Y 0 1 * h.bar (Y 0 1) = 0 := by
        rw [ha, zero_mul, zero_sub, neg_eq_zero] at hdet
        exact hdet
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact (map_eq_zero h.bar).1 h2
    obtain ⟨c, hc⟩ := exists_mul_bar_eq h h11
    refine ⟨![0, c], fun h0 => ?_, ?_⟩
    · apply hY0
      have hc0 : c = 0 := by simpa using congrFun h0 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, h10, ← hc, hc0]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec, ha, hb, h10, hc]
  · obtain ⟨α, hα⟩ := exists_mul_bar_eq h h00
    have hα0 : α ≠ 0 := by rintro rfl; rw [zero_mul] at hα; exact ha hα.symm
    have hαb : h.bar α ≠ 0 := (map_ne_zero h.bar).2 hα0
    refine ⟨![α, h.bar (Y 0 1) / h.bar α], fun h0 => hα0 (by simpa using congrFun h0 0), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [vecMulVec, hα]
    · simp [vecMulVec, map_div₀, h.bar_bar]
      field_simp
    · simp [vecMulVec, h10]
      field_simp
    · simp [vecMulVec, map_div₀, h.bar_bar]
      have e : Y 1 1 = Y 0 1 * h.bar (Y 0 1) / Y 0 0 := by
        field_simp
        linear_combination hdet
      rw [e, ← hα]
      field_simp

theorem bar_det_of_isHerm {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y) :
    h.bar Y.det = Y.det := by
  obtain ⟨h00, h11, h10⟩ := isHerm_iff.1 hY
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h10, h.bar_bar]
  ring

theorem exists_mul_conjTranspose_of_det_ne_zero {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hdet : Y.det ≠ 0) : ∃ B : Matrix (Fin 2) (Fin 2) K, IsUnit B.det ∧
      Y = B * (B.map h.bar)ᵀ := by
  have := h.charP
  have h2 : ∀ a : K, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  have hD := bar_det_of_isHerm h hY
  obtain ⟨h00, h11, h10⟩ := isHerm_iff.1 hY
  have hdetY : Y.det = Y 0 0 * Y 1 1 + Y 0 1 * h.bar (Y 0 1) := by
    rw [Matrix.det_fin_two, h10, CharTwo.sub_eq_add]
  by_cases ha : Y 0 0 = 0
  · by_cases hd : Y 1 1 = 0
    ·
      have hb : Y 0 1 ≠ 0 := by
        intro hb
        rw [hdetY, ha, hd, hb] at hdet
        simp at hdet
      obtain ⟨r, hr⟩ := h.exists_bar_ne
      have hr0 : r ≠ 0 := by rintro rfl; exact hr (map_zero _)
      have hrb : h.bar r ≠ 0 := (map_ne_zero h.bar).2 hr0
      obtain ⟨μ, hμ⟩ : ∃ μ, μ = r / h.bar r := ⟨_, rfl⟩
      have hμ1 : μ + 1 ≠ 0 := by
        intro h1
        apply hr
        have : μ = 1 := by linear_combination h1 - h2 1
        rw [hμ, div_eq_one_iff_eq hrb] at this
        exact this.symm
      have hNμ : μ * h.bar μ = 1 := by
        rw [hμ, map_div₀, h.bar_bar]
        field_simp
      obtain ⟨w, hw⟩ : ∃ w, w = h.bar (Y 0 1) / (μ + 1) := ⟨_, rfl⟩
      have hw0 : w ≠ 0 := by
        rw [hw]
        exact div_ne_zero ((map_ne_zero h.bar).2 hb) hμ1
      have e1 : w * (μ + 1) = h.bar (Y 0 1) := by
        rw [hw]
        field_simp
      have e2 : h.bar w * (h.bar μ + 1) = Y 0 1 := by
        have := congrArg h.bar e1
        rwa [map_mul, map_add, map_one, h.bar_bar] at this
      refine ⟨!![1, 1; μ * w, w], ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        refine isUnit_iff_ne_zero.2 fun h0 => ?_
        have : w * (μ + 1) = 0 := by linear_combination h0 + h2 (μ * w)
        rcases mul_eq_zero.1 this with h3 | h3
        · exact hw0 h3
        · exact hμ1 h3
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd, h10, h2]
        · linear_combination -e2
        · linear_combination -e1
        · linear_combination (-(w * h.bar w)) * hNμ - h2 (w * h.bar w)
    ·
      obtain ⟨δ, hδ⟩ := exists_mul_bar_eq h h11
      have hδ0 : δ ≠ 0 := by rintro rfl; rw [zero_mul] at hδ; exact hd hδ.symm
      have hδb : h.bar δ ≠ 0 := (map_ne_zero h.bar).2 hδ0
      have hbarD : h.bar (Y.det / Y 1 1) = Y.det / Y 1 1 := by rw [map_div₀, hD, h11]
      obtain ⟨β, hβ⟩ := exists_mul_bar_eq h hbarD
      have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hβ
        exact div_ne_zero hdet hd hβ.symm
      have hdetY0 : Y.det = Y 0 1 * h.bar (Y 0 1) := by rw [hdetY, ha, zero_mul, zero_add]
      refine ⟨!![β, Y 0 1 / h.bar δ; 0, δ], ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        exact isUnit_iff_ne_zero.2 (by simpa using mul_ne_zero hβ0 hδ0)
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, ha, h10, map_div₀, h.bar_bar]
        · rw [hβ, hdetY0, ← hδ, div_mul_div_comm, mul_comm (h.bar δ) δ]
          exact (h2 _).symm
        · exact (div_mul_cancel₀ _ hδb).symm
        · exact (mul_div_cancel₀ _ hδ0).symm
        · exact hδ.symm
  ·
    obtain ⟨α, hα⟩ := exists_mul_bar_eq h h00
    have hα0 : α ≠ 0 := by rintro rfl; rw [zero_mul] at hα; exact ha hα.symm
    have hαb : h.bar α ≠ 0 := (map_ne_zero h.bar).2 hα0
    have hbarD : h.bar (Y.det / Y 0 0) = Y.det / Y 0 0 := by rw [map_div₀, hD, h00]
    obtain ⟨β, hβ⟩ := exists_mul_bar_eq h hbarD
    have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hβ
      exact div_ne_zero hdet ha hβ.symm
    refine ⟨!![α, 0; h.bar (Y 0 1) / h.bar α, β], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      exact isUnit_iff_ne_zero.2 (by simpa using mul_ne_zero hα0 hβ0)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, h10, map_div₀, h.bar_bar]
      · exact hα.symm
      · exact (mul_div_cancel₀ _ hα0).symm
      · exact (div_mul_cancel₀ _ hαb).symm
      · have hA : α * h.bar α ≠ 0 := mul_ne_zero hα0 hαb
        rw [hβ, hdetY, ← hα, div_mul_div_comm, mul_comm (h.bar α) α, ← add_div,
          eq_div_iff hA]
        linear_combination -h2 (h.bar (Y 0 1) * Y 0 1)

theorem exists_conj_eq_of_det_eq_zero {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hY0 : Y ≠ 0) (hdet : Y.det = 0) (hY' : IsHerm h Y') (hY'0 : Y' ≠ 0) (hdet' : Y'.det = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, IsUnit A.det ∧ A * Y * (A.map h.bar)ᵀ = Y' := by
  obtain ⟨w, hw0, rfl⟩ := exists_vecMulVec_of_det_eq_zero h hY hY0 hdet
  obtain ⟨w', hw'0, rfl⟩ := exists_vecMulVec_of_det_eq_zero h hY' hY'0 hdet'
  obtain ⟨A, hA, hAw⟩ := exists_sl2_smul hw0 hw'0
  refine ⟨A, by rw [hA]; exact isUnit_one, ?_⟩
  rw [mul_vecMulVec, vecMulVec_mul, hAw]
  congr 1
  funext j
  rw [← hAw]
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct]
  ring

theorem exists_conj_eq_of_det_ne_zero {Y Y' : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm h Y)
    (hdet : Y.det ≠ 0) (hY' : IsHerm h Y') (hdet' : Y'.det ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, IsUnit A.det ∧ A * Y * (A.map h.bar)ᵀ = Y' := by
  obtain ⟨B, hB, rfl⟩ := exists_mul_conjTranspose_of_det_ne_zero h hY hdet
  obtain ⟨B', hB', rfl⟩ := exists_mul_conjTranspose_of_det_ne_zero h hY' hdet'
  refine ⟨B' * B⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact hB'.mul (Matrix.isUnit_nonsing_inv_det B hB)
  · have h1 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
    have h2 : (B.map h.bar)ᵀ * ((B⁻¹).map h.bar)ᵀ = 1 := by
      rw [← conjTranspose_mul', h1, Matrix.map_one _ (map_zero _) (map_one _), transpose_one]
    calc B' * B⁻¹ * (B * (B.map h.bar)ᵀ) * ((B' * B⁻¹).map h.bar)ᵀ
        = B' * (B⁻¹ * B) * ((B.map h.bar)ᵀ * ((B⁻¹).map h.bar)ᵀ) * (B'.map h.bar)ᵀ := by
          rw [conjTranspose_mul']
          simp only [Matrix.mul_assoc]
      _ = B' * (B'.map h.bar)ᵀ := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]

section Count

variable [DecidableEq K]

theorem sum_count_d [Fintype h.fixedField] (a : h.fixedField) {c : K} (hc : h.bar c = c) :
    (∑ d : h.fixedField, if (a : K) * d = c then 1 else 0) =
      if (a : K) = 0 then (if c = 0 then Fintype.card h.fixedField else 0) else 1 := by
  by_cases ha : (a : K) = 0
  · simp only [ha, zero_mul]
    by_cases hc0 : c = 0
    · simp [hc0]
    · simp [hc0, Ne.symm hc0]
  · have hmem : c / a ∈ h.fixedField := by
      rw [h.mem_fixedField, map_div₀, hc, h.mem_fixedField.1 a.2]
    have key : ∀ d : h.fixedField, (a : K) * d = c ↔ d = ⟨c / a, hmem⟩ := by
      intro d
      constructor
      · intro hd
        apply Subtype.ext
        change (d : K) = c / a
        rw [eq_div_iff ha, mul_comm]
        exact hd
      · rintro rfl
        change (a : K) * (c / a) = c
        rw [mul_div_cancel₀ _ ha]
    simp only [key, ha]
    simp

theorem sum_count_a [Fintype h.fixedField] {c : K} (hc : h.bar c = c) :
    (∑ a : h.fixedField, ∑ d : h.fixedField, if (a : K) * d = c then 1 else 0) =
      (if c = 0 then Fintype.card h.fixedField else 0) + (Fintype.card h.fixedField - 1) := by
  simp only [sum_count_d h _ hc]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : h.fixedField))]
  simp only [ZeroMemClass.coe_zero, ite_true]
  congr 1
  have h1 : ∀ a ∈ (Finset.univ : Finset h.fixedField).erase 0,
      (if (a : K) = 0 then (if c = 0 then Fintype.card h.fixedField else 0) else 1) = 1 := by
    intro a ha
    have h0 : (a : K) ≠ 0 := by
      intro h0
      exact (Finset.mem_erase.1 ha).1 (Subtype.ext h0)
    simp [h0]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

theorem sum_count_triples [Fintype h.fixedField] [Fintype K] :
    (∑ b : K, ∑ a : h.fixedField, ∑ d : h.fixedField,
        if (a : K) * d = b * h.bar b then 1 else 0) =
      Fintype.card h.fixedField + Fintype.card K * (Fintype.card h.fixedField - 1) := by
  have hfix : ∀ b : K, h.bar (b * h.bar b) = b * h.bar b := fun b => by
    rw [map_mul, h.bar_bar, mul_comm]
  simp only [sum_count_a h (hfix _)]
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  congr 1
  have h0 : ∀ b : K, b * h.bar b = 0 ↔ b = 0 := fun b => by
    rw [mul_eq_zero, map_eq_zero h.bar, or_self]
  simp only [h0]
  simp

end Count

theorem card_singular_herm :
    Nat.card {Y : Matrix (Fin 2) (Fin 2) K // IsHerm h Y ∧ Y.det = 0} =
      2 ^ f + (2 ^ f) ^ 2 * (2 ^ f - 1) := by
  classical
  have := h.finite
  have := Fintype.ofFinite K
  have := h.charP
  have e : {Y : Matrix (Fin 2) (Fin 2) K // IsHerm h Y ∧ Y.det = 0} ≃
      {p : K × h.fixedField × h.fixedField // (p.2.1 : K) * p.2.2 = p.1 * h.bar p.1} :=
    { toFun := fun Y => ⟨(Y.1 0 1, ⟨Y.1 0 0, (isHerm_iff.1 Y.2.1).1⟩,
        ⟨Y.1 1 1, (isHerm_iff.1 Y.2.1).2.1⟩), by
          have h1 := Y.2.2
          rw [Matrix.det_fin_two, (isHerm_iff.1 Y.2.1).2.2, sub_eq_zero] at h1
          exact h1⟩
      invFun := fun p => ⟨hermM h p.1.2.1 p.1.2.2 p.1.1,
        hermM_isHerm (h.mem_fixedField.1 p.1.2.1.2) (h.mem_fixedField.1 p.1.2.2.2), by
          rw [Matrix.det_fin_two]
          simp only [hermM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
          rw [p.2, sub_self]⟩
      left_inv := fun Y => Subtype.ext (eq_hermM Y.2.1).symm
      right_inv := fun p => by
        apply Subtype.ext
        simp [hermM] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  simp only [Fintype.sum_prod_type]
  rw [sum_count_triples h, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    h.card_fixedField, h.card_eq_sq]

end Herm

section Orbits

variable (h : UnitaryFieldData 2 f K)

theorem lev_conj_Yof (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) {v : hypSU h 2 1}
    (hv : v ∈ Vsub h) :
    lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹ ∈ Vsub h ∧
      Yof (lev (hK := h) A hA * v * (lev (hK := h) A hA)⁻¹) = A * Yof v * (A.map h.bar)ᵀ := by
  obtain ⟨-, Y, hY⟩ := hv
  have h1 := lev_conj (hK := h) A hA hY
  simp only [mulVec_zero, smul_zero] at h1
  rw [Yof_eq hY]
  exact ⟨mem_Vsub_of_mat h1, Yof_eq h1⟩

theorem eq_one_iff_Yof_eq_zero {v : hypSU h 2 1} (hv : v ∈ Vsub h) : v = 1 ↔ Yof v = 0 := by
  constructor
  · rintro rfl
    exact Yof_eq (by rw [mat_one, oddUni_zero])
  · intro h0
    obtain ⟨-, Y, hY⟩ := hv
    rw [Yof_eq hY] at h0
    apply mat_injective
    rw [hY, h0, oddUni_zero, mat_one]

theorem Yof_injOn : Set.InjOn (Yof (hK := h)) (Vsub h : Set (hypSU h 2 1)) := by
  intro v hv w hw hvw
  exact Yof_ext hv hw (by rw [hvw]) (by rw [hvw]) (by rw [hvw])

theorem leviOrbitsV : LeviOrbitsV h := by
  intro _ _ X hXsub hXinv
  classical
  have := CFSG.RankThree.PartOne.U5K.Hyp.finite_hypSU h
  have := h.finite
  have hfinS : ∀ S : Set (hypSU h 2 1), S.Finite := fun S => S.toFinite
  set R₁ : Set (hypSU h 2 1) := {v | v ∈ Vsub h ∧ Yof v ≠ 0 ∧ (Yof v).det = 0} with hR₁
  set R₂ : Set (hypSU h 2 1) := {v | v ∈ Vsub h ∧ (Yof v).det ≠ 0} with hR₂
  have hunion : (Vsub h : Set (hypSU h 2 1)) \ {1} = R₁ ∪ R₂ := by
    ext v
    constructor
    · rintro ⟨hv, hv1⟩
      have hY0 : Yof v ≠ 0 := fun h0 => hv1 ((eq_one_iff_Yof_eq_zero h hv).2 h0)
      by_cases hd : (Yof v).det = 0
      · exact Or.inl ⟨hv, hY0, hd⟩
      · exact Or.inr ⟨hv, hd⟩
    · rintro (⟨hv, hY0, -⟩ | ⟨hv, hd⟩)
      · exact ⟨hv, fun h1 => hY0 ((eq_one_iff_Yof_eq_zero h hv).1 h1)⟩
      · refine ⟨hv, fun h1 => hd ?_⟩
        rw [(eq_one_iff_Yof_eq_zero h hv).1 h1, Matrix.det_zero]
  have hdisj : Disjoint R₁ R₂ := by
    rw [Set.disjoint_left]
    rintro v ⟨-, -, hd⟩ ⟨-, hd'⟩
    exact hd' hd
  have hV1 : ((Vsub h : Set (hypSU h 2 1)) \ {1}).ncard = (2 ^ f) ^ 4 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem (Vsub h)), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, card_Vsub]
  have hR₁card : R₁.ncard = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
    have himage : Yof '' R₁ =
        {Y : Matrix (Fin 2) (Fin 2) K | IsHerm h Y ∧ Y.det = 0} \ {0} := by
      ext Y
      constructor
      · rintro ⟨v, ⟨hv, hY0, hd⟩, rfl⟩
        exact ⟨⟨herm_Yof hv, hd⟩, hY0⟩
      · rintro ⟨⟨hY, hd⟩, hY0⟩
        obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub hY
        rw [← Yof_eq hvm] at hY0 hd ⊢
        exact ⟨v, ⟨hv, hY0, hd⟩, rfl⟩
    rw [← (Yof_injOn h).mono (fun v hv => hv.1) |>.ncard_image, himage]
    have h0 : (0 : Matrix (Fin 2) (Fin 2) K) ∈
        {Y : Matrix (Fin 2) (Fin 2) K | IsHerm h Y ∧ Y.det = 0} :=
      ⟨by simp [IsHerm], Matrix.det_zero⟩
    have h1 : ({Y : Matrix (Fin 2) (Fin 2) K | IsHerm h Y ∧ Y.det = 0} \ {0}).ncard + 1 =
        2 ^ f + (2 ^ f) ^ 2 * (2 ^ f - 1) := by
      rw [Set.ncard_sdiff_singleton_add_one h0 (Set.toFinite _), ← Nat.card_coe_set_eq,
        ← card_singular_herm h]
      rfl
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have e : 2 ^ f + (2 ^ f) ^ 2 * (2 ^ f - 1) = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) + 1 := by
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 := ⟨2 ^ f - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
    omega
  have hR₂card : R₂.ncard = (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) := by
    have h1 := Set.ncard_union_eq hdisj (hfinS R₁) (hfinS R₂)
    rw [← hunion, hV1, hR₁card] at h1
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ f = m + 1 := ⟨2 ^ f - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel] at h1 ⊢
    have e : (m + 1) ^ 4 - 1 = m * ((m + 1) ^ 2 + 1) + m * (m + 1) * ((m + 1) ^ 2 + 1) := by
      have : (m + 1) ^ 4 = m * ((m + 1) ^ 2 + 1) + m * (m + 1) * ((m + 1) ^ 2 + 1) + 1 := by
        ring
      omega
    omega
  have hX₁ : X ∩ R₁ = ∅ ∨ X ∩ R₁ = R₁ := by
    by_cases hne : (X ∩ R₁).Nonempty
    · right
      obtain ⟨v₀, hv₀X, hv₀⟩ := hne
      refine Set.Subset.antisymm Set.inter_subset_right fun w hw => ⟨?_, hw⟩
      obtain ⟨A, hA, hAY⟩ := exists_conj_eq_of_det_eq_zero h (herm_Yof hv₀.1) hv₀.2.1 hv₀.2.2
        (herm_Yof hw.1) hw.2.1 hw.2.2
      obtain ⟨hmem, hY⟩ := lev_conj_Yof h A hA hv₀.1
      have : lev (hK := h) A hA * v₀ * (lev (hK := h) A hA)⁻¹ = w :=
        Yof_injOn h hmem hw.1 (by rw [hY, hAY])
      rw [← this]
      exact hXinv A hA v₀ hv₀X
    · left
      exact Set.not_nonempty_iff_eq_empty.1 hne
  have hX₂ : X ∩ R₂ = ∅ ∨ X ∩ R₂ = R₂ := by
    by_cases hne : (X ∩ R₂).Nonempty
    · right
      obtain ⟨v₀, hv₀X, hv₀⟩ := hne
      refine Set.Subset.antisymm Set.inter_subset_right fun w hw => ⟨?_, hw⟩
      obtain ⟨A, hA, hAY⟩ := exists_conj_eq_of_det_ne_zero h (herm_Yof hv₀.1) hv₀.2
        (herm_Yof hw.1) hw.2
      obtain ⟨hmem, hY⟩ := lev_conj_Yof h A hA hv₀.1
      have : lev (hK := h) A hA * v₀ * (lev (hK := h) A hA)⁻¹ = w :=
        Yof_injOn h hmem hw.1 (by rw [hY, hAY])
      rw [← this]
      exact hXinv A hA v₀ hv₀X
    · left
      exact Set.not_nonempty_iff_eq_empty.1 hne
  have hXeq : X = (X ∩ R₁) ∪ (X ∩ R₂) := by
    rw [← Set.inter_union_distrib_left, ← hunion]
    exact (Set.inter_eq_left.2 hXsub).symm
  have hXcard : X.ncard = (X ∩ R₁).ncard + (X ∩ R₂).ncard := by
    conv_lhs => rw [hXeq]
    exact Set.ncard_union_eq (hdisj.mono Set.inter_subset_right Set.inter_subset_right)
      (hfinS _) (hfinS _)
  rw [Nat.card_coe_set_eq, hXcard]
  have hsum : (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) + (2 ^ f - 1) * 2 ^ f * ((2 ^ f) ^ 2 + 1) =
      (2 ^ f) ^ 4 - 1 := by
    rw [← hR₁card, ← hR₂card, ← Set.ncard_union_eq hdisj (hfinS R₁) (hfinS R₂), ← hunion, hV1]
  rcases hX₁ with h1 | h1 <;> rcases hX₂ with h2 | h2 <;> rw [h1, h2] <;>
    simp only [Set.ncard_empty, zero_add, add_zero, hR₁card, hR₂card, hsum, true_or, or_true]

end Orbits

end CFSG.LocalAnalysis.EvenBN.U5

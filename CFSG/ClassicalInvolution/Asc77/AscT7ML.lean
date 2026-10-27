module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Alpha

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPlane
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] def sgn (j i : Fin 4) : F := if i = j then -1 else 1

@[expose] def dMat (j : Fin 4) : Matrix (Fin 4) (Fin 4) F := Matrix.diagonal (sgn j)

theorem dMat_mul_self (j : Fin 4) : (dMat j : Matrix (Fin 4) (Fin 4) F) * dMat j = 1 := by
  rw [dMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  by_cases h : i = j <;> simp [sgn, h]

@[expose] def dGL (j : Fin 4) : GL (Fin 4) F := ⟨dMat j, dMat j, dMat_mul_self j, dMat_mul_self j⟩

theorem coe_dGL (j : Fin 4) : ((dGL j : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = dMat j := rfl

theorem coe_dGL_inv (j : Fin 4) :
    (((dGL j)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = dMat j := rfl

theorem dMat_conj_apply (j : Fin 4) (g : Matrix (Fin 4) (Fin 4) F) (i k : Fin 4) :
    (((dMat j : Matrix (Fin 4) (Fin 4) F) * g * (dMat j : Matrix (Fin 4) (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)) i k = sgn j i * g i k * sgn j k := by
  rw [dMat, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem coe_slConj_dGL (j : Fin 4) (g : SL(4, F)) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F (dGL j) g :
      SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = dMat j * (g : Matrix (Fin 4) (Fin 4) F) * dMat j := by
  rw [coe_slConjugation, coe_dGL, coe_dGL_inv]

theorem sgn_mul_self (j i : Fin 4) : (sgn j i : F) * sgn j i = 1 := by
  by_cases h : i = j <;> simp [sgn, h]

theorem sgn_eq_one_iff {j i : Fin 4} (h2 : (2 : F) ≠ 0) : (sgn j i : F) = 1 ↔ i ≠ j := by
  by_cases h : i = j
  · simp only [sgn, h, ite_true, ne_eq, not_true_eq_false, iff_false]
    intro h1
    apply h2
    linear_combination -h1
  · simp [sgn, h]

@[expose] def Jc (j : Fin 4) : Finset (Fin 4) := Finset.univ.erase j

theorem mem_Jc {j i : Fin 4} : i ∈ Jc j ↔ i ≠ j := by simp [Jc]

theorem Jc_card (j : Fin 4) : (Jc j).card = 3 := by
  rw [Jc, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

theorem slConj_eq_of_mem_blk {j : Fin 4} {g : SL(4, F)} (hg : g ∈ coordBlockSL F (Jc j)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F (dGL j) g = g := by
  apply Subtype.ext
  rw [coe_slConj_dGL]
  ext i k
  rw [dMat_conj_apply]
  rw [mem_coordBlockSL_iff] at hg
  by_cases hi : i = j
  · have hg1 := hg i k (Or.inl (by simp [mem_Jc, hi]))
    rw [hg1]
    by_cases hik : i = k
    · subst hik
      simp only [ite_true]
      calc (sgn j i : F) * 1 * sgn j i = sgn j i * sgn j i := by rw [mul_one]
        _ = 1 := sgn_mul_self j i
    · simp [hik]
  · by_cases hk : k = j
    · have hg1 := hg i k (Or.inr (by simp [mem_Jc, hk]))
      rw [hg1]
      by_cases hik : i = k
      · subst hik
        exact absurd hk hi
      · simp [hik]
    · have e1 : (sgn j i : F) = 1 := by simp [sgn, hi]
      have e2 : (sgn j k : F) = 1 := by simp [sgn, hk]
      rw [e1, e2]
      ring

theorem exists_two_ne (j : Fin 4) : ∃ a b : Fin 4, a ≠ b ∧ a ≠ j ∧ b ≠ j := by
  fin_cases j <;> decide

theorem comm_of_fix (h2 : (2 : F) ≠ 0) {j : Fin 4} {g : SL(4, F)}
    (h : conjAut 4 F (dGL j) (proj 4 F g) = proj 4 F g) :
    (dMat j : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * dMat j := by
  rw [conjAut_proj] at h
  obtain ⟨c, -, hc⟩ := OuterL4.proj_eq_exists (n := 4) h
  rw [coe_slConj_dGL] at hc
  have hent : ∀ i k : Fin 4, (g : Matrix (Fin 4) (Fin 4) F) i k =
      (c : F) * (sgn j i * (g : Matrix (Fin 4) (Fin 4) F) i k * sgn j k) := by
    intro i k
    have := congrFun (congrFun hc i) k
    rw [Matrix.smul_apply, dMat_conj_apply] at this
    simpa using this
  have hc1 : (c : F) = 1 := by
    by_contra hne
    have hzero : ∀ i k : Fin 4, i ≠ j → k ≠ j → (g : Matrix (Fin 4) (Fin 4) F) i k = 0 := by
      intro i k hi hk
      have e1 : (sgn j i : F) = 1 := by simp [sgn, hi]
      have e2 : (sgn j k : F) = 1 := by simp [sgn, hk]
      have := hent i k
      rw [e1, e2] at this
      have h3 : (1 - (c : F)) * (g : Matrix (Fin 4) (Fin 4) F) i k = 0 := by linear_combination this
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (sub_eq_zero.mp h4).symm hne
      · exact h4
    obtain ⟨a, b, hab, haj, hbj⟩ := exists_two_ne j
    set G : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin 4) (Fin 4) F) with hG
    set Gi : Matrix (Fin 4) (Fin 4) F := ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) with hGi
    have hGGi : G * Gi = 1 := by
      rw [hG, hGi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hrow : ∀ i : Fin 4, i ≠ j → ∀ k : Fin 4, (G * Gi) i k = G i j * Gi j k := by
      intro i hi k
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro l _ hl
        rw [hzero i l hi hl, zero_mul]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have e1 := congrFun (congrFun hGGi a) a
    have e2 := congrFun (congrFun hGGi b) a
    have e3 := congrFun (congrFun hGGi b) b
    rw [hrow a haj] at e1
    rw [hrow b hbj] at e2 e3
    simp only [Matrix.one_apply_eq] at e1 e3
    simp only [Matrix.one_apply, hab.symm, ite_false] at e2
    have h5 : Gi j a ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e1
      exact zero_ne_one e1
    have h6 : G b j = 0 := by
      rcases mul_eq_zero.mp e2 with h7 | h7
      · exact h7
      · exact absurd h7 h5
    rw [h6, zero_mul] at e3
    exact zero_ne_one e3
  have hmid : ∀ i k : Fin 4, (sgn j i : F) ≠ sgn j k → (g : Matrix (Fin 4) (Fin 4) F) i k = 0 := by
    intro i k hik
    have := hent i k
    rw [hc1, one_mul] at this
    have hs : (sgn j i : F) * sgn j k = -1 := by
      by_cases hi : i = j <;> by_cases hk : k = j
      · exact absurd (by simp [sgn, hi, hk]) hik
      · simp [sgn, hi, hk]
      · simp [sgn, hi, hk]
      · exact absurd (by simp [sgn, hi, hk]) hik
    have h3 : (2 : F) * (g : Matrix (Fin 4) (Fin 4) F) i k = 0 := by
      linear_combination this + ((g : Matrix (Fin 4) (Fin 4) F) i k) * hs
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 h2
    · exact h4
  ext i k
  rw [dMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hik : (sgn j i : F) = sgn j k
  · rw [hik]
    ring
  · rw [hmid i k hik]
    simp

theorem entry_zero_of_comm {j : Fin 4} {g : Matrix (Fin 4) (Fin 4) F}
    (hg : (dMat j : Matrix (Fin 4) (Fin 4) F) * g = g * dMat j) {i k : Fin 4}
    (hik : (sgn j i : F) ≠ sgn j k) : g i k = 0 := by
  have := congrFun (congrFun hg i) k
  rw [dMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have h3 : (sgn j i - sgn j k : F) * g i k = 0 := by linear_combination this
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hik
  · exact h4

theorem sgn_ne_of_eq_ne (h2 : (2 : F) ≠ 0) {j i k : Fin 4} (hi : i = j) (hk : k ≠ j) :
    (sgn j i : F) ≠ sgn j k := by
  simp only [sgn, hi, hk, ite_true, ite_false]
  intro h
  apply h2
  linear_combination -h

theorem compIndicator_comm (h2 : (2 : F) ≠ 0) {j : Fin 4} {g : Matrix (Fin 4) (Fin 4) F}
    (hg : (dMat j : Matrix (Fin 4) (Fin 4) F) * g = g * dMat j) :
    compIndicator F (Jc j) * g = g * compIndicator F (Jc j) := by
  ext i k
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hi : i = j <;> by_cases hk : k = j
  · simp [mem_Jc, hi, hk]
  · have h0 := entry_zero_of_comm hg (sgn_ne_of_eq_ne h2 hi hk)
    have e1 : i ∉ Jc j := by simp [mem_Jc, hi]
    have e2 : k ∈ Jc j := by simp [mem_Jc, hk]
    simp only [e1, e2, ite_true, ite_false, h0]
  · have h0 := entry_zero_of_comm hg (sgn_ne_of_eq_ne h2 hk hi).symm
    have e1 : i ∈ Jc j := by simp [mem_Jc, hi]
    have e2 : k ∉ Jc j := by simp [mem_Jc, hk]
    simp only [e1, e2, ite_true, ite_false, h0]
  · simp [mem_Jc, hi, hk]

variable (F) in
@[expose] def lay (j : Fin 4) : Subgroup (projectiveSL 4 F) :=
  (coordBlockSL F (Jc j)).map (proj 4 F)

theorem lay_fix (j : Fin 4) : ∀ q ∈ lay F j, conjAut 4 F (dGL j) q = q := by
  rintro _ ⟨g, hg, rfl⟩
  rw [conjAut_proj, slConj_eq_of_mem_blk hg]

theorem lay_norm (h2 : (2 : F) ≠ 0) (j : Fin 4) :
    ∀ q' : projectiveSL 4 F, conjAut 4 F (dGL j) q' = q' → ∀ q ∈ lay F j,
      q' * q * q'⁻¹ ∈ lay F j := by
  intro q' hq' q hq
  obtain ⟨g', rfl⟩ := proj_surjective 4 F q'
  obtain ⟨g, hg, rfl⟩ := hq
  have hcomm := comm_of_fix h2 hq'
  have hCI := compIndicator_comm h2 hcomm
  refine ⟨g' * g * g'⁻¹, conj_mem_coordBlockSL hCI hg, ?_⟩
  simp

theorem lay_open_quasisimple [Finite F] (h4 : 4 ≤ Nat.card F) (j : Fin 4) :
    CFSG.Open.IsQuasisimple ↥(lay F j) := by
  have hq : CFSG.IsQuasisimple (coordBlockSL F (Jc j)) :=
    isQuasisimple_coordBlockSL (by rw [Jc_card]; norm_num) h4
  have hq' : CFSG.Open.IsQuasisimple ↥(coordBlockSL F (Jc j)) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hker : (proj 4 F).ker ≤ Subgroup.center SL(4, F) :=
    ((ker_proj (n := 4) (K := F)).trans (scalars_eq_center 4 F)).le
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.isQuasisimple_map_of_ker_le_center
    (proj 4 F) hker hq'

theorem lay_perf [Finite F] (h4 : 4 ≤ Nat.card F) (j : Fin 4) : lay F j ≤ ⁅lay F j, lay F j⁆ :=
  (commutator_self_of_perfect (lay_open_quasisimple h4 j).1).ge

theorem lay_gen [Finite F] (h4 : 4 ≤ Nat.card F) (j : Fin 4) :
    ∃ 𝓗 : Set (Subgroup (projectiveSL 4 F)), (∀ H ∈ 𝓗, H ≤ lay F j ∧
      CFSG.Open.IsQuasisimple ↥H ∧ ∀ p ∈ lay F j, ∀ h ∈ H, p * h * p⁻¹ ∈ H) ∧
      lay F j ≤ ⨆ H ∈ 𝓗, H := by
  refine ⟨{lay F j}, ?_, ?_⟩
  · intro H hH
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact ⟨le_rfl, lay_open_quasisimple h4 j, fun p hp h hh => (lay F j).mul_mem
      ((lay F j).mul_mem hp hh) ((lay F j).inv_mem hp)⟩
  · exact le_iSup₂_of_le (lay F j) rfl le_rfl

theorem transvection_mem_blk {J : Finset (Fin 4)} {a b : Fin 4} (hab : a ≠ b) (ha : a ∈ J)
    (hb : b ∈ J) (c : F) :
    Matrix.SpecialLinearGroup.transvection hab c ∈ coordBlockSL F J := by
  rw [mem_coordBlockSL_iff]
  intro i k hik
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  have hne : ¬ (a = i ∧ b = k) := by
    rintro ⟨rfl, rfl⟩
    rcases hik with h | h
    · exact h ha
    · exact h hb
  simp only [Matrix.add_apply, Matrix.single_apply, hne, ite_false, add_zero, Matrix.one_apply]

theorem blk_sup_eq_top :
    coordBlockSL F (Jc 0) ⊔ coordBlockSL F (Jc 1) = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 4) (K := F), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  set H : Subgroup SL(4, F) := coordBlockSL F (Jc 0) ⊔ coordBlockSL F (Jc 1) with hH
  have hle0 : coordBlockSL F (Jc 0) ≤ H := le_sup_left
  have hle1 : coordBlockSL F (Jc 1) ≤ H := le_sup_right
  have hcomm : ∀ {x y : SL(4, F)}, x ∈ H → y ∈ H → ⁅x, y⁆ ∈ H := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · exact absurd (hi0.trans hj0.symm) hij
  · by_cases hj1 : j = 1
    · subst hi0 hj1
      have h02 : (0 : Fin 4) ≠ 2 := by decide
      have h21 : (2 : Fin 4) ≠ 1 := by decide
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection h02 h21 hij c (1 : F)
      rw [mul_one] at this
      rw [← this]
      exact hcomm (hle1 (transvection_mem_blk h02 (by simp [mem_Jc]) (by simp [mem_Jc]) c))
        (hle0 (transvection_mem_blk h21 (by simp [mem_Jc]) (by simp [mem_Jc]) 1))
    · exact hle1 (transvection_mem_blk hij (by simp [mem_Jc, hi0]) (by simp [mem_Jc, hj1]) c)
  · by_cases hi1 : i = 1
    · subst hj0 hi1
      have h12 : (1 : Fin 4) ≠ 2 := by decide
      have h20 : (2 : Fin 4) ≠ 0 := by decide
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection h12 h20 hij c (1 : F)
      rw [mul_one] at this
      rw [← this]
      exact hcomm (hle0 (transvection_mem_blk h12 (by simp [mem_Jc]) (by simp [mem_Jc]) c))
        (hle1 (transvection_mem_blk h20 (by simp [mem_Jc]) (by simp [mem_Jc]) 1))
    · exact hle1 (transvection_mem_blk hij (by simp [mem_Jc, hi1]) (by simp [mem_Jc, hj0]) c)
  · exact hle0 (transvection_mem_blk hij (by simp [mem_Jc, hi0]) (by simp [mem_Jc, hj0]) c)

theorem lay_sup : lay F 0 ⊔ lay F 1 = ⊤ := by
  rw [lay, lay, ← Subgroup.map_sup, blk_sup_eq_top, Subgroup.map_top_of_surjective _
    (proj_surjective 4 F)]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.SqL4

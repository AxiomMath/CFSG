module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

theorem exists_torus (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate)
    {E : Matrix ι ι K} (hE : E * E = 0)
    (hadj : ∀ u v, Q.polarBilin (E *ᵥ u) v = Q.polarBilin u (E *ᵥ v))
    (hQE : ∀ v, Q (E *ᵥ v) = 0) {k : ℕ} (a : Fin k → ι → K) (ha : ∀ j, E *ᵥ a j = 0)
    (hli : LinearIndependent K a)
    (hdisj : Disjoint (LinearMap.range E.mulVecLin) (Submodule.span K (Set.range a)))
    {c : K} (hc : c ≠ 0) :
    ∃ D : GL ι K, (∀ v, Q ((D : Matrix ι ι K) *ᵥ v) = Q v) ∧
      (∀ j, (D : Matrix ι ι K) *ᵥ a j = a j) ∧
      ((D⁻¹ : GL ι K) : Matrix ι ι K) * E * D = c • E := by
  classical
  set B := Q.polarBilin with hBdef
  have hBs : ∀ x y, B x y = B y x := polarBilin_comm Q
  have hnd : ∀ w, (∀ z, B z w = 0) → w = 0 := hQ.2
  set U := LinearMap.range E.mulVecLin with hU
  set m := finrank K U with hm
  let bU := Module.finBasis K U
  set u : Fin m → ι → K := fun i => (bU i : ι → K) with hu
  have huU : ∀ i, u i ∈ U := fun i => (bU i).2
  have hQU : ∀ w ∈ U, Q w = 0 := by
    rintro _ ⟨v, rfl⟩
    exact hQE v
  have hBUU : ∀ w ∈ U, ∀ w' ∈ U, B w w' = 0 := by
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩
    change B (E *ᵥ v) (E *ᵥ v') = 0
    rw [hadj, mulVec_mulVec, hE, zero_mulVec, map_zero]
  have haU : ∀ j, ∀ w ∈ U, B (a j) w = 0 := by
    rintro j _ ⟨v, rfl⟩
    change B (a j) (E *ᵥ v) = 0
    rw [← hadj, ha, map_zero, LinearMap.zero_apply]
  have hu_li : LinearIndependent K u := bU.linearIndependent.map' U.subtype U.ker_subtype
  have hspanU : Submodule.span K (Set.range u) ≤ U :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact huU i)
  let g : Fin m ⊕ Fin k → ι → K := Sum.elim u a
  have hg : LinearIndependent K g := hu_li.sum_type hli (hdisj.mono_left hspanU)
  obtain ⟨w, hw⟩ := exists_polar_dual Q hQ g hg
  rw [← hBdef] at hw
  set u' : Fin m → ι → K := fun j => w (.inl j) with hu'
  have hdual : ∀ i j, B (u i) (u' j) = if i = j then 1 else 0 := fun i j => by
    have := hw (.inl i) (.inl j)
    simp only [g, Sum.elim_inl, Sum.inl.injEq] at this
    exact this
  have hau' : ∀ l j, B (a l) (u' j) = 0 := fun l j => by
    have := hw (.inr l) (.inl j)
    simp only [g, Sum.elim_inr, reduceCtorEq, ↓reduceIte] at this
    exact this
  have huu : ∀ i j, B (u i) (u j) = 0 := fun i j => hBUU _ (huU i) _ (huU j)
  obtain ⟨u'', hdual'', hiso'', hsing'', hcomb⟩ :=
    exists_singular_dual Q u u' (fun i => hQU _ (huU i)) huu hdual
  rw [← hBdef] at hdual'' hiso''
  have hau'' : ∀ l j, B (a l) (u'' j) = 0 := fun l j => by
    obtain ⟨cj, hcj⟩ := hcomb j
    rw [hcj, map_add, map_sum, hau', zero_add]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, haU l _ (huU i), smul_zero]
  have hu''u : ∀ i j, B (u'' i) (u j) = if i = j then 1 else 0 := fun i j => by
    rw [hBs, hdual'']
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  set P := LinearMap.toMatrix' (∑ i, (B (u'' i)).smulRight (u i)) with hP
  set P' := LinearMap.toMatrix' (∑ i, (B (u i)).smulRight (u'' i)) with hP'
  have hPv : ∀ v, P *ᵥ v = ∑ i, B (u'' i) v • u i := fun v => by
    rw [hP, LinearMap.toMatrix'_mulVec]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hP'v : ∀ v, P' *ᵥ v = ∑ i, B (u i) v • u'' i := fun v => by
    rw [hP', LinearMap.toMatrix'_mulVec]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hPu : ∀ j, P *ᵥ u j = u j := fun j => by
    rw [hPv]
    simp [hu''u]
  have hPu'' : ∀ j, P *ᵥ u'' j = 0 := fun j => by
    rw [hPv]
    simp [hiso'']
  have hP'u : ∀ j, P' *ᵥ u j = 0 := fun j => by
    rw [hP'v]
    simp [huu]
  have hP'u'' : ∀ j, P' *ᵥ u'' j = u'' j := fun j => by
    rw [hP'v]
    simp [hdual'']
  have hPP : P * P = P := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp only [mulVec_smul, hPu]
  have hP'P' : P' * P' = P' := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hP'v v, mulVec_sum]
    simp only [mulVec_smul, hP'u'']
  have hPP' : P * P' = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hP'v v, mulVec_sum]
    simp [mulVec_smul, hPu'']
  have hP'P : P' * P = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp [mulVec_smul, hP'u]
  have hrepr : ∀ v, E *ᵥ v = ∑ j, bU.repr ⟨E *ᵥ v, ⟨v, rfl⟩⟩ j • u j := fun v => by
    have h1 := congrArg Subtype.val (bU.sum_repr ⟨E *ᵥ v, ⟨v, rfl⟩⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have hEu : ∀ i, E *ᵥ u i = 0 := fun i => by
    obtain ⟨z, hz⟩ := huU i
    rw [← hz, Matrix.mulVecLin_apply, mulVec_mulVec, hE, zero_mulVec]
  have hEP : E * P = 0 := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hPv v, mulVec_sum]
    simp [mulVec_smul, hEu]
  have hPE : P * E = E := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, hrepr v, mulVec_sum]
    simp only [mulVec_smul, hPu]
  have hP'E : P' * E = 0 := ext_iff_mulVec.mpr fun v => by
    have h1 : ∀ i, B (u i) (E *ᵥ v) = 0 := fun i => hBUU _ (huU i) _ ⟨v, rfl⟩
    rw [← mulVec_mulVec, hP'v]
    simp [h1]
  have hEP' : E * P' = E := ext_iff_mulVec.mpr fun v => by
    rw [← mulVec_mulVec, ← sub_eq_zero, ← mulVec_sub]
    refine hnd _ fun z => ?_
    rw [← hadj, hrepr z, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_sub, hP'v, map_sum]
    simp [hdual'', Finset.sum_ite_eq]
  obtain ⟨α, hα⟩ := isSquare_of_charTwo' c⁻¹
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hα
    exact inv_ne_zero hc hα
  have hab : (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) = 0 := by
    field_simp
    ring
  have hab' : (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) = 0 := by
    rw [show (α⁻¹ - 1) + (α - 1) + (α⁻¹ - 1) * (α - 1) =
      (α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1) by ring]
    exact hab
  set X := 1 + (α - 1) • P + (α⁻¹ - 1) • P' with hX
  set X' := 1 + (α⁻¹ - 1) • P + (α - 1) • P' with hX'
  have hXX' : X * X' = 1 := one_add_two_smul_mul hPP hP'P' hPP' hP'P hab hab'
  have hX'X : X' * X = 1 := one_add_two_smul_mul hPP hP'P' hPP' hP'P hab' hab
  let D : GL ι K := ⟨X, X', hXX', hX'X⟩
  have hDinv : ((D⁻¹ : GL ι K) : Matrix ι ι K) = X' := rfl
  have hXv : ∀ v, X *ᵥ v = v + (α - 1) • (P *ᵥ v) + (α⁻¹ - 1) • (P' *ᵥ v) := fun v => by
    rw [hX, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec]
  have hQP : ∀ v, Q (P *ᵥ v) = 0 := fun v => by
    rw [hPv]
    exact hQU _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (huU i))
  have hQP' : ∀ v, Q (P' *ᵥ v) = 0 := fun v => by
    rw [hP'v]
    exact apply_sum_smul_eq_zero Q u'' hsing'' hiso'' _
  have hBPv : ∀ v, B v (P *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hPv, map_sum]
    simp only [map_smul, smul_eq_mul, hBs v (u _)]
  have hBP'v : ∀ v, B v (P' *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hP'v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hBs v (u'' i), mul_comm]
  have hBPP' : ∀ v, B (P *ᵥ v) (P' *ᵥ v) = ∑ i, B (u'' i) v * B (u i) v := fun v => by
    rw [hPv, hP'v]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      hdual'', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hDQ : ∀ v, Q (X *ᵥ v) = Q v := fun v => by
    set S := ∑ i, B (u'' i) v * B (u i) v with hS
    calc Q (X *ᵥ v) = Q v + ((α - 1) + (α⁻¹ - 1) + (α - 1) * (α⁻¹ - 1)) * S := by
          rw [hXv, quad_add, quad_add, QuadraticMap.map_smul, QuadraticMap.map_smul, hQP, hQP',
            smul_zero, smul_zero, add_zero, add_zero, ← hBdef]
          simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
            hBPv, hBP'v, hBPP']
          ring
      _ = Q v := by rw [hab, zero_mul, add_zero]
  have hPa : ∀ j, P *ᵥ a j = 0 := fun j => by
    rw [hPv]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, hau'', zero_smul]
  have hP'a : ∀ j, P' *ᵥ a j = 0 := fun j => by
    rw [hP'v]
    exact Finset.sum_eq_zero fun i _ => by rw [hBs, haU j _ (huU i), zero_smul]
  refine ⟨D, hDQ, fun j => ?_, ?_⟩
  · change X *ᵥ a j = a j
    rw [hXv, hPa, hP'a, smul_zero, smul_zero, add_zero, add_zero]
  have hmod : E + (α⁻¹ - 1) • E = α⁻¹ • E := by
    nth_rewrite 1 [← one_smul K E]
    rw [← add_smul, add_sub_cancel]
  have h1 : E * X = α⁻¹ • E := by
    rw [hX, mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul, hEP, hEP', smul_zero,
      add_zero, hmod]
  have h2 : X' * E = α⁻¹ • E := by
    rw [hX', add_mul, add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul, hPE, hP'E,
      smul_zero, add_zero, hmod]
  rw [hDinv]
  change X' * E * X = c • E
  rw [mul_assoc, h1, Matrix.mul_smul, h2, smul_smul, ← mul_inv, ← hα, inv_inv]

end CFSG.ComponentClassification.RankTwoClassical

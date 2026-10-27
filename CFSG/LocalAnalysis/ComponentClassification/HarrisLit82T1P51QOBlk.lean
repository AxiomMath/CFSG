module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (blockOn blockOn_apply_mem blockOn_apply_not_mem
  diagGL)
open CFSG.ComponentClassification.Burgoyne.U (blockGL coe_blockGL)

variable {K : Type} [Field K]

theorem two_lt_card_of_ringChar [Finite K] (hK : ringChar K ≠ 2) : 2 < Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hodd : ¬ Even (Fintype.card K) := fun h => hK (FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 h))
  rw [Nat.card_eq_fintype_card] at h1 ⊢
  by_contra h
  exact hodd (by rw [show Fintype.card K = 2 by omega]; exact even_two)

theorem eq_smul_one_of_commute_matrixDerived [Finite K] (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    {R : GL (Fin n) K} (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R)
    {M : Matrix (Fin n) (Fin n) K}
    (h : ∀ Z ∈ matrixDerived (oQ R), M * (Z : Matrix (Fin n) (Fin n) K) = Z * M) :
    ∃ c : K, M = c • 1 := by
  have hnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : 3 ≤ Module.finrank K (Fin n → K) := by rwa [Module.finrank_fin_fun]
  obtain ⟨hiff, -⟩ :=
    RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      (two_lt_card_of_ringChar hK) (oQ R) hnd hdim
  have hmap : matrixDerived (oQ R) = (⁅TauCeti.QuadraticMap.orthogonalGroup (oQ R),
      TauCeti.QuadraticMap.orthogonalGroup (oQ R)⁆).map matrixLinearIso.symm.toMonoidHom := by
    have key : ∀ H : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)),
        H.comap matrixLinearIso.toMonoidHom = H.map matrixLinearIso.symm.toMonoidHom :=
      fun H => Subgroup.comap_equiv_eq_map_symm
        (matrixLinearIso : GL (Fin n) K ≃* ((Fin n → K) ≃ₗ[K] (Fin n → K))) H
    rw [matrixDerived, matrixIsometries, key, Subgroup.map_commutator]
  obtain ⟨c, hc⟩ := (hiff M.mulVecLin).mp fun g hg => by
    have hZ : matrixLinearIso.symm g ∈ matrixDerived (oQ R) := by
      rw [hmap]
      exact ⟨g, hg, rfl⟩
    have hgZ : ∀ v, g v = ((matrixLinearIso.symm g : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v := fun v => by
      have e : g = matrixLinearIso (matrixLinearIso.symm g) :=
        (MulEquiv.apply_symm_apply _ g).symm
      conv_lhs => rw [e]
      rfl
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply, hgZ,
      mulVec_mulVec, h _ hZ]
  refine ⟨c, Matrix.ext_iff_mulVec.mpr fun v => ?_⟩
  have h1 := congrArg (fun f : (Fin n → K) →ₗ[K] (Fin n → K) => f v) hc
  simp only [Matrix.mulVecLin_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  rw [h1, smul_mulVec, one_mulVec]

theorem eq_zero_of_forall_mulVec_eq [Finite K] (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    {R : GL (Fin n) K} (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) {v : Fin n → K}
    (hv : ∀ Z ∈ matrixDerived (oQ R), (Z : Matrix (Fin n) (Fin n) K) *ᵥ v = v) : v = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute_matrixDerived hK hn hR
    (M := vecMulVec v ((R : Matrix (Fin n) (Fin n) K) *ᵥ v)) fun Z hZ => by
      have hiso : (Z : Matrix (Fin n) (Fin n) K)ᵀ * R * Z = R :=
        (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
          ((mem_matrixIsometries_oQ h2 R hR Z).1 (matrixDerived_le_isometries _ hZ))
      have huZ : ((R : Matrix (Fin n) (Fin n) K) *ᵥ v) ᵥ* (Z : Matrix (Fin n) (Fin n) K) =
          (R : Matrix (Fin n) (Fin n) K) *ᵥ v := by
        rw [← mulVec_transpose]
        conv_lhs => rw [← hv Z hZ]
        rw [mulVec_mulVec, mulVec_mulVec, hiso]
      rw [vecMulVec_mul, mul_vecMulVec, huZ, hv Z hZ]
  have hM : ∀ i j, v i * ((R : Matrix (Fin n) (Fin n) K) *ᵥ v) j = if i = j then c else 0 := by
    intro i j
    have e := congrFun (congrFun hc i) j
    rw [vecMulVec_apply] at e
    rw [e, Matrix.smul_apply, one_apply]
    split_ifs <;> simp
  by_contra hv0
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hu0 : (R : Matrix (Fin n) (Fin n) K) *ᵥ v ≠ 0 := by
    intro h0
    apply hv0
    have e := congrArg (fun x => ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) h0
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] using e
  obtain ⟨b, hb⟩ : ∃ b, ((R : Matrix (Fin n) (Fin n) K) *ᵥ v) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  have hba : a = b := by
    by_contra hne
    have e := hM a b
    rw [ite_eq_right hne] at e
    exact mul_ne_zero ha hb e
  subst hba
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨a', ha'⟩ := exists_ne a
  have hc0 : c ≠ 0 := by
    have e := hM a a
    rw [ite_eq_left rfl] at e
    rw [← e]
    exact mul_ne_zero ha hb
  have hva' : v a' ≠ 0 := by
    intro h0
    have e := hM a' a'
    rw [ite_eq_left rfl, h0, zero_mul] at e
    exact hc0 e.symm
  have e := hM a' a
  rw [ite_eq_right ha'] at e
  exact mul_ne_zero hva' hb e

theorem eq_zero_of_forall_vecMul_eq [Finite K] (hK : ringChar K ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    {R : GL (Fin n) K} (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) {u : Fin n → K}
    (hu : ∀ Z ∈ matrixDerived (oQ R), u ᵥ* (Z : Matrix (Fin n) (Fin n) K) = u) : u = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRR : ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * R = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRR' : (R : Matrix (Fin n) (Fin n) K) * ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfix : ∀ Z ∈ matrixDerived (oQ R), (Z : Matrix (Fin n) (Fin n) K) *ᵥ
      (((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) =
        ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u := by
    intro Z hZ
    have hiso : ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * R *
        ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = R :=
      (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
        ((mem_matrixIsometries_oQ h2 R hR _).1 (matrixDerived_le_isometries _ (inv_mem hZ)))
    have hWZ : ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have key : (Z : Matrix (Fin n) (Fin n) K) * ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
      calc (Z : Matrix (Fin n) (Fin n) K) * ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ * R *
              ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * Z *
            ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [hiso, hRR, Matrix.one_mul]
        _ = ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
              ((R : Matrix (Fin n) (Fin n) K) *
                (((Z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z) *
                  ((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hWZ, Matrix.mul_one, hRR', Matrix.mul_one]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, mulVec_transpose, hu _ (inv_mem hZ)]
  have h0 := eq_zero_of_forall_mulVec_eq hK hn hR hfix
  have e := congrArg (fun x => (R : Matrix (Fin n) (Fin n) K) *ᵥ x) h0
  simpa only [mulVec_mulVec, hRR', one_mulVec, mulVec_zero] using e

theorem sum_eq_sum_equivFin {d : ℕ} {I : Finset (Fin d)} (F : Fin d → K)
    (hF : ∀ z ∉ I, F z = 0) : ∑ z, F z = ∑ k : Fin I.card, F (I.equivFin.symm k) := by
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun z _ hz => hF z hz),
    ← Finset.sum_coe_sort I]
  exact (Equiv.sum_comp I.equivFin.symm (fun z : I => F z)).symm

variable {d : ℕ} {I : Finset (Fin d)}

theorem mul_blockOn_apply_mem (D : Matrix (Fin d) (Fin d) K)
    (X : Matrix (Fin I.card) (Fin I.card) K) (x : Fin d) {y : Fin d} (hy : y ∈ I) :
    (D * blockOn K I X) x y = ∑ k, D x (I.equivFin.symm k) * X k (I.equivFin ⟨y, hy⟩) := by
  rw [mul_apply, sum_eq_sum_equivFin _ fun z hz => by
    rw [blockOn_apply_not_mem _ _ (Or.inl hz), ite_eq_right (fun h : z = y => hz (h ▸ hy)),
      mul_zero]]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [blockOn_apply_mem _ _ (I.equivFin.symm k).2 hy]
  simp

theorem blockOn_mul_apply_mem (D : Matrix (Fin d) (Fin d) K)
    (X : Matrix (Fin I.card) (Fin I.card) K) {x : Fin d} (hx : x ∈ I) (y : Fin d) :
    (blockOn K I X * D) x y = ∑ k, X (I.equivFin ⟨x, hx⟩) k * D (I.equivFin.symm k) y := by
  rw [mul_apply, sum_eq_sum_equivFin _ fun z hz => by
    rw [blockOn_apply_not_mem _ _ (Or.inr hz), ite_eq_right (fun h : x = z => hz (h ▸ hx)),
      zero_mul]]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [blockOn_apply_mem _ _ hx (I.equivFin.symm k).2]
  simp

theorem mul_blockOn_apply_not_mem (D : Matrix (Fin d) (Fin d) K)
    (X : Matrix (Fin I.card) (Fin I.card) K) (x : Fin d) {y : Fin d} (hy : y ∉ I) :
    (D * blockOn K I X) x y = D x y := by
  rw [mul_apply, Finset.sum_eq_single y]
  · rw [blockOn_apply_not_mem _ _ (Or.inr hy), ite_eq_left rfl, mul_one]
  · intro z _ hzy
    rw [blockOn_apply_not_mem _ _ (Or.inr hy), ite_eq_right hzy, mul_zero]
  · exact fun h => absurd (Finset.mem_univ y) h

theorem blockOn_mul_apply_not_mem (D : Matrix (Fin d) (Fin d) K)
    (X : Matrix (Fin I.card) (Fin I.card) K) {x : Fin d} (hx : x ∉ I) (y : Fin d) :
    (blockOn K I X * D) x y = D x y := by
  rw [mul_apply, Finset.sum_eq_single x]
  · rw [blockOn_apply_not_mem _ _ (Or.inl hx), ite_eq_left rfl, one_mul]
  · intro z _ hzx
    rw [blockOn_apply_not_mem _ _ (Or.inl hx), ite_eq_right (Ne.symm hzx), zero_mul]
  · exact fun h => absurd (Finset.mem_univ x) h

theorem eq_of_commute_oBlock [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hI : 3 ≤ I.card) {D : Matrix (Fin d) (Fin d) K}
    (hD : ∀ g ∈ oBlock K hw I, D * (g : Matrix (Fin d) (Fin d) K) = g * D) :
    ∃ c : K, ∀ x ∈ I, ∀ y, D x y = (if x = y then c else 0) ∧
      D y x = (if y = x then c else 0) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := diagGL_transpose _
  have hX : ∀ X ∈ matrixDerived (oQ (diagGL (wRes_ne_zero hw I))),
      D * blockOn K I (X : Matrix (Fin I.card) (Fin I.card) K) = blockOn K I X * D := by
    intro X hX
    have hmem : blockGL K I X ∈ oBlock K hw I := by
      rw [oBlock_eq_map, ← matrixDerived_oQ h2 _ hR]
      exact ⟨X, hX, rfl⟩
    have e := hD _ hmem
    rwa [coe_blockGL] at e
  obtain ⟨c, hc⟩ := eq_smul_one_of_commute_matrixDerived hK hI hR
    (M := Matrix.of fun a b => D (I.equivFin.symm a) (I.equivFin.symm b)) fun X hXm => by
      ext a b
      have h := congrFun (congrFun (hX X hXm) (I.equivFin.symm a)) (I.equivFin.symm b)
      rw [mul_blockOn_apply_mem _ _ _ (I.equivFin.symm b).2,
        blockOn_mul_apply_mem _ _ (I.equivFin.symm a).2] at h
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at h
      simpa only [mul_apply, of_apply] using h
  have hcol : ∀ y ∉ I, ∀ k, D (I.equivFin.symm k) y = 0 := by
    intro y hy
    have h0 := eq_zero_of_forall_mulVec_eq hK hI hR (v := fun k => D (I.equivFin.symm k) y)
      fun X hXm => by
        funext a
        have h := congrFun (congrFun (hX X hXm) (I.equivFin.symm a)) y
        rw [mul_blockOn_apply_not_mem _ _ _ hy,
          blockOn_mul_apply_mem _ _ (I.equivFin.symm a).2] at h
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at h
        rw [mulVec, dotProduct]
        exact h.symm
    exact fun k => congrFun h0 k
  have hrow : ∀ y ∉ I, ∀ k, D y (I.equivFin.symm k) = 0 := by
    intro y hy
    have h0 := eq_zero_of_forall_vecMul_eq hK hI hR (u := fun k => D y (I.equivFin.symm k))
      fun X hXm => by
        funext b
        have h := congrFun (congrFun (hX X hXm) y) (I.equivFin.symm b)
        rw [mul_blockOn_apply_mem _ _ _ (I.equivFin.symm b).2,
          blockOn_mul_apply_not_mem _ _ hy] at h
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply] at h
        rw [vecMul, dotProduct]
        exact h
    exact fun k => congrFun h0 k
  refine ⟨c, fun x hx y => ?_⟩
  have hxe : x = I.equivFin.symm (I.equivFin ⟨x, hx⟩) := by simp
  by_cases hy : y ∈ I
  · have hye : y = I.equivFin.symm (I.equivFin ⟨y, hy⟩) := by simp
    have h1 := congrFun (congrFun hc (I.equivFin ⟨x, hx⟩)) (I.equivFin ⟨y, hy⟩)
    have h2' := congrFun (congrFun hc (I.equivFin ⟨y, hy⟩)) (I.equivFin ⟨x, hx⟩)
    simp only [of_apply, Equiv.symm_apply_apply, Matrix.smul_apply, one_apply,
      EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h1 h2'
    exact ⟨h1, h2'⟩
  · have hxy : x ≠ y := fun h => hy (h ▸ hx)
    rw [ite_eq_right hxy, ite_eq_right (Ne.symm hxy)]
    refine ⟨?_, ?_⟩
    · rw [hxe]
      exact hcol y hy _
    · rw [hxe]
      exact hrow y hy _

end CFSG.ComponentClassification.HarrisLit.T1.P51Q

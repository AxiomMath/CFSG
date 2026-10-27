module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassU

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K]

theorem eq_smul_one_of_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι K}
    {c : K} (hA : ∀ v, A *ᵥ v = c • v) : A = c • 1 :=
  ext_iff_mulVec.mpr fun v => by rw [hA, Matrix.smul_mulVec, one_mulVec]

theorem norm_eq_one_of_smul (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = c • 1) : h.norm c = 1 := by
  have hU := mem_hypUnitary.mp hA
  rw [hc, show (c • 1 : Matrix (HypIndex r ε) (HypIndex r ε) K) = Matrix.scalar _ c by
    rw [scalar_apply, smul_one_eq_diagonal], scalar_gram] at hU
  have h2 := congrFun (congrFun hU (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
  simpa [hypGram_apply] using h2

theorem orthonormal_elim (h : UnitaryFieldData p f K) {κ₁ κ₂ : Type*} [DecidableEq κ₁]
    [DecidableEq κ₂] {a : κ₁ → HypIndex 2 0 → K} {b : κ₂ → HypIndex 2 0 → K}
    (ha : ∀ i j, hypForm h 2 0 (a i) (a j) = if i = j then 1 else 0)
    (hb : ∀ i j, hypForm h 2 0 (b i) (b j) = if i = j then 1 else 0)
    (hab : ∀ i j, hypForm h 2 0 (a i) (b j) = 0) :
    ∀ i j, hypForm h 2 0 (Sum.elim a b i) (Sum.elim a b j) = if i = j then 1 else 0 := by
  have hba : ∀ i j, hypForm h 2 0 (b j) (a i) = 0 := fun i j => by
    rw [← (hypForm_isSymm h).eq (a i) (b j), hab, map_zero]
  rintro (i | i) (j | j)
  · simp [ha]
  · simp [hab]
  · simp [hba]
  · simp [hb]

theorem exists_orthonormal_of_finrank (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex 2 0 → K)}
    (hW : ((hypForm h 2 0).domRestrict₁₂ W W).SeparatingLeft) {k : ℕ} (hk : finrank K W = k) :
    ∃ a : Fin k → HypIndex 2 0 → K, (∀ i, a i ∈ W) ∧
      ∀ i j, hypForm h 2 0 (a i) (a j) = if i = j then 1 else 0 := by
  have hBW : ((hypForm h 2 0).domRestrict₁₂ W W).IsSymm :=
    ⟨fun x y => (hypForm_isSymm (r := 2) (ε := 0) h).eq x y⟩
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBW hW
  refine ⟨fun i => (e (Fin.cast hk.symm i) : HypIndex 2 0 → K), fun i => (e _).2,
    fun i j => ?_⟩
  have := he (Fin.cast hk.symm i) (Fin.cast hk.symm j)
  simp only [LinearMap.domRestrict₁₂_apply, Fin.cast_inj] at this
  exact this

theorem exists_frame_of_norm_eq_one (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1) (hN : h.norm l = 1)
    (hns : ∀ c : K, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ≠ c • 1) :
    (∃ v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K,
      (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
        Sum.elim (fun _ => l) (fun _ => -l) i • v i) ∨
    (∃ d : K, h.norm d = 1 ∧ ∃ v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K,
      (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
        Sum.elim (fun _ => d) (fun _ => -d) i • v i) := by
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨horth, hsepP, hsepM, -⟩ := exists_split_centralizer_equiv hp (hypForm_isSymm h)
    (hypForm_separatingLeft h) hl0 hAA' hN
  rw [coe_unitaryOfHyp] at horth hsepP hsepM hAA'
  have hc : IsCompl (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)))
      (eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) :=
    isCompl_ker_sub_one_ker_add_one (two_ne_zero_of_odd h hp) (invSMulOp_mul_self hl0 hAA')
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_hypIndex_fun] at hdim
  have hP : ∀ v ∈ eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = l • v :=
    fun v hv => mulVec_eq_of_mem_eigenPlus hl0 hv
  have hM : ∀ v ∈ eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = (-l) • v :=
    fun v hv => mulVec_eq_of_mem_eigenMinus hl0 hv
  have hNm : h.norm (-l) = 1 := by
    rw [UnitaryFieldData.norm, map_neg, neg_mul_neg]
    exact hN
  have horth' : ∀ v ∈ eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      ∀ w ∈ eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
        hypForm h 2 0 v w = 0 := fun v hv w hw => by
    rw [← (hypForm_isSymm h).eq w v, horth w hw v hv, map_zero]
  obtain ⟨k, hk⟩ : ∃ k, finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0)
      (HypIndex 2 0) K))) = k := ⟨_, rfl⟩
  have hk4 : k ≤ 4 := by omega
  interval_cases k
  · exfalso
    have htop : eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_hypIndex_fun]; omega)
    exact hns (-l) (eq_smul_one_of_mulVec fun v => hM v (htop ▸ Submodule.mem_top))
  · obtain ⟨a, haW, ha⟩ := exists_orthonormal_of_finrank h hsepM (k := 3) (by omega)
    obtain ⟨b, hbW, hb⟩ := exists_orthonormal_of_finrank h hsepP hk
    refine Or.inr ⟨-l, hNm, Sum.elim a b,
      orthonormal_elim h ha hb fun i j => horth' _ (haW i) _ (hbW j), ?_⟩
    rintro (i | i)
    · exact hM _ (haW i)
    · rw [Sum.elim_inr, Sum.elim_inr, neg_neg]
      exact hP _ (hbW i)
  · obtain ⟨a, haW, ha⟩ := exists_orthonormal_of_finrank h hsepP hk
    obtain ⟨b, hbW, hb⟩ := exists_orthonormal_of_finrank h hsepM (k := 2) (by omega)
    refine Or.inl ⟨Sum.elim a b,
      orthonormal_elim h ha hb fun i j => horth _ (haW i) _ (hbW j), ?_⟩
    rintro (i | i)
    · exact hP _ (haW i)
    · exact hM _ (hbW i)
  · obtain ⟨a, haW, ha⟩ := exists_orthonormal_of_finrank h hsepP hk
    obtain ⟨b, hbW, hb⟩ := exists_orthonormal_of_finrank h hsepM (k := 1) (by omega)
    refine Or.inr ⟨l, hN, Sum.elim a b,
      orthonormal_elim h ha hb fun i j => horth _ (haW i) _ (hbW j), ?_⟩
    rintro (i | i)
    · exact hP _ (haW i)
    · exact hM _ (hbW i)
  · exfalso
    have htop : eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_hypIndex_fun]; omega)
    exact hns l (eq_smul_one_of_mulVec fun v => hP v (htop ▸ Submodule.mem_top))

theorem classify_inv_U4 (h : UnitaryFieldData p f K) (hp : p ≠ 2) {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0)
    (hord : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0) = 2) :
    ∃ l : K, l ≠ 0 ∧ (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 ∧
      ((h.norm l = 1 ∧
        ((∃ v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K,
          (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
          ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
            Sum.elim (fun _ => l) (fun _ => -l) i • v i) ∨
        (∃ d : K, h.norm d = 1 ∧ ∃ v : Fin 3 ⊕ Fin 1 → HypIndex 2 0 → K,
          (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
          ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
            Sum.elim (fun _ => d) (fun _ => -d) i • v i))) ∨
      (h.norm l = -1 ∧ ∃ e g : Fin 2 → HypIndex 2 0 → K,
        (∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ e i = l • e i) ∧
        (∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ g i = (-l) • g i) ∧
        (∀ i j, hypForm h 2 0 (e i) (e j) = 0) ∧ (∀ i j, hypForm h 2 0 (g i) (g j) = 0) ∧
        ∀ i j, hypForm h 2 0 (e i) (g j) = if i = j then 1 else 0)) := by
  have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h 2 0) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
  obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
  obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
  have hAA' : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1 := by
    have h1 := congrArg (fun g : GL (HypIndex 2 0) K =>
      (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) hAA
    simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ c : K, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) ≠ c • 1 := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact (Matrix.isUnits_det_units A).ne_zero (by rw [hc, det_zero])
    have hmem : (⟨A, hA⟩ : hypUnitary h 2 0) ∈ normOneScalars h (hypUnitary h 2 0) 0 := by
      refine ⟨Units.mk0 c hc0, norm_eq_one_of_smul h (by norm_num) hA hc, pow_zero _, ?_⟩
      apply Units.ext
      change (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = _
      rw [hc, GeneralLinearGroup.coe_scalar, Units.val_mk0, scalar_apply,
        smul_one_eq_diagonal]
    have h1 : (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h 2 0) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmem
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hN : h.norm l = 1 ∨ h.norm l = -1 := by
    have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq h, ← pow_two, hld, hd]
    exact mul_self_eq_one_iff.mp h1
  refine ⟨l, hl0, hAA', ?_⟩
  rcases hN with hN | hN
  · exact Or.inl ⟨hN, exists_frame_of_norm_eq_one h hp hA hl0 hAA' hN hns⟩
  · exact Or.inr ⟨hN, exists_paired_eigen_basis h hp (by norm_num) hA hl0 hAA' hN⟩

end InvClassU

end CFSG.ComponentClassification.CatFactsL4U4

module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronFix

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL
  commutatorElement_mul_mem_center)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem X10Data.le_isoCent {R : GL (Fin d) K} (hK : ringChar K ≠ 2)
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {g : similarityPairs (oQ R)}
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R g M Q) (hσ : g.val.right = 1) :
    M ≤ ⁅isoCent R g.val.left, isoCent R g.val.left⁆ ∧
      (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)) ≤
        matrixDerived (oQ R) ∧
      ((⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)).subgroupOf
        (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ g) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set S := g.val.left with hSdef
  have hSM := h.commute_left hσ
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K R := fun X hX =>
    (mem_matrixIsometries_oQ h2 R hR X).1 (matrixDerived_le_isometries _ (h.le hX))
  have hMC : M ≤ isoCent R S := fun X hX =>
    ⟨hiso X hX, mem_centralizer_singleton_iff.2 (hSM X hX)⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.perf]
    exact commutator_mono hMC hMC
  · rw [matrixDerived_oQ h2 R hR]
    exact commutator_mono inf_le_left inf_le_left
  · rintro _ ⟨x, hx, rfl⟩
    rw [DX.mem_autFixed_iff, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply]
    have hxC : (x : GL (Fin d) K) ∈ isoCent R S := commutator_le_self _ (mem_subgroupOf.1 hx)
    have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hxC).2
    change S * (x : GL (Fin d) K) * S⁻¹ = x
    rw [← hc, mul_inv_cancel_right]

theorem le_of_map_projH_le {H L M : Subgroup (GL (Fin d) K)} (hM : M ≤ H) (hperf : ⁅M, M⁆ = M)
    (hP : (M.subgroupOf H).map (projH H) ≤ (L.subgroupOf H).map (projH H)) : M ≤ L := by
  have hlift : ∀ m (hm : m ∈ M), ∃ ω ∈ L.subgroupOf H, ∃ z ∈ center H,
      (⟨m, hM hm⟩ : H) = ω * z := by
    intro m hm
    obtain ⟨ω, hω, hωm⟩ := hP ⟨⟨m, hM hm⟩, mem_subgroupOf.2 hm, rfl⟩
    exact ⟨ω, hω, ω⁻¹ * ⟨m, hM hm⟩,
      scalars_subgroupOf_le_center ((projH_eq_projH_iff).1 hωm), by group⟩
  rw [← hperf, commutator_le]
  intro a ha b hb
  obtain ⟨ω₁, hω₁, z₁, hz₁, e₁⟩ := hlift a ha
  obtain ⟨ω₂, hω₂, z₂, hz₂, e₂⟩ := hlift b hb
  have e : ⁅(⟨a, hM ha⟩ : H), ⟨b, hM hb⟩⁆ = ⁅ω₁, ω₂⁆ := by
    rw [e₁, e₂, commutatorElement_mul_mem_center ω₁ ω₂ hz₁ hz₂]
  have e' := congrArg Subtype.val e
  change ⁅a, b⁆ = ⁅(ω₁ : GL (Fin d) K), (ω₂ : GL (Fin d) K)⁆ at e'
  rw [e', commutatorElement_def]
  have h₁ := mem_subgroupOf.1 hω₁
  have h₂ := mem_subgroupOf.1 hω₂
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem X10Data.map_eq_isoCent [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {g : similarityPairs (oQ R)}
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R g M Q) (hσ : g.val.right = 1)
    (hN : Group.IsSolvable (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
        Subgroup (GL (Fin d) K)) ∨
      IsQuasisimple (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K))) :
    (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)) ≤
        matrixDerived (oQ R) ∧
      (M.subgroupOf (matrixDerived (oQ R))).map (projH _) =
        ((⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)).subgroupOf
          (matrixDerived (oQ R))).map (projH _) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set S := g.val.left with hSdef
  set N : Subgroup (GL (Fin d) K) := ⁅isoCent R S, isoCent R S⁆ with hNdef
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  have hSM := h.commute_left hσ
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K R := fun X hX =>
    (mem_matrixIsometries_oQ h2 R hR X).1 (matrixDerived_le_isometries _ (h.le hX))
  have hMC : M ≤ isoCent R S := fun X hX =>
    ⟨hiso X hX, mem_centralizer_singleton_iff.2 (hSM X hX)⟩
  have hMN : M ≤ N := by
    rw [← h.perf]
    exact commutator_mono hMC hMC
  have hNH : N ≤ H := by
    rw [hH, matrixDerived_oQ h2 R hR]
    exact commutator_mono inf_le_left inf_le_left
  refine ⟨hNH, ?_⟩
  set Pn := (N.subgroupOf H).map (projH H) with hPn
  have hQP : Qb ≤ Pn := map_mono fun g hg => mem_subgroupOf.2 (hMN (mem_subgroupOf.1 hg))
  have hPs : Pn ≤ autFixed (oκ _ g) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [DX.mem_autFixed_iff, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply]
    have hxC : (x : GL (Fin d) K) ∈ isoCent R S := commutator_le_self _ (mem_subgroupOf.1 hx)
    have hc := mem_centralizer_singleton_iff.1 (mem_inf.1 hxC).2
    change S * (x : GL (Fin d) K) * S⁻¹ = x
    rw [← hc, mul_inv_cancel_right]
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs h.comp
  set φ := (projH H).comp ((N.subgroupOf H).subtype.comp
    (subgroupOfEquivOfLe hNH).symm.toMonoidHom) with hφ
  have hφr : φ.range = Pn := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      (subgroupOfEquivOfLe hNH).symm.surjective, Subgroup.map_top, Subgroup.range_subtype]
  rcases hN with hsol | hqs
  · have : Group.IsSolvable φ.range := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
    rw [hφr] at this
    exact (C.not_le_of_isSolvable hQP hQc' this hQP).elim
  rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hqs φ with hb | hqr
  · rw [hφr] at hb
    rw [hb] at hQP
    exact (C.ne_bot_of_isPComponent h.fix h.comp (le_bot_iff.1 hQP)).elim
  rw [hφr] at hqr
  exact C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqr

theorem X10Data.false_of_isoCent_e8 [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {g : similarityPairs (oQ R)}
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ} (h : X10Data R g M Q) (hσ : g.val.right = 1)
    (hN : Group.IsSolvable (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
        Subgroup (GL (Fin d) K)) ∨
      IsQuasisimple (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    {X Y Z : GL (Fin d) K}
    (hX : X ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hY : Y ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hZ : Z ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ : Subgroup (GL (Fin d) K)))
    (hT : ∀ (hXH : X ∈ matrixDerived (oQ R)) (hYH : Y ∈ matrixDerived (oQ R))
      (hZH : Z ∈ matrixDerived (oQ R)),
      E8Triple (projH _ (⟨X, hXH⟩ : matrixDerived (oQ R))) (projH _ ⟨Y, hYH⟩)
        (projH _ ⟨Z, hZH⟩)) : False := by
  obtain ⟨hNH, heq⟩ := h.map_eq_isoCent hK hR hσ hN
  have hin : ∀ (W : GL (Fin d) K) (hW : W ∈ (⁅isoCent R g.val.left, isoCent R g.val.left⁆ :
      Subgroup (GL (Fin d) K))), projH _ (⟨W, hNH hW⟩ : matrixDerived (oQ R)) ∈
        (M.subgroupOf (matrixDerived (oQ R))).map (projH _) := fun W hW => by
    rw [heq]
    exact ⟨⟨W, hNH hW⟩, mem_subgroupOf.2 hW, rfl⟩
  exact h.false_of_e8 (hin X hX) (hin Y hY) (hin Z hZ) (hT _ _ _)

theorem mem_pairSet_iff {n : ℕ} (S : Finset (Fin n)) (x : Fin (2 * n)) :
    x ∈ pairSet S ↔ ((pairEquiv n).symm x).1 ∈ S := by
  simp [pairSet]

theorem pairSet_symmDiff {n : ℕ} (A B : Finset (Fin n)) :
    pairSet (symmDiff A B) = symmDiff (pairSet A) (pairSet B) := by
  ext x
  simp only [Finset.mem_symmDiff, mem_pairSet_iff]

theorem pairSet_props {n : ℕ} {T : Finset (Fin n)} (h : T.Nonempty ∧ Tᶜ.Nonempty) :
    (pairSet T).Nonempty ∧ (pairSet T)ᶜ.Nonempty := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
  refine ⟨⟨pairEquiv n (x, 0), (mem_pairSet _ _ _).2 hx⟩, ⟨pairEquiv n (y, 0), ?_⟩⟩
  rw [Finset.mem_compl, mem_pairSet]
  exact Finset.mem_compl.1 hy

theorem kronGL_signGL (n : ℕ) (T : Finset (Fin n)) :
    kronGL K n (signGL K T) = signGL K (pairSet T) :=
  Units.ext (by rw [coe_kronGL, coe_signGL, coe_signGL, kronI_signMat])

theorem e8Triple_kron_sign (h2 : (2 : K) ≠ 0) {n : ℕ} {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hn : 5 ≤ n) {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (hX : signGL K (pairSet {i, j}) ∈ matrixDerived Q)
    (hY : signGL K (pairSet {i, k}) ∈ matrixDerived Q)
    (hZ : signGL K (pairSet {i, l}) ∈ matrixDerived Q) :
    E8Triple (projH _ (⟨signGL K (pairSet {i, j}), hX⟩ : matrixDerived Q))
      (projH _ ⟨signGL K (pairSet {i, k}), hY⟩) (projH _ ⟨signGL K (pairSet {i, l}), hZ⟩) := by
  refine e8Triple_sign h2 hX hY hZ ?_
  have hs := e8Sets (by omega) hij hik hil hjk hjl hkl
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] at hs ⊢
  obtain ⟨h1, h2', h3, h4, h5, h6, h7⟩ := hs
  refine ⟨pairSet_props h1, pairSet_props h2', pairSet_props h3, ?_, ?_, ?_, ?_⟩
  · rw [← pairSet_symmDiff]
    exact pairSet_props h4
  · rw [← pairSet_symmDiff]
    exact pairSet_props h5
  · rw [← pairSet_symmDiff]
    exact pairSet_props h6
  · rw [← pairSet_symmDiff, ← pairSet_symmDiff]
    exact pairSet_props h7

theorem exists_anti_pair {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ x y : SL(2, F), x * x = -1 ∧ y * y = -1 ∧ x * y = -(y * x) := by
  have := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two
    (fun h => h2 (by rw [← Nat.cast_ofNat, ← h, ringChar.Nat.cast_ringChar]))
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 + Polynomial.C 1)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_add_C (by norm_num) 1) hodd
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C]
    at hab
  have hab' : a ^ 2 + b ^ 2 = -1 := by linear_combination hab
  have hdx : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  have hdy : (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1) * hab'
  set x : SL(2, F) := ⟨_, hdx⟩ with hx
  set y : SL(2, F) := ⟨_, hdy⟩ with hy
  have hxm : (x : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl
  have hym : (y : Matrix (Fin 2) (Fin 2) F) = !![a, b; b, -a] := rfl
  refine ⟨x, y, ?_, ?_, ?_⟩ <;> apply Subtype.ext <;>
    rw [Matrix.SpecialLinearGroup.coe_mul] <;>
    try rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  · rw [hxm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hym]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination hab' | ring
  · rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul, hxm, hym]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem ne_of_anti {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {u v : SL(2, F)}
    (huv : u * v = -(v * u)) : u * v ≠ v * u := by
  intro h
  have e : ((v * u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      -((v * u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) (h.symm.trans huv)
    simpa using this
  have e0 : ((v * u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have : (2 : F) • ((v * u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [two_smul]
      nth_rw 1 [e]
      rw [neg_add_cancel]
    exact (smul_eq_zero.1 this).resolve_left h2
  have hdet := (v * u).2
  rw [e0, Matrix.det_zero] at hdet
  exact zero_ne_one hdet

theorem X10Data.false_of_e4_sl2 {F : Type*} [Field F] [Finite F] (h2F : (2 : F) ≠ 0)
    {R : GL (Fin d) K} {g : similarityPairs (oQ R)} {M : Subgroup (GL (Fin d) K)} {Q : ℕ}
    (h : X10Data R g M Q) (hker : OKer (oQ R)) (hσ : g.val.right = 1)
    {ι : SL(2, F) →* GL (Fin d) K} (hι : Function.Injective ι) (hι1 : ι (-1) = -1)
    (hιC : ∀ B, ι B ∈ isoCent R g.val.left) (hιH : ∀ B, ι B ∈ matrixDerived (oQ R))
    (hιM : ∀ B, ∀ m ∈ M, ι B * m = m * ι B) : False := by
  obtain ⟨x, y, hxx, hyy, hxy⟩ := exists_anti_pair h2F
  have hneg : (-1 : GL (Fin d) K) = GeneralLinearGroup.scalar (Fin d) (-1) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_neg, Units.val_one, Units.val_one,
      scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_one_smul]
  have hS : ∀ B, ι B * g.val.left = g.val.left * ι B := fun B =>
    (mem_centralizer_singleton_iff.1 (mem_inf.1 (hιC B)).2)
  have hcent : ∀ u v : SL(2, F), u * v = -(v * u) →
      ∀ c : Kˣ, ι u ≠ GeneralLinearGroup.scalar (Fin d) c ∧
        ι u ≠ GeneralLinearGroup.scalar (Fin d) c * g.val.left := by
    intro u v huv c
    have hne := ne_of_anti h2F huv
    constructor
    · intro hc
      apply hne
      apply hι
      rw [map_mul, map_mul, hc]
      exact (commute_scalar c (ι v)).eq.symm
    · intro hc
      apply hne
      apply hι
      rw [map_mul, map_mul, hc, mul_assoc, ← hS v, ← mul_assoc,
        ← (commute_scalar c (ι v)).eq, mul_assoc]
  have hxy' : y * x = -(x * y) := by
    rw [hxy, neg_neg]
  have hxxy : (x * y) * x = -(x * (x * y)) := by
    rw [mul_assoc, hxy', mul_neg]
  refine h.false_of_e4 hker hσ (hιH x) (hιH y) (a := -1) (b := -1) (e := -1) ?_ ?_ ?_ (hS x)
    (hS y) (hιM x) (hιM y) (fun c => (hcent x y hxy c).1) (fun c => (hcent y x hxy' c).1) ?_
    (fun c => (hcent x y hxy c).2) (fun c => (hcent y x hxy' c).2) ?_
  · rw [← map_mul, hxx, hι1, hneg]
  · rw [← map_mul, hyy, hι1, hneg]
  · rw [← map_mul, ← map_mul, hxy, ← neg_one_mul, map_mul, hι1, hneg]
  · intro c
    rw [← map_mul]
    exact (hcent (x * y) x hxxy c).1
  · intro c
    rw [← map_mul]
    exact (hcent (x * y) x hxxy c).2

end CFSG.ComponentClassification.GSThmB.X10Orth

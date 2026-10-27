module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

abbrev hypWeyl (r : ℕ) : Subgroup (Equiv.Perm (Fin r ⊕ Fin r)) :=
  SymplecticTorusWeyl.signedPermGroup r

theorem mem_hypWeyl {w : Equiv.Perm (Fin r ⊕ Fin r)} :
    w ∈ hypWeyl r ↔ ∀ x, w x.swap = (w x).swap :=
  Iff.rfl

theorem apply_inr_of_mem_hypWeyl {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (i : Fin r) : w (.inr i) = (w (.inl i)).swap :=
  hw (.inl i)

@[expose] def absPerm {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    Equiv.Perm (Fin r) where
  toFun i := (w (.inl i)).elim id id
  invFun j := (w⁻¹ (.inl j)).elim id id
  left_inv i := by
    change (w⁻¹ (.inl ((w (.inl i)).elim id id))).elim id id = i
    rcases hwi : w (.inl i) with j | j
    · rw [Sum.elim_inl, id, Equiv.Perm.inv_eq_iff_eq.mpr hwi.symm]
      rfl
    · have h' : w (.inr i) = .inl j := by rw [apply_inr_of_mem_hypWeyl hw, hwi]; rfl
      rw [Sum.elim_inr, id, Equiv.Perm.inv_eq_iff_eq.mpr h'.symm]
      rfl
  right_inv j := by
    change (w (.inl ((w⁻¹ (.inl j)).elim id id))).elim id id = j
    rcases hwj : w⁻¹ (.inl j) with i | i
    · rw [Sum.elim_inl, id, (Equiv.Perm.inv_eq_iff_eq.mp hwj).symm]
      rfl
    · have h' : w (.inr i) = .inl j := (Equiv.Perm.inv_eq_iff_eq.mp hwj).symm
      have : w (.inl i) = .inr j := by
        have := apply_inr_of_mem_hypWeyl hw i
        rw [h'] at this
        rcases hwi : w (.inl i) with k | k <;> rw [hwi] at this <;> cases this
        rfl
      rw [Sum.elim_inr, id, this]
      rfl

theorem apply_inl_eq_of_mem_hypWeyl {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (i : Fin r) : w (.inl i) = .inl (absPerm hw i) ∨ w (.inl i) = .inr (absPerm hw i) := by
  rcases hwi : w (.inl i) with j | j <;> simp [absPerm, hwi]

@[expose] def swapSet (M : Finset (Fin r)) : Equiv.Perm (Fin r ⊕ Fin r) where
  toFun
    | .inl j => if j ∈ M then .inr j else .inl j
    | .inr j => if j ∈ M then .inl j else .inr j
  invFun
    | .inl j => if j ∈ M then .inr j else .inl j
    | .inr j => if j ∈ M then .inl j else .inr j
  left_inv x := by rcases x with j | j <;> by_cases hj : j ∈ M <;> simp [hj]
  right_inv x := by rcases x with j | j <;> by_cases hj : j ∈ M <;> simp [hj]

theorem swapSet_insert {M : Finset (Fin r)} {j : Fin r} (hj : j ∉ M) :
    swapSet (insert j M) = Equiv.swap (.inl j) (.inr j) * swapSet M := by
  ext x
  rcases x with k | k <;> by_cases hk : k = j
  · subst hk
    simp [swapSet, hj]
  · have hkM : k ∉ M ∨ k ∈ M := (em _).symm
    rcases hkM with hkM | hkM <;>
      simp [swapSet, hk, hkM, Equiv.swap_apply_of_ne_of_ne]
  · subst hk
    simp [swapSet, hj]
  · have hkM : k ∉ M ∨ k ∈ M := (em _).symm
    rcases hkM with hkM | hkM <;>
      simp [swapSet, hk, hkM, Equiv.swap_apply_of_ne_of_ne]

theorem sign_swapSet (M : Finset (Fin r)) : Equiv.Perm.sign (swapSet M) = (-1) ^ M.card := by
  induction M using Finset.induction_on with
  | empty =>
    have : swapSet (∅ : Finset (Fin r)) = 1 := by
      ext x
      rcases x with k | k <;> simp [swapSet]
    rw [this, map_one, Finset.card_empty, pow_zero]
  | insert j M hj ih =>
    rw [swapSet_insert hj, map_mul, ih, Equiv.Perm.sign_swap (by simp),
      Finset.card_insert_of_notMem hj, pow_succ, mul_comm]

@[expose] def negSet (w : Equiv.Perm (Fin r ⊕ Fin r)) : Finset (Fin r) :=
  Finset.univ.filter fun i => (w (.inl i)).isRight

theorem mem_negSet {w : Equiv.Perm (Fin r ⊕ Fin r)} {i : Fin r} :
    i ∈ negSet w ↔ (w (.inl i)).isRight := by
  simp [negSet]

theorem eq_sumCongr_mul_swapSet {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    w = Equiv.sumCongr (absPerm hw) (absPerm hw) * swapSet (negSet w) := by
  ext x
  rcases x with i | i
  · rcases apply_inl_eq_of_mem_hypWeyl hw i with hwi | hwi <;>
      simp [swapSet, mem_negSet, hwi]
  · rw [apply_inr_of_mem_hypWeyl hw]
    rcases apply_inl_eq_of_mem_hypWeyl hw i with hwi | hwi <;>
      simp [swapSet, mem_negSet, hwi]

theorem sign_of_mem_hypWeyl {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    Equiv.Perm.sign w = (-1) ^ (negSet w).card := by
  conv_lhs => rw [eq_sumCongr_mul_swapSet hw]
  rw [map_mul, Equiv.Perm.sign_sumCongr, Int.units_mul_self, one_mul, sign_swapSet]

@[expose] def lineCoord : Fin r ⊕ Fin r → HypIndex r ε
  | .inl i => .inl i
  | .inr i => .inr (.inr i)

@[expose] def hypIndexEquiv : HypIndex r ε ≃ (Fin r ⊕ Fin r) ⊕ Fin ε where
  toFun
    | .inl i => .inl (.inl i)
    | .inr (.inl k) => .inr k
    | .inr (.inr i) => .inl (.inr i)
  invFun
    | .inl (.inl i) => .inl i
    | .inl (.inr i) => .inr (.inr i)
    | .inr k => .inr (.inl k)
  left_inv x := by rcases x with i | k | i <;> rfl
  right_inv x := by rcases x with (i | i) | k <;> rfl

@[expose] def weylPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) : Equiv.Perm (HypIndex r ε) :=
  hypIndexEquiv.symm.permCongr (Equiv.sumCongr w 1)

@[simp] theorem weylPerm_inl (w : Equiv.Perm (Fin r ⊕ Fin r)) (i : Fin r) :
    weylPerm (ε := ε) w (.inl i) = lineCoord (w (.inl i)) := by
  simp only [weylPerm, Equiv.permCongr_apply, Equiv.symm_symm]
  rcases hwi : w (.inl i) with j | j <;> simp [hypIndexEquiv, hwi, lineCoord]

@[simp] theorem weylPerm_inr_inl (w : Equiv.Perm (Fin r ⊕ Fin r)) (k : Fin ε) :
    weylPerm w (.inr (.inl k) : HypIndex r ε) = .inr (.inl k) :=
  rfl

@[simp] theorem weylPerm_inr_inr (w : Equiv.Perm (Fin r ⊕ Fin r)) (i : Fin r) :
    weylPerm (ε := ε) w (.inr (.inr i)) = lineCoord (w (.inr i)) := by
  simp only [weylPerm, Equiv.permCongr_apply, Equiv.symm_symm]
  rcases hwi : w (.inr i) with j | j <;> simp [hypIndexEquiv, hwi, lineCoord]

theorem sign_weylPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    Equiv.Perm.sign (weylPerm (ε := ε) w) = Equiv.Perm.sign w := by
  rw [weylPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, map_one, mul_one]

@[expose] noncomputable def weylCoeff (h : UnitaryFieldData p f K) (c : K)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) : HypIndex r ε → K
  | .inl i => (w (.inl i)).elim (fun _ => 1) fun _ => c
  | .inr (.inl _) => 1
  | .inr (.inr i) => (w (.inl i)).elim (fun _ => 1) fun _ => (h.bar c)⁻¹

@[expose] noncomputable def weylMat (h : UnitaryFieldData p f K) (c : K)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  signedPerm (weylPerm w) (weylCoeff h c w)

theorem weylMat_mulVec_single (h : UnitaryFieldData p f K) (c : K)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) (x : HypIndex r ε) :
    weylMat h c w *ᵥ Pi.single x 1 = weylCoeff h c w x • Pi.single (weylPerm w x) 1 := by
  funext y
  rw [mulVec_single_one, col_apply, weylMat, signedPerm_apply]
  by_cases hy : y = weylPerm w x <;> simp [hy]

theorem weylMat_mulVec_z (h : UnitaryFieldData p f K) (c : K) (w : Equiv.Perm (Fin r ⊕ Fin r))
    (k : Fin ε) :
    weylMat h c w *ᵥ Pi.single (.inr (.inl k)) 1 = Pi.single (.inr (.inl k)) 1 := by
  rw [weylMat_mulVec_single, weylPerm_inr_inl, weylCoeff, one_smul]

theorem weylMat_mulVec_of_inl (h : UnitaryFieldData p f K) (c : K)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) {i j : Fin r}
    (hij : w (.inl i) = .inl j) :
    weylMat (ε := ε) h c w *ᵥ Pi.single (.inl i) 1 = Pi.single (.inl j) 1 ∧
      weylMat (ε := ε) h c w *ᵥ Pi.single (.inr (.inr i)) 1 = Pi.single (.inr (.inr j)) 1 := by
  have h' : w (.inr i) = .inr j := by rw [apply_inr_of_mem_hypWeyl hw, hij]; rfl
  refine ⟨?_, ?_⟩ <;>
    rw [weylMat_mulVec_single] <;> simp [weylCoeff, hij, h', lineCoord]

theorem weylMat_mulVec_of_inr (h : UnitaryFieldData p f K) (c : K)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) {i j : Fin r}
    (hij : w (.inl i) = .inr j) :
    weylMat (ε := ε) h c w *ᵥ Pi.single (.inl i) 1 = c • Pi.single (.inr (.inr j)) 1 ∧
      weylMat (ε := ε) h c w *ᵥ Pi.single (.inr (.inr i)) 1 =
        (h.bar c)⁻¹ • Pi.single (.inl j) 1 := by
  have h' : w (.inr i) = .inl j := by rw [apply_inr_of_mem_hypWeyl hw, hij]; rfl
  refine ⟨?_, ?_⟩ <;>
    rw [weylMat_mulVec_single] <;> simp [weylCoeff, hij, h', lineCoord]

theorem lineCoord_swap (s : Fin r ⊕ Fin r) :
    lineCoord (ε := ε) s.swap = hypPartner (lineCoord s) := by
  rcases s with i | i <;> rfl

theorem weylPerm_hypPartner {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (a : HypIndex r ε) : weylPerm w (hypPartner a) = hypPartner (weylPerm w a) := by
  rcases a with i | k | i
  · rw [hypPartner_inl, weylPerm_inr_inr, weylPerm_inl, apply_inr_of_mem_hypWeyl hw,
      lineCoord_swap]
  · rfl
  · rw [hypPartner_inr_inr, weylPerm_inl, weylPerm_inr_inr, apply_inr_of_mem_hypWeyl hw,
      lineCoord_swap, hypPartner_hypPartner]

theorem bar_weylCoeff_mul (h : UnitaryFieldData p f K) {c : K} (hc0 : c ≠ 0)
    (w : Equiv.Perm (Fin r ⊕ Fin r)) (a : HypIndex r ε) :
    h.bar (weylCoeff h c w a) * weylCoeff h c w (hypPartner a) = 1 := by
  have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).mpr hc0
  rcases a with i | k | i
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hbc]
  · simp [weylCoeff]
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, map_inv₀, h.bar_bar, hc0]

theorem weylMat_isometry (h : UnitaryFieldData p f K) {c : K} (hc0 : c ≠ 0)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    ((weylMat (ε := ε) h c w).map h.bar)ᵀ * hypGram r ε K * weylMat h c w = hypGram r ε K := by
  ext a b
  rw [← gramForm_single h (((weylMat h c w).map h.bar)ᵀ * hypGram r ε K * weylMat h c w) a b,
    ← gramForm_mulVec, weylMat_mulVec_single, weylMat_mulVec_single]
  simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, gramForm_single,
    hypGram_apply, ← weylPerm_hypPartner hw, (weylPerm w).injective.eq_iff]
  split_ifs with hab
  · subst hab
    rw [mul_one, mul_comm]
    exact bar_weylCoeff_mul h hc0 w a
  · simp

theorem det_signedPerm {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (κ : ι → K) :
    (signedPerm π κ).det = Equiv.Perm.sign π * ∏ i, κ i := by
  have : signedPerm π κ = (π⁻¹).permMatrix K * diagonal κ := by
    ext a b
    rw [mul_diagonal, signedPerm_apply]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]
    split_ifs <;> simp
  rw [this, det_mul, det_permutation, det_diagonal, Equiv.Perm.sign_inv]

theorem det_weylMat (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    (weylMat (ε := ε) h c w).det = 1 := by
  have hbar : h.bar c = -c := by
    have := (h.mem_traceZero).mp hc
    rw [UnitaryFieldData.trace] at this
    linear_combination this
  have hpair : ∀ i, weylCoeff (ε := ε) h c w (.inl i) *
      weylCoeff (ε := ε) h c w (.inr (.inr i)) =
      if i ∈ negSet w then -1 else 1 := by
    intro i
    rcases hwi : w (.inl i) with j | j
    · simp [weylCoeff, hwi, mem_negSet]
    · simp only [weylCoeff, hwi, mem_negSet, Sum.elim_inr, Sum.isRight_inr, ↓reduceIte, hbar,
        inv_neg]
      field_simp
  rw [weylMat, det_signedPerm, sign_weylPerm, sign_of_mem_hypWeyl hw, Fintype.prod_sum_type,
    Fintype.prod_sum_type]
  simp only [show ∀ k : Fin ε, weylCoeff h c w (.inr (.inl k) : HypIndex r ε) = 1 from
    fun _ => rfl, Finset.prod_const_one, one_mul]
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => hpair i, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_const, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem weylMat_mem (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    ((weylMat (ε := ε) h c w).map h.bar)ᵀ * hypGram r ε K * weylMat h c w = hypGram r ε K ∧
      (weylMat (ε := ε) h c w).det = 1 :=
  ⟨weylMat_isometry h hc0 hw, det_weylMat h hc hc0 hw⟩

@[expose] noncomputable def weylElt (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) : hypSU h r ε :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (weylMat h c w)
      (by rw [det_weylMat h hc hc0 hw]; exact one_ne_zero),
    weylMat_mem h hc hc0 hw⟩

theorem coe_weylElt (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r) :
    (((weylElt (ε := ε) h hc hc0 hw : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = weylMat h c w :=
  rfl

theorem exists_mem_traceZero_ne_zero' (h : UnitaryFieldData p f K) :
    ∃ c ∈ h.traceZero, c ≠ 0 :=
  h.exists_mem_traceZero_ne_zero

end CFSG.ClassicalGroups.UnitaryFlag

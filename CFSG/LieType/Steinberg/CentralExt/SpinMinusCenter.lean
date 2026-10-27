module

public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.LieType.Steinberg.CentralExt.SpinTorus
public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

variable {n : ℕ} {K : Type} [Field K] {b c : K}

variable (n K b c) in
noncomputable abbrev scalarSpinM : Subgroup (spinGroup (quadMinus n K b c)) :=
  (StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).comap (spinMatrix (quadMinus n K b c))

theorem exists_sign_of_mem {x : spinGroup (quadMinus n K b c)} (hx : x ∈ scalarSpinM n K b c) :
    ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ v, spinAction _ x v = e • v := by
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨e, he⟩ := mem_scalars.mp hx
  refine ⟨e, ?_, he⟩
  have h := map_spinAction (quadMinus n K b c) x (planeVec n planeOne)
  rw [he, QuadraticMap.map_smul, quadMinus_planeOne, smul_eq_mul, mul_one] at h
  exact mul_self_eq_one_iff.1 h

theorem mem_of_spinAction_eq_smul {x : spinGroup (quadMinus n K b c)} {e : K}
    (hx : ∀ v, spinAction _ x v = e • v) : x ∈ scalarSpinM n K b c := by
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix]
  exact mem_scalars.mpr ⟨e, hx⟩

theorem mem_ker_of_forall_eq {x : spinGroup (quadMinus n K b c)}
    (hx : ∀ v, spinAction _ x v = v) : x ∈ (spinMatrix (quadMinus n K b c)).ker := by
  rw [ker_spinMatrix, MonoidHom.mem_ker]
  exact LinearEquiv.ext fun v => hx v

theorem quadMinus_ne_zero' : quadMinus n K b c ≠ 0 := fun h => by
  have h1 := DFunLike.congr_fun h (planeVec n planeOne)
  rw [quadMinus_planeOne, zero_apply] at h1
  exact one_ne_zero h1

variable (n K b c) in
noncomputable abbrev negOneM : spinGroup (quadMinus n K b c) :=
  spinGroup.negOne (quadMinus n K b c) quadMinus_ne_zero'

theorem negOneM_mem_scalarSpinM : negOneM n K b c ∈ scalarSpinM n K b c :=
  mem_of_spinAction_eq_smul (e := 1) fun v => by
    rw [one_smul, spinAction_apply_eq_iff', spinGroup.coe_negOne, neg_one_mul, mul_neg_one]

theorem negOneM_mul_self : negOneM n K b c * negOneM n K b c = 1 :=
  spinGroup.negOne_mul_self _ _

theorem negOneM_ne_one (h2 : (2 : K) ≠ 0) : negOneM n K b c ≠ 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  exact spinGroup.negOne_ne_one _ _

theorem commute_negOneM (x : spinGroup (quadMinus n K b c)) : Commute (negOneM n K b c) x := by
  refine Subtype.ext ?_
  change (negOneM n K b c : CliffordAlgebra (quadMinus n K b c)) * x = x * negOneM n K b c
  rw [spinGroup.coe_negOne, neg_one_mul, mul_neg_one]

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem eq_one_or_eq_negOneM_of_mem_ker [Finite K] {x : spinGroup (quadMinus n K b c)}
    (hx : x ∈ (spinMatrix (quadMinus n K b c)).ker) : x = 1 ∨ x = negOneM n K b c := by
  rcases (mem_ker_spinMatrix_quadMinus_iff hirr x).1 hx with h | h
  · exact Or.inl h
  · exact Or.inr ((eq_negOne_iff _ quadMinus_ne_zero' x).2 h)

theorem ne_of_actsNeg (h2 : (2 : K) ≠ 0) {z y : spinGroup (quadMinus n K b c)}
    (hz : ∀ v, spinAction _ z v = -v) (hy : y ∈ (spinMatrix (quadMinus n K b c)).ker) : z ≠ y := by
  rintro rfl
  rw [ker_spinMatrix, MonoidHom.mem_ker] at hy
  have h := hz (planeVec n planeOne)
  rw [hy] at h
  have h' : planeVec n (planeOne : Fin 2 → K) = -planeVec n planeOne := h
  rw [eq_neg_iff_add_eq_zero, ← two_smul K] at h'
  have h0 := (smul_eq_zero.1 h').resolve_left h2
  have h1 := quadMinus_planeOne (K := K) n b c
  rw [h0, QuadraticMap.map_zero] at h1
  exact zero_ne_one h1

include hirr in
theorem coe_scalarSpinM_eq_of_actsNeg [Finite K] {z : spinGroup (quadMinus n K b c)}
    (hz : ∀ v, spinAction _ z v = -v) :
    ((scalarSpinM n K b c : Subgroup _) : Set (spinGroup (quadMinus n K b c))) =
      {1, negOneM n K b c, z, negOneM n K b c * z} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := exists_sign_of_mem hx
    rcases he with rfl | rfl
    · rcases eq_one_or_eq_negOneM_of_mem_ker hirr
        (mem_ker_of_forall_eq fun v => by rw [hxe, one_smul]) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hzinv : ∀ v, spinAction _ z⁻¹ v = -v := fun v => by
        have h := hz (-v)
        rw [neg_neg] at h
        conv_lhs => rw [← h]
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      rcases eq_one_or_eq_negOneM_of_mem_ker hirr (x := x * z⁻¹) (mem_ker_of_forall_eq fun v => by
        rw [map_mul, LinearEquiv.mul_apply, hzinv, map_neg, hxe, neg_one_smul, neg_neg]) with
        h | h
      · exact Or.inr (Or.inr (Or.inl (mul_inv_eq_one.1 h)))
      · exact Or.inr (Or.inr (Or.inr (mul_inv_eq_iff_eq_mul.1 h)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact negOneM_mem_scalarSpinM
    · exact mem_of_spinAction_eq_smul (e := -1) fun v => by rw [hz, neg_one_smul]
    · exact Subgroup.mul_mem _ negOneM_mem_scalarSpinM
        (mem_of_spinAction_eq_smul (e := -1) fun v => by rw [hz, neg_one_smul])

include hirr in
theorem card_scalarSpinM_of_actsNeg [Finite K] (h2 : (2 : K) ≠ 0)
    {z : spinGroup (quadMinus n K b c)} (hz : ∀ v, spinAction _ z v = -v) :
    Nat.card (scalarSpinM n K b c) = 4 := by
  have hNz : ∀ v, spinAction _ (negOneM n K b c * z) v = -v := fun v => by
    have hN : ∀ w, spinAction _ (negOneM n K b c) w = w := fun w => by
      rw [spinAction_apply_eq_iff', spinGroup.coe_negOne, neg_one_mul, mul_neg_one]
    rw [map_mul, LinearEquiv.mul_apply, hz, hN]
  have hN1 := negOneM_ne_one (n := n) (b := b) (c := c) h2
  have hker1 : (1 : spinGroup (quadMinus n K b c)) ∈ (spinMatrix (quadMinus n K b c)).ker :=
    one_mem _
  have hkerN : negOneM n K b c ∈ (spinMatrix (quadMinus n K b c)).ker :=
    mem_ker_of_forall_eq fun v => by
      rw [spinAction_apply_eq_iff', spinGroup.coe_negOne, neg_one_mul, mul_neg_one]
  have h1 : Nat.card (scalarSpinM n K b c) =
      ((scalarSpinM n K b c : Subgroup _) : Set (spinGroup (quadMinus n K b c))).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, coe_scalarSpinM_eq_of_actsNeg hirr hz]
  have hz1 := ne_of_actsNeg h2 hz hker1
  have hzN := ne_of_actsNeg h2 hz hkerN
  have hNz1 := ne_of_actsNeg h2 hNz hker1
  have hNzN := ne_of_actsNeg h2 hNz hkerN
  have hzNz : z ≠ negOneM n K b c * z := fun h => hN1 (by
    have := congrArg (· * z⁻¹) h
    simpa using this.symm)
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hN1.symm, hz1.symm, hNz1.symm⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hzN.symm, hNzN.symm⟩),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hzNz), Set.ncard_singleton]

include hirr in
theorem card_scalarSpinM_of_not [Finite K] (h2 : (2 : K) ≠ 0)
    (hno : ∀ z : spinGroup (quadMinus n K b c), ¬∀ v, spinAction _ z v = -v) :
    Nat.card (scalarSpinM n K b c) = 2 := by
  have hset : ((scalarSpinM n K b c : Subgroup _) : Set (spinGroup (quadMinus n K b c))) =
      {1, negOneM n K b c} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨e, he, hxe⟩ := exists_sign_of_mem hx
      rcases he with rfl | rfl
      · exact eq_one_or_eq_negOneM_of_mem_ker hirr
          (mem_ker_of_forall_eq fun v => by rw [hxe, one_smul])
      · exact absurd (fun v => by rw [hxe, neg_one_smul]) (hno x)
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact negOneM_mem_scalarSpinM
  have h1 : Nat.card (scalarSpinM n K b c) =
      ((scalarSpinM n K b c : Subgroup _) : Set (spinGroup (quadMinus n K b c))).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_pair (negOneM_ne_one h2).symm]

include hirr in
theorem scalarSpinM_eq_bot_of_two_eq_zero [Finite K] (h2 : (2 : K) = 0) :
    scalarSpinM n K b c = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := exists_sign_of_mem hx
  have he1 : e = 1 := by
    rcases he with he | he
    · exact he
    · rw [he]
      linear_combination -h2
  rcases eq_one_or_eq_negOneM_of_mem_ker hirr
    (mem_ker_of_forall_eq fun v => by rw [hxe, he1, one_smul]) with h | h
  · exact h
  · rw [h]
    apply Subtype.ext
    rw [spinGroup.coe_negOne, Submonoid.coe_one, neg_one_eq_one_of_two_eq_zero _ h2]

open CFSG.ClassicalInvolution in
include hirr in
theorem isSquare_of_actsNeg [Finite K] (h2 : (2 : K) ≠ 0) (hn : 4 ≤ n)
    {z : spinGroup (quadMinus n K b c)} (hz : ∀ v, spinAction _ z v = -v) :
    IsSquare ((-1 : K) ^ (n - 1) * (4 * c - b ^ 2)) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hP : (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth
      (minusPair K b c ⟨1, by omega⟩) := minusPair_orth (by simp [Fin.ext_iff])
  have hmem : spinAction _ z ∈ elementaryGroup (quadMinus n K b c) :=
    range_spinAction_le_elementaryGroup hQ hP ⟨z, rfl⟩
  have hneg : spinAction _ z = LinearEquiv.neg K := LinearEquiv.ext fun v => hz v
  rw [hneg] at hmem
  exact (neg_mem_elementaryGroup_quadMinus_iff h2 hirr hn).1 hmem

section Pairs

variable (n b c) in
@[expose] noncomputable def pairTorusM (l : ℕ) : spinGroup (quadMinus n K b c) :=
  if h : 2 * l + 1 < n - 1 then
    (minusFrame n b c).longTorus (i := ⟨2 * l, by omega⟩) (j := ⟨2 * l + 1, h⟩)
      (Fin.ne_of_val_ne (by simp)) true true (-1)
  else 1

variable (n b c) in
@[expose] noncomputable def pairProdM : ℕ → spinGroup (quadMinus n K b c)
  | 0 => 1
  | m + 1 => pairProdM m * pairTorusM n b c m

theorem actsBy_pairTorusM {l : ℕ} (h : 2 * l + 1 < n - 1) :
    SpinPlusClosed.ActsBy (minusFrame n b c).toHypFrame (pairTorusM (K := K) n b c l)
      (fun p => if p.val = 2 * l ∨ p.val = 2 * l + 1 then -1 else 1) := by
  rw [pairTorusM, dite_eq_left h]
  refine (SpinPlusClosed.actsBy_longTorus_neg_one _ _).congr (funext fun p => ?_)
  simp only [Fin.ext_iff]

theorem actsBy_pairProdM {m : ℕ} (hm : 2 * m ≤ n - 1) :
    SpinPlusClosed.ActsBy (minusFrame n b c).toHypFrame (pairProdM (K := K) n b c m)
      (fun p => if p.val < 2 * m then -1 else 1) := by
  induction m with
  | zero =>
    refine SpinPlusClosed.actsBy_one.congr (funext fun p => ?_)
    rw [ite_eq_right (by omega)]
  | succ m ih =>
    refine ((ih (by omega)).mul (actsBy_pairTorusM (by omega))).congr (funext fun p => ?_)
    simp only [Pi.mul_apply]
    by_cases h1 : p.val < 2 * m
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega), mul_one]
    · rw [ite_eq_right h1, one_mul]
      by_cases h2 : p.val = 2 * m ∨ p.val = 2 * m + 1
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem pairTorusM_mul_self (l : ℕ) :
    pairTorusM (K := K) n b c l * pairTorusM n b c l = 1 := by
  unfold pairTorusM
  split_ifs
  · rw [← map_mul, neg_one_mul, neg_neg, map_one]
  · rw [mul_one]

theorem commute_pairProdM_pairTorusM (m l : ℕ) :
    Commute (pairProdM (K := K) n b c m) (pairTorusM n b c l) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih =>
    refine ih.mul_left ?_
    unfold pairTorusM
    split_ifs <;> first
      | exact HypFrame.commute_longTorus_longTorus _ _ _ _ _ _ _ _ _
      | exact Commute.one_left _
      | exact Commute.one_right _

theorem pairProdM_mul_self (m : ℕ) : pairProdM (K := K) n b c m * pairProdM n b c m = 1 := by
  induction m with
  | zero => rw [pairProdM, mul_one]
  | succ m ih =>
    rw [pairProdM, mul_assoc, ← mul_assoc (pairTorusM n b c m),
      ← (commute_pairProdM_pairTorusM m m).eq, mul_assoc, pairTorusM_mul_self, mul_one, ih]

theorem spinAction_pairProdM_planeVec (m : ℕ) (w : Fin 2 → K) :
    spinAction _ (pairProdM (K := K) n b c m) (planeVec n w) = planeVec n w := by
  induction m with
  | zero => rw [pairProdM, map_one]; rfl
  | succ m ih =>
    rw [pairProdM, map_mul, LinearEquiv.mul_apply]
    unfold pairTorusM
    split_ifs
    · rw [spinAction_longTorus_planeVec n, ih]
    · rw [map_one]
      exact ih

end Pairs

section Plane

variable (b) in
@[expose] noncomputable def planePerp : Fin 2 → K := ![-(b / 2), 1]

theorem four_ne_zero' (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  rw [show (4 : K) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

theorem polarPlane_planeOne_smul_planePerp (h2 : (2 : K) ≠ 0) (t : K) :
    polarPlane b c planeOne (t • planePerp b) = 0 := by
  simp only [polarPlane, planeOne, planePerp, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

theorem planeNorm_smul_planePerp (h2 : (2 : K) ≠ 0) (t : K) :
    planeNorm b c (t • planePerp b) = t ^ 2 * ((4 * c - b ^ 2) / 4) := by
  have h4 := four_ne_zero' h2
  simp only [planeNorm, planePerp, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp
  ring

theorem eq_planeOne_add_planePerp (h2 : (2 : K) ≠ 0) {t : K} (ht : t ≠ 0) (p : Fin 2 → K) :
    p = (p 0 + p 1 * (b / 2)) • planeOne + (p 1 / t) • (t • planePerp b) := by
  funext k
  fin_cases k
  · simp [planeOne, planePerp]
    field_simp
    ring
  · simp [planeOne, planePerp]
    field_simp

variable (n) in
@[expose] noncomputable def planeW (r : K) : CliffordAlgebra (quadMinus n K b c) :=
  ι _ (planeVec n planeOne) * ι _ (planeVec n ((2 / r) • planePerp b))

variable {r : K} (h2 : (2 : K) ≠ 0) (hr : 4 * c - b ^ 2 = r * r) (hr0 : r ≠ 0)

include h2 hr hr0 in
theorem quadMinus_u₂ : quadMinus n K b c (planeVec n ((2 / r) • planePerp b)) = 1 := by
  have h4 := four_ne_zero' h2
  rw [quadMinus_planeVec' n, planeNorm_smul_planePerp h2, hr]
  field_simp
  ring

include h2 in
theorem polar_u₁_u₂ :
    polar (quadMinus n K b c) (planeVec n planeOne) (planeVec n ((2 / r) • planePerp b)) = 0 := by
  rw [polar_planeVec_planeVec n, polarPlane_planeOne_smul_planePerp h2]

include h2 hr hr0 in
theorem planeW_mem : planeW n (b := b) (c := c) r ∈ spinGroup (quadMinus n K b c) :=
  ι_mul_ι_mem_spinGroup _ (by rw [quadMinus_planeOne, quadMinus_u₂ h2 hr hr0, one_mul])

include h2 hr hr0 in
theorem planeW_mul_self : planeW n (b := b) (c := c) r * planeW n r = -1 := by
  set x := ι (quadMinus n K b c) (planeVec n planeOne)
  set y := ι (quadMinus n K b c) (planeVec n ((2 / r) • planePerp b))
  have hyx : y * x = -(x * y) := by
    rw [ι_mul_ι_comm, polar_comm, polar_u₁_u₂ h2, map_zero, zero_sub]
  have hxx : x * x = 1 := by rw [ι_sq_scalar, quadMinus_planeOne, map_one]
  have hyy : y * y = 1 := by rw [ι_sq_scalar, quadMinus_u₂ h2 hr hr0, map_one]
  calc planeW n r * planeW n r = x * (y * x) * y := by simp only [planeW, mul_assoc]; rfl
    _ = -1 := by rw [hyx, mul_neg, neg_mul, ← mul_assoc, hxx, one_mul, hyy]

theorem commute_planeW_ι_minusVec (m : Fin (n - 1)) (s : Bool) :
    Commute (planeW n (b := b) (c := c) r) (ι _ (minusVec n m s)) := by
  have h1 : ι (quadMinus n K b c) (minusVec n m s) * ι _ (planeVec n planeOne) =
      -(ι _ (planeVec n planeOne) * ι _ (minusVec n m s)) := by
    rw [ι_mul_ι_comm, polar_minusVec_planeVec, map_zero, zero_sub]
  have h3 : ι (quadMinus n K b c) (minusVec n m s) * ι _ (planeVec n ((2 / r) • planePerp b)) =
      -(ι _ (planeVec n ((2 / r) • planePerp b)) * ι _ (minusVec n m s)) := by
    rw [ι_mul_ι_comm, polar_minusVec_planeVec, map_zero, zero_sub]
  change planeW n r * _ = _ * planeW n r
  simp only [planeW]
  rw [mul_assoc, ← neg_neg (ι _ (planeVec n ((2 / r) • planePerp b)) * ι _ (minusVec n m s)),
    ← h3, mul_neg, ← mul_assoc, ← neg_mul, ← h1, mul_assoc]

include h2 hr hr0 in
theorem planeW_mul_ι_planeVec (p : Fin 2 → K) :
    planeW n (b := b) (c := c) r * ι _ (planeVec n p) = -(ι _ (planeVec n p) * planeW n r) := by
  have ht : (2 / r : K) ≠ 0 := div_ne_zero h2 hr0
  set x := ι (quadMinus n K b c) (planeVec n planeOne)
  set y := ι (quadMinus n K b c) (planeVec n ((2 / r) • planePerp b))
  have hyx : y * x = -(x * y) := by
    rw [ι_mul_ι_comm, polar_comm, polar_u₁_u₂ h2, map_zero, zero_sub]
  have hxx : x * x = 1 := by rw [ι_sq_scalar, quadMinus_planeOne, map_one]
  have hyy : y * y = 1 := by rw [ι_sq_scalar, quadMinus_u₂ h2 hr hr0, map_one]
  have hx : planeW n r * x = -(x * planeW n r) :=
    calc planeW n r * x = x * (y * x) := by simp only [planeW, x, y, mul_assoc]
      _ = -(x * (x * y)) := by rw [hyx, mul_neg]
      _ = -(x * planeW n r) := rfl
  have hy : planeW n r * y = -(y * planeW n r) :=
    calc planeW n r * y = x * (y * y) := by simp only [planeW, x, y, mul_assoc]
      _ = -(y * (x * y)) := by
        rw [hyy, mul_one, ← mul_assoc, hyx, neg_mul, neg_neg, mul_assoc, hyy, mul_one]
      _ = -(y * planeW n r) := rfl
  rw [eq_planeOne_add_planePerp h2 ht p, planeVec_add, planeVec_smul, planeVec_smul, map_add,
    map_smul, map_smul, mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, hx, hy, smul_neg, smul_neg, neg_add]

end Plane

theorem commute_longTorus_planeW (r : K) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (τ : Kˣ) :
    Commute (((minusFrame n b c).longTorus hij s t τ : spinGroup (quadMinus n K b c)) :
      CliffordAlgebra (quadMinus n K b c)) (planeW n r) := by
  have hnum : ∀ (m : Fin (n - 1)) (u : Bool),
      Commute ((minusFrame n b c).toHypFrame.numOp m u) (planeW n (b := b) (c := c) r) :=
    fun m u => ((commute_planeW_ι_minusVec m u).symm).mul_left
      (commute_planeW_ι_minusVec m (!u)).symm
  rw [HypFrame.coe_longTorus]
  refine SL2Pair.commute_toFun_diagSL2 _ ?_ ?_ τ
  · rw [HypFrame.longPair_X_mul_Y]
    exact (hnum _ _).mul_left (hnum _ _)
  · rw [HypFrame.longPair_Y_mul_X]
    exact (hnum _ _).mul_left (hnum _ _)

theorem commute_pairProdM_planeW (r : K) (m : ℕ) :
    Commute ((pairProdM (K := K) n b c m : spinGroup (quadMinus n K b c)) :
      CliffordAlgebra (quadMinus n K b c)) (planeW n r) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih =>
    rw [pairProdM, Submonoid.coe_mul]
    refine ih.mul_left ?_
    unfold pairTorusM
    split_ifs
    · exact commute_longTorus_planeW r _ _ _ _
    · exact Commute.one_left _

include hirr in
theorem card_scalarSpinM_of_isSquare [Finite K] (h2 : (2 : K) ≠ 0)
    (hS : IsSquare ((-1 : K) ^ (n - 1) * (4 * c - b ^ 2))) :
    Nat.card (scalarSpinM n K b c) = 4 ∧ IsCyclic (scalarSpinM n K b c) := by
  have hν : ¬IsSquare (b ^ 2 - 4 * c) := by
    rintro ⟨r, hr⟩
    apply hirr ((r - b) / 2)
    field_simp
    linear_combination -hr
  have heven : Even (n - 1) := by
    by_contra hodd
    obtain ⟨r, hr⟩ := hS
    rw [(Nat.not_even_iff_odd.1 hodd).neg_one_pow] at hr
    exact hν ⟨r, by linear_combination hr⟩
  obtain ⟨r, hr⟩ := hS
  rw [heven.neg_one_pow, one_mul] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hν ⟨0, by linear_combination -hr⟩
  set y := pairProdM (K := K) n b c ((n - 1) / 2)
  set w : spinGroup (quadMinus n K b c) := ⟨planeW n r, planeW_mem h2 hr hr0⟩
  have hyF : ∀ (m : Fin (n - 1)) (u : Bool),
      spinAction _ y (minusVec n m u) = -minusVec n m u := fun m u => by
    have h := actsBy_pairProdM (K := K) (b := b) (c := c) (m := (n - 1) / 2) (by omega) m u
    simp only [minusFrame_vec] at h
    rw [ite_eq_left (by obtain ⟨k, hk⟩ := heven; have := m.isLt; omega), neg_one_smul] at h
    exact h
  have hwF : ∀ (m : Fin (n - 1)) (u : Bool),
      spinAction _ w (minusVec n m u) = minusVec n m u := fun m u =>
    (spinAction_apply_eq_iff' _ w _ _).2 (commute_planeW_ι_minusVec m u).eq
  have hwP : ∀ p : Fin 2 → K, spinAction _ w (planeVec n p) = -planeVec n p := fun p =>
    (spinAction_apply_eq_iff' _ w _ _).2 (by
      change planeW n r * _ = _ * planeW n r
      rw [planeW_mul_ι_planeVec h2 hr hr0, map_neg, neg_mul])
  have hbasis : ∀ a, spinAction _ (y * w) (Pi.single a 1) = -Pi.single a 1 := by
    intro a
    rcases a with i | i | t
    · rw [show (Pi.single (Sum.inl i) 1 : Vm n K) = minusVec n i true from
        (minusVec_eq_single n i true).symm, map_mul, LinearEquiv.mul_apply, hwF, hyF]
    · rw [show (Pi.single (Sum.inr (Sum.inl i)) 1 : Vm n K) = minusVec n i false from
        (minusVec_eq_single n i false).symm, map_mul, LinearEquiv.mul_apply, hwF, hyF]
    · have hp : (Pi.single (Sum.inr (Sum.inr t)) 1 : Vm n K) = planeVec n (Pi.single t 1) := by
        funext v
        rcases v with j | j | u <;> simp [planeVec, Pi.single_apply]
      rw [hp, map_mul, LinearEquiv.mul_apply, hwP, map_neg, spinAction_pairProdM_planeVec]
  have hz : ∀ v, spinAction _ (y * w) v = -v := by
    have hlin : ((spinAction _ (y * w) : Vm n K ≃ₗ[K] Vm n K) : Vm n K →ₗ[K] Vm n K) =
        -LinearMap.id := (Pi.basisFun K _).ext fun a => by
      rw [Pi.basisFun_apply, LinearEquiv.coe_coe, hbasis, LinearMap.neg_apply, LinearMap.id_apply]
    intro v
    exact LinearMap.congr_fun hlin v
  have hcard := card_scalarSpinM_of_actsNeg hirr h2 hz
  refine ⟨hcard, ?_⟩
  have hzz : (y * w) * (y * w) = negOneM n K b c := by
    apply Subtype.ext
    have hyy : (y : CliffordAlgebra (quadMinus n K b c)) * y = 1 := by
      rw [← Submonoid.coe_mul, pairProdM_mul_self, Submonoid.coe_one]
    have hc := commute_pairProdM_planeW (n := n) (K := K) (b := b) (c := c) r ((n - 1) / 2)
    rw [Submonoid.coe_mul, Submonoid.coe_mul, spinGroup.coe_negOne]
    change (y : CliffordAlgebra (quadMinus n K b c)) * planeW n (b := b) (c := c) r *
      ((y : CliffordAlgebra (quadMinus n K b c)) * planeW n (b := b) (c := c) r) = -1
    rw [mul_assoc, ← mul_assoc (planeW n r), ← hc.eq, mul_assoc, ← mul_assoc, hyy, one_mul,
      planeW_mul_self h2 hr hr0]
  have hzmem : y * w ∈ scalarSpinM n K b c := mem_of_spinAction_eq_smul (e := -1) fun v => by
    rw [hz, neg_one_smul]
  set z : scalarSpinM n K b c := ⟨y * w, hzmem⟩
  have hz2 : (z : spinGroup (quadMinus n K b c)) ^ 2 = negOneM n K b c := by
    rw [pow_two]
    exact hzz
  have hz2' : z ^ 2 ≠ 1 := fun h => negOneM_ne_one h2 (by
    have := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one, hz2] at this
    exact this)
  have hz4 : z ^ 4 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz2,
      pow_two, negOneM_mul_self]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf z = 4 := orderOf_eq_prime_pow (n := 1) (p := 2) (by simpa using hz2')
    (by simpa using hz4)
  have : Finite (scalarSpinM n K b c) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact isCyclic_of_orderOf_eq_card z (hord.trans hcard.symm)

open CFSG.ClassicalInvolution in
include hirr in
theorem card_scalarSpinM [Finite K] (hn : 4 ≤ n) {p f : ℕ} (hK : Nat.card K = p ^ f) :
    Nat.card (scalarSpinM n K b c) = Nat.gcd 4 ((p ^ f) ^ n + 1) ∧
      IsCyclic (scalarSpinM n K b c) := by
  by_cases h2 : (2 : K) = 0
  · have hbot := scalarSpinM_eq_bot_of_two_eq_zero hirr (n := n) h2
    have hev : Even (p ^ f) := by
      rw [← hK]
      exact SpinTorus.two_eq_zero_iff_even_card.1 h2
    have hgcd : Nat.gcd 4 ((p ^ f) ^ n + 1) = 1 := by
      have hodd : Odd ((p ^ f) ^ n + 1) := (hev.pow_of_ne_zero (by omega)).add_one
      have hm : ((p ^ f) ^ n + 1) % 4 = 1 ∨ ((p ^ f) ^ n + 1) % 4 = 3 := by
        have := Nat.odd_iff.1 hodd
        omega
      rw [Nat.gcd_rec]
      rcases hm with h | h <;> rw [h] <;> norm_num
    rw [hbot, hgcd]
    exact ⟨Subgroup.card_bot, isCyclic_of_subsingleton⟩
  have hodd : Odd (p ^ f) := by
    rw [← hK]
    exact Nat.not_even_iff_odd.1 fun h => h2 (SpinTorus.two_eq_zero_iff_even_card.2 h)
  have hν : ¬IsSquare (b ^ 2 - 4 * c) := by
    rintro ⟨r, hr⟩
    apply hirr ((r - b) / 2)
    field_simp
    linear_combination -hr
  have hsq : IsSquare ((-1 : K) ^ (n - 1) * (4 * c - b ^ 2)) ↔ (p ^ f) ^ n % 4 = 3 := by
    have h1 : (-1 : K) ^ (n - 1) * (4 * c - b ^ 2) = (-1) ^ n * (b ^ 2 - 4 * c) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    rw [h1, isSquare_mul_iff_of_not_isSquare hν (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)),
      isSquare_neg_one_pow_iff hK hodd]
    rcases odd_pow_mod_four hodd n with h | h <;> simp [h]
  rcases odd_pow_mod_four hodd n with hmod | hmod
  · have hc := card_scalarSpinM_of_not hirr h2 fun z hz =>
      absurd (hsq.1 (isSquare_of_actsNeg hirr h2 hn hz)) (by omega)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨by rw [hc, gcd_four_of_mod_two (by omega)], isCyclic_of_prime_card hc⟩
  · obtain ⟨hc, hcyc⟩ := card_scalarSpinM_of_isSquare hirr h2 (hsq.2 hmod)
    exact ⟨by rw [hc, gcd_four_of_mod_zero (by omega)], hcyc⟩

end CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed

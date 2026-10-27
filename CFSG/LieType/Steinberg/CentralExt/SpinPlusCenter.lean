module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range

public section

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

section PlaneUnit

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

@[expose] noncomputable def planeUnit (k : Fin n) : CliffordAlgebra Q :=
  ι Q (F.vec k true) * ι Q (F.vec k false) - ι Q (F.vec k false) * ι Q (F.vec k true)

theorem planeUnit_mul_self (k : Fin n) : planeUnit F k * planeUnit F k = 1 := by
  set E := ι Q (F.vec k true)
  set G := ι Q (F.vec k false)
  have hEE : E * E = 0 := F.ι_vec_mul_ι_vec_self k true
  have hGG : G * G = 0 := F.ι_vec_mul_ι_vec_self k false
  have hEGE : E * (G * E) = E := F.ι_vec_mul_ι_vec_not_mul_ι_vec k true
  have hGEG : G * (E * G) = G := F.ι_vec_mul_ι_vec_not_mul_ι_vec k false
  have hsum : E * G + G * E = 1 := F.ι_vec_mul_ι_vec_not_add k true
  calc planeUnit F k * planeUnit F k =
        E * (G * E) * G - E * (G * G) * E - G * (E * E) * G + G * (E * G) * E := by
        simp only [planeUnit]
        noncomm_ring
    _ = 1 := by
        rw [hEGE, hGEG, hGG, hEE, mul_zero, zero_mul, mul_zero, zero_mul, sub_zero, sub_zero, hsum]

theorem planeUnit_mul_ι_vec_self (k : Fin n) (r : Bool) :
    planeUnit F k * ι Q (F.vec k r) = -(ι Q (F.vec k r) * planeUnit F k) := by
  set E := ι Q (F.vec k true)
  set G := ι Q (F.vec k false)
  have hEE : E * E = 0 := F.ι_vec_mul_ι_vec_self k true
  have hGG : G * G = 0 := F.ι_vec_mul_ι_vec_self k false
  have hEGE : E * (G * E) = E := F.ι_vec_mul_ι_vec_not_mul_ι_vec k true
  have hGEG : G * (E * G) = G := F.ι_vec_mul_ι_vec_not_mul_ι_vec k false
  cases r
  · change planeUnit F k * G = -(G * planeUnit F k)
    have h1 : planeUnit F k * G = E * (G * G) - G * (E * G) := by
      simp only [planeUnit]
      noncomm_ring
    have h2 : G * planeUnit F k = G * (E * G) - G * G * E := by
      simp only [planeUnit]
      noncomm_ring
    rw [h1, h2, hGEG, hGG, mul_zero, zero_mul, zero_sub, sub_zero]
  · change planeUnit F k * E = -(E * planeUnit F k)
    have h1 : planeUnit F k * E = E * (G * E) - G * (E * E) := by
      simp only [planeUnit]
      noncomm_ring
    have h2 : E * planeUnit F k = E * E * G - E * (G * E) := by
      simp only [planeUnit]
      noncomm_ring
    rw [h1, h2, hEGE, hEE, mul_zero, zero_mul, zero_sub, sub_zero, neg_neg]

theorem planeUnit_mul_ι_vec_of_ne {k m : Fin n} (hmk : m ≠ k) (r : Bool) :
    planeUnit F k * ι Q (F.vec m r) = ι Q (F.vec m r) * planeUnit F k := by
  set E := ι Q (F.vec k true)
  set G := ι Q (F.vec k false)
  set W := ι Q (F.vec m r)
  have hEW : E * W = -(W * E) := F.ι_vec_mul_ι_vec_of_ne hmk.symm true r
  have hGW : G * W = -(W * G) := F.ι_vec_mul_ι_vec_of_ne hmk.symm false r
  have h1 : E * (G * W) = W * (E * G) := by
    rw [hGW, mul_neg, ← mul_assoc, hEW, neg_mul, neg_neg, mul_assoc]
  have h2 : G * (E * W) = W * (G * E) := by
    rw [hEW, mul_neg, ← mul_assoc, hGW, neg_mul, neg_neg, mul_assoc]
  calc planeUnit F k * W = E * (G * W) - G * (E * W) := by
        simp only [planeUnit]
        noncomm_ring
    _ = W * planeUnit F k := by
        rw [h1, h2, planeUnit, mul_sub]

theorem star_planeUnit (k : Fin n) : star (planeUnit F k) = -planeUnit F k := by
  simp only [planeUnit, star_sub, star_mul, star_ι, neg_mul_neg]
  abel

theorem exists_eq_algebraMap_mul_planeUnit [Algebra.IsCentral K (CliffordAlgebra Q)]
    (hspan : Submodule.span K (Set.range fun p : Fin n × Bool => F.vec p.1 p.2) = ⊤)
    {k : Fin n} {x : CliffordAlgebra Q}
    (hk : ∀ r, x * ι Q (F.vec k r) = -(ι Q (F.vec k r) * x))
    (hm : ∀ m, m ≠ k → ∀ r, x * ι Q (F.vec m r) = ι Q (F.vec m r) * x) :
    ∃ c : K, x = algebraMap K (CliffordAlgebra Q) c * planeUnit F k := by
  have hcomm : ∀ v, Commute (x * planeUnit F k) (ι Q v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range fun p : Fin n × Bool => F.vec p.1 p.2) :=
      hspan ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨⟨m, r⟩, rfl⟩ := hw
      change x * planeUnit F k * ι Q (F.vec m r) = ι Q (F.vec m r) * (x * planeUnit F k)
      by_cases hmk : m = k
      · subst hmk
        rw [mul_assoc, planeUnit_mul_ι_vec_self, mul_neg, ← mul_assoc, hk, neg_mul, neg_neg,
          mul_assoc]
      · rw [mul_assoc, planeUnit_mul_ι_vec_of_ne F hmk, ← mul_assoc, hm m hmk, mul_assoc]
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact ha.add_right hb
    | smul c a _ ha =>
      rw [map_smul]
      exact ha.smul_right c
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_commute hcomm
  refine ⟨c, ?_⟩
  calc x = x * planeUnit F k * planeUnit F k := by rw [mul_assoc, planeUnit_mul_self, mul_one]
    _ = _ := by rw [hc]

theorem sq_eq_neg_one_of_eq_planeUnit [Invertible (2 : K)] {g : spinGroup Q} {k : Fin n} {c : K}
    (hg : (g : CliffordAlgebra Q) = algebraMap K (CliffordAlgebra Q) c * planeUnit F k) :
    c ^ 2 = -1 := by
  have h := spinGroup.star_mul_self_of_mem g.2
  rw [hg, star_mul, star_algebraMap, star_planeUnit] at h
  have h' : -planeUnit F k * algebraMap K (CliffordAlgebra Q) c *
      (algebraMap K (CliffordAlgebra Q) c * planeUnit F k) =
      -algebraMap K (CliffordAlgebra Q) (c ^ 2) := by
    rw [neg_mul, neg_mul, ← Algebra.commutes, mul_assoc, ← mul_assoc (planeUnit F k),
      ← Algebra.commutes, mul_assoc, planeUnit_mul_self, mul_one, ← map_mul, pow_two]
  rw [h', neg_eq_iff_eq_neg, ← map_one (algebraMap K (CliffordAlgebra Q)), ← map_neg] at h
  exact algebraMap_injective Q h

end PlaneUnit

section Plus

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem span_plusFrame :
    Submodule.span K (Set.range fun p : Fin n × Bool => (plusFrame n K hn).vec p.1 p.2) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← (Pi.basisFun K (Fin n ⊕ Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  rcases j with m | m
  · exact ⟨(m, true), by simp [plusFrame]⟩
  · exact ⟨(m, false), by simp [plusFrame]⟩

theorem coe_mul_ι {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (g : spinGroup Q) (v : V) :
    (g : CliffordAlgebra Q) * ι Q v = ι Q (spinAction Q g v) * g := by
  rw [ι_spinAction, mul_assoc _ _ (g : CliffordAlgebra Q), ← Submonoid.coe_mul, inv_mul_cancel,
    Submonoid.coe_one, mul_one]

theorem exists_eq_planeUnit {g : spinGroup (quadPlus n K)} {k : Fin n}
    (hk : ∀ r, spinAction _ g ((plusFrame n K hn).vec k r) = -(plusFrame n K hn).vec k r)
    (hm : ∀ m, m ≠ k → ∀ r, spinAction _ g ((plusFrame n K hn).vec m r) = (plusFrame n K hn).vec m r) :
    ∃ c : K, (g : CliffordAlgebra (quadPlus n K)) =
      algebraMap K (CliffordAlgebra (quadPlus n K)) c * planeUnit (plusFrame n K hn) k := by
  have := isCentral_cliffordAlgebra_quadPlus K n
  refine exists_eq_algebraMap_mul_planeUnit _ (span_plusFrame hn) (fun r => ?_) fun m hmk r => ?_
  · rw [coe_mul_ι, hk, map_neg, neg_mul]
  · rw [coe_mul_ι, hm m hmk]

end Plus


section Signs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

@[expose] def ActsBy (g : spinGroup Q) (σ : Fin n → K) : Prop :=
  ∀ m r, spinAction Q g (F.vec m r) = σ m • F.vec m r

variable {F}

theorem ActsBy.mul {g h : spinGroup Q} {σ τ : Fin n → K} (hg : ActsBy F g σ) (hh : ActsBy F h τ) :
    ActsBy F (g * h) (σ * τ) := by
  intro m r
  rw [map_mul, LinearEquiv.mul_apply, hh, map_smul, hg, smul_smul, Pi.mul_apply, mul_comm]

theorem ActsBy.congr {g : spinGroup Q} {σ τ : Fin n → K} (hg : ActsBy F g σ) (h : σ = τ) :
    ActsBy F g τ :=
  h ▸ hg

theorem actsBy_one : ActsBy F 1 (fun _ => 1) := fun m r => by
  simp

variable (F)

theorem actsBy_longTorus_neg_one {i j : Fin n} (hij : i ≠ j) :
    ActsBy F (F.longTorus hij true true (-1)) (fun m => if m = i ∨ m = j then -1 else 1) := by
  intro m r
  rw [F.spinAction_longTorus_vec]
  congr 1
  by_cases hi : m = i
  · subst hi
    cases r <;> simp [longCoroot, hij]
  · by_cases hj : m = j
    · subst hj
      cases r <;> simp [longCoroot, hi]
    · simp [longCoroot, hi, hj]

theorem actsBy_longTorus_mul_longTorus {i j : Fin n} (hij : i ≠ j) {ι : Kˣ} (hι : ι ^ 2 = -1) :
    ActsBy F (F.longTorus hij true true ι * F.longTorus hij true false ι)
      (fun m => if m = i then -1 else 1) := by
  intro m r
  rw [map_mul, LinearEquiv.mul_apply, F.spinAction_longTorus_vec, map_smul,
    F.spinAction_longTorus_vec, smul_smul, ← Units.val_mul, ← zpow_add]
  congr 1
  have h2 : ((ι ^ (2 : ℤ) : Kˣ) : K) = -1 := by
    rw [zpow_two, ← pow_two, hι, Units.val_neg, Units.val_one]
  have h2' : ((ι ^ (-2 : ℤ) : Kˣ) : K) = -1 := by
    rw [zpow_neg, zpow_two, ← pow_two, hι, inv_neg, inv_one, Units.val_neg, Units.val_one]
  beta_reduce
  by_cases hi : m = i
  · rw [ite_eq_left hi, hi]
    cases r
    · have he : longCoroot i j true false i false + longCoroot i j true true i false = -2 := by
        simp [longCoroot, hij]
      rw [he]
      exact h2'
    · have he : longCoroot i j true false i true + longCoroot i j true true i true = 2 := by
        simp [longCoroot, hij]
      rw [he]
      exact h2
  · by_cases hj : m = j
    · subst hj
      cases r <;> simp [longCoroot, hi]
    · simp [longCoroot, hi, hj]

end Signs

section Pairs

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

variable (K) in
@[expose] noncomputable def pairTorus (o l : ℕ) : spinGroup (quadPlus n K) :=
  if h : o + 2 * l + 1 < n then
    (plusFrame n K hn).longTorus (i := ⟨o + 2 * l, by omega⟩) (j := ⟨o + 2 * l + 1, h⟩)
      (Fin.ne_of_val_ne (by simp)) true true (-1)
  else 1

variable (K) in
@[expose] noncomputable def pairProd (o : ℕ) : ℕ → spinGroup (quadPlus n K)
  | 0 => 1
  | m + 1 => pairProd o m * pairTorus K hn o m

theorem actsBy_pairTorus {o l : ℕ} (h : o + 2 * l + 1 < n) :
    ActsBy (plusFrame n K hn) (pairTorus K hn o l)
      (fun p => if p.val = o + 2 * l ∨ p.val = o + 2 * l + 1 then -1 else 1) := by
  rw [pairTorus, dite_eq_left h]
  refine (actsBy_longTorus_neg_one _ _).congr (funext fun p => ?_)
  simp only [Fin.ext_iff]

theorem actsBy_pairProd (o : ℕ) {m : ℕ} (hm : o + 2 * m ≤ n) :
    ActsBy (plusFrame n K hn) (pairProd K hn o m)
      (fun p => if o ≤ p.val ∧ p.val < o + 2 * m then -1 else 1) := by
  induction m with
  | zero =>
    refine actsBy_one.congr (funext fun p => ?_)
    rw [ite_eq_right (by omega)]
  | succ m ih =>
    refine ((ih (by omega)).mul (actsBy_pairTorus hn (by omega))).congr (funext fun p => ?_)
    simp only [Pi.mul_apply]
    by_cases h1 : o ≤ p.val ∧ p.val < o + 2 * m
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega), mul_one]
    · rw [ite_eq_right h1, one_mul]
      by_cases h2 : p.val = o + 2 * m ∨ p.val = o + 2 * m + 1
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem commute_pairTorus_longTorus (o l : ℕ) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    Commute (pairTorus K hn o l) ((plusFrame n K hn).longTorus hij s t τ) := by
  unfold pairTorus
  split_ifs
  · exact HypFrame.commute_longTorus_longTorus _ _ _ _ _ _ _ _ _
  · exact Commute.one_left _

theorem commute_pairProd_longTorus (o m : ℕ) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (τ : Kˣ) :
    Commute (pairProd K hn o m) ((plusFrame n K hn).longTorus hij s t τ) := by
  induction m with
  | zero => exact Commute.one_left _
  | succ m ih => exact ih.mul_left (commute_pairTorus_longTorus hn o m hij s t τ)

theorem commute_pairProd_pairTorus (o m o' l : ℕ) :
    Commute (pairProd K hn o m) (pairTorus K hn o' l) := by
  unfold pairTorus
  split_ifs
  · exact commute_pairProd_longTorus hn o m _ _ _ _
  · exact Commute.one_right _

theorem pairTorus_mul_self (o l : ℕ) : pairTorus K hn o l * pairTorus K hn o l = 1 := by
  unfold pairTorus
  split_ifs
  · rw [← map_mul, neg_one_mul, neg_neg, map_one]
  · rw [mul_one]

theorem pairProd_mul_self (o m : ℕ) : pairProd K hn o m * pairProd K hn o m = 1 := by
  induction m with
  | zero => rw [pairProd, mul_one]
  | succ m ih =>
    rw [pairProd, mul_assoc, ← mul_assoc (pairTorus K hn o m),
      ← (commute_pairProd_pairTorus hn o m o m).eq, mul_assoc, pairTorus_mul_self, mul_one, ih]

end Pairs

section Center

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

variable (n K) in
noncomputable abbrev scalarSpin : Subgroup (spinGroup (quadPlus n K)) :=
  (StatedScalars (Fin n ⊕ Fin n) K).comap (spinMatrix (quadPlus n K))

theorem quadPlus_vec_add_vec (i : Fin n) :
    quadPlus n K ((plusFrame n K hn).vec i true + (plusFrame n K hn).vec i false) = 1 := by
  have h := (plusFrame n K hn).polar_vec_not i true
  simp only [Bool.not_true] at h
  rw [QuadraticMap.map_add (⇑(quadPlus n K)), HypFrame.map_vec, HypFrame.map_vec, h, zero_add,
    zero_add]

include hn in
theorem exists_sign_of_mem {x : spinGroup (quadPlus n K)} (hx : x ∈ scalarSpin n K) :
    ∃ c : K, (c = 1 ∨ c = -1) ∧ ∀ v, spinAction _ x v = c • v := by
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hx
  obtain ⟨c, hc⟩ := mem_scalars.mp hx
  refine ⟨c, ?_, hc⟩
  have h := map_spinAction (quadPlus n K) x
    ((plusFrame n K hn).vec ⟨0, by omega⟩ true + (plusFrame n K hn).vec ⟨0, by omega⟩ false)
  rw [hc, QuadraticMap.map_smul, quadPlus_vec_add_vec, smul_eq_mul, mul_one] at h
  exact mul_self_eq_one_iff.1 h

theorem mem_of_spinAction_eq_smul {x : spinGroup (quadPlus n K)} {c : K}
    (hx : ∀ v, spinAction _ x v = c • v) : x ∈ scalarSpin n K := by
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix]
  exact mem_scalars.mpr ⟨c, hx⟩

theorem spinAction_eq_smul_of_actsBy {x : spinGroup (quadPlus n K)} {c : K}
    (hx : ActsBy (plusFrame n K hn) x fun _ => c) (v : Fin n ⊕ Fin n → K) :
    spinAction _ x v = c • v := by
  have h : ((spinAction _ x : (Fin n ⊕ Fin n → K) ≃ₗ[K] Fin n ⊕ Fin n → K) :
      (Fin n ⊕ Fin n → K) →ₗ[K] Fin n ⊕ Fin n → K) = c • LinearMap.id :=
    LinearMap.ext_on_range (span_plusFrame hn) fun p => by
      rw [LinearEquiv.coe_coe, hx p.1 p.2, LinearMap.smul_apply, LinearMap.id_apply]
  exact LinearMap.congr_fun h v

theorem mem_ker_of_forall_eq {x : spinGroup (quadPlus n K)} (hx : ∀ v, spinAction _ x v = v) :
    x ∈ (spinMatrix (quadPlus n K)).ker := by
  rw [ker_spinMatrix, MonoidHom.mem_ker]
  exact LinearEquiv.ext fun v => hx v

theorem vec_ne_zero (m : Fin n) (r : Bool) : (plusFrame n K hn).vec m r ≠ 0 := by
  intro h
  cases r
  · have := congrFun h (Sum.inr m)
    simp [plusFrame] at this
  · have := congrFun h (Sum.inl m)
    simp [plusFrame] at this

theorem ne_of_actsBy_neg (h2 : (2 : K) ≠ 0) {x y : spinGroup (quadPlus n K)}
    (hx : ActsBy (plusFrame n K hn) x fun _ => -1) (hy : y ∈ (spinMatrix (quadPlus n K)).ker) :
    x ≠ y := by
  rintro rfl
  rw [ker_spinMatrix, MonoidHom.mem_ker] at hy
  have h := hx ⟨0, by omega⟩ true
  rw [hy] at h
  have h' : (plusFrame n K hn).vec ⟨0, by omega⟩ true =
      (-1 : K) • (plusFrame n K hn).vec ⟨0, by omega⟩ true := h
  rw [neg_one_smul, eq_neg_iff_add_eq_zero, ← two_smul K] at h'
  exact vec_ne_zero hn _ _ ((smul_eq_zero.1 h').resolve_left h2)

include hn in
theorem quadPlus_ne_zero : quadPlus n K ≠ 0 := fun h => by
  have h1 := quadPlus_vec_add_vec (K := K) hn ⟨0, by omega⟩
  have h2 := DFunLike.congr_fun h
    ((plusFrame n K hn).vec ⟨0, by omega⟩ true + (plusFrame n K hn).vec ⟨0, by omega⟩ false)
  rw [zero_apply] at h2
  exact zero_ne_one (h2.symm.trans h1)

variable (K) in
include hn in
noncomputable abbrev negOneS : spinGroup (quadPlus n K) :=
  spinGroup.negOne (quadPlus n K) (quadPlus_ne_zero hn)

theorem negOne_mem_ker : negOneS K hn ∈ (spinMatrix (quadPlus n K)).ker :=
  (mem_ker_spinMatrix_quadPlus_iff _).2 (Or.inr (spinGroup.coe_negOne _ _))

theorem one_mem_ker : (1 : spinGroup (quadPlus n K)) ∈ (spinMatrix (quadPlus n K)).ker :=
  one_mem _

include hn in
theorem comap_statedScalars_quadPlus_eq_bot (h2 : (2 : K) = 0) : scalarSpin n K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨c, hc, hx⟩ := exists_sign_of_mem hn hx
  have hc1 : c = 1 := by
    rcases hc with hc | hc
    · exact hc
    · rw [hc]
      linear_combination -h2
  have hker := ker_spinMatrix_quadPlus_eq_bot (n := n) h2
  have hmem := mem_ker_of_forall_eq (x := x) fun v => by rw [hx, hc1, one_smul]
  rw [hker] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem mem_of_actsBy_neg {x : spinGroup (quadPlus n K)}
    (hx : ActsBy (plusFrame n K hn) x fun _ => -1) : x ∈ scalarSpin n K :=
  mem_of_spinAction_eq_smul (spinAction_eq_smul_of_actsBy hn hx)

theorem eq_of_mem_of_actsBy_neg {z : spinGroup (quadPlus n K)}
    (hz : ActsBy (plusFrame n K hn) z fun _ => -1) {x : spinGroup (quadPlus n K)} (hx : x ∈ scalarSpin n K) :
    x ∈ (spinMatrix (quadPlus n K)).ker ∨ x * z⁻¹ ∈ (spinMatrix (quadPlus n K)).ker := by
  obtain ⟨c, hc, hxc⟩ := exists_sign_of_mem hn hx
  rcases hc with rfl | rfl
  · exact Or.inl (mem_ker_of_forall_eq fun v => by rw [hxc, one_smul])
  · refine Or.inr (mem_ker_of_forall_eq fun v => ?_)
    have hzinv : spinAction _ z⁻¹ v = -v := by
      have h := spinAction_eq_smul_of_actsBy hn hz (-v)
      rw [neg_one_smul, neg_neg] at h
      conv_lhs => rw [← h]
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [map_mul, LinearEquiv.mul_apply, hzinv, map_neg, hxc, neg_one_smul, neg_neg]

end Center

section Structure

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem actsBy_of_mem_ker {x : spinGroup (quadPlus n K)} (hx : x ∈ (spinMatrix (quadPlus n K)).ker) :
    ActsBy (plusFrame n K hn) x fun _ => 1 := fun m r => by
  rw [ker_spinMatrix, MonoidHom.mem_ker] at hx
  rw [hx, one_smul]
  rfl

theorem eq_one_or_eq_negOneS_of_mem_ker {x : spinGroup (quadPlus n K)}
    (hx : x ∈ (spinMatrix (quadPlus n K)).ker) : x = 1 ∨ x = negOneS K hn := by
  rcases (mem_ker_spinMatrix_quadPlus_iff x).1 hx with h | h
  · exact Or.inl h
  · exact Or.inr ((eq_negOne_iff _ (quadPlus_ne_zero hn) x).2 h)

theorem negOneS_mul_self : negOneS K hn * negOneS K hn = 1 := spinGroup.negOne_mul_self _ _

theorem negOneS_ne_one (h2 : (2 : K) ≠ 0) : negOneS K hn ≠ 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  exact spinGroup.negOne_ne_one _ _

theorem commute_negOneS (x : spinGroup (quadPlus n K)) : Commute (negOneS K hn) x := by
  refine Subtype.ext ?_
  change (negOneS K hn : CliffordAlgebra (quadPlus n K)) * x = x * negOneS K hn
  rw [spinGroup.coe_negOne, neg_one_mul, mul_neg_one]

theorem coe_scalarSpin_eq_of_actsBy_neg {z : spinGroup (quadPlus n K)}
    (hz : ActsBy (plusFrame n K hn) z fun _ => -1) :
    ((scalarSpin n K : Subgroup _) : Set (spinGroup (quadPlus n K))) =
      {1, negOneS K hn, z, negOneS K hn * z} := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hx
    rcases eq_of_mem_of_actsBy_neg hn hz hx with h | h
    · rcases eq_one_or_eq_negOneS_of_mem_ker hn h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases eq_one_or_eq_negOneS_of_mem_ker hn h with h' | h'
      · exact Or.inr (Or.inr (Or.inl (mul_inv_eq_one.1 h')))
      · exact Or.inr (Or.inr (Or.inr (mul_inv_eq_iff_eq_mul.1 h')))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_of_spinAction_eq_smul (c := 1) fun v => by
        have := negOne_mem_ker hn (K := K)
        rw [ker_spinMatrix, MonoidHom.mem_ker] at this
        rw [this, one_smul]
        rfl
    · exact mem_of_actsBy_neg hn hz
    · exact mem_of_actsBy_neg hn (((actsBy_of_mem_ker hn (negOne_mem_ker hn)).mul hz).congr
        (funext fun _ => one_mul _))

theorem card_scalarSpin_of_actsBy_neg (h2 : (2 : K) ≠ 0) {z : spinGroup (quadPlus n K)}
    (hz : ActsBy (plusFrame n K hn) z fun _ => -1) : Nat.card (scalarSpin n K) = 4 := by
  have hNz : ActsBy (plusFrame n K hn) (negOneS K hn * z) fun _ => -1 :=
    ((actsBy_of_mem_ker hn (negOne_mem_ker hn)).mul hz).congr (funext fun _ => one_mul _)
  have hN1 := negOneS_ne_one hn h2
  have h1 : Nat.card (scalarSpin n K) =
      ((scalarSpin n K : Subgroup _) : Set (spinGroup (quadPlus n K))).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, coe_scalarSpin_eq_of_actsBy_neg hn hz]
  have hz1 := ne_of_actsBy_neg hn h2 hz (one_mem_ker (K := K))
  have hzN := ne_of_actsBy_neg hn h2 hz (negOne_mem_ker hn)
  have hNz1 := ne_of_actsBy_neg hn h2 hNz (one_mem_ker (K := K))
  have hNzN := ne_of_actsBy_neg hn h2 hNz (negOne_mem_ker hn)
  have hzNz : z ≠ negOneS K hn * z := fun h => hN1 (by
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

include hn in
theorem isKleinFour_scalarSpin (h2 : (2 : K) ≠ 0) (he : Even n) : IsKleinFour (scalarSpin n K) := by
  have hm : 0 + 2 * (n / 2) ≤ n := by omega
  have hz : ActsBy (plusFrame n K hn) (pairProd K hn 0 (n / 2)) fun _ => -1 :=
    (actsBy_pairProd hn 0 hm).congr (funext fun p => by
      rw [ite_eq_left ⟨Nat.zero_le _, by obtain ⟨k, hk⟩ := he; omega⟩])
  have hsq : ∀ x : scalarSpin n K, x ^ 2 = 1 := by
    rintro ⟨x, hx⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    have hx' : x ∈ ((scalarSpin n K : Subgroup _) : Set (spinGroup (quadPlus n K))) := hx
    rw [coe_scalarSpin_eq_of_actsBy_neg hn hz] at hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · rw [mul_one]
    · exact negOneS_mul_self hn
    · exact pairProd_mul_self hn 0 _
    · rw [mul_assoc, ← mul_assoc (pairProd K hn 0 (n / 2)),
        ← (commute_negOneS hn (pairProd K hn 0 (n / 2))).eq, mul_assoc, pairProd_mul_self,
        mul_one, negOneS_mul_self]
  refine ⟨card_scalarSpin_of_actsBy_neg hn h2 hz, ?_⟩
  have hN : (⟨negOneS K hn, mem_of_spinAction_eq_smul (c := 1) fun v => by
      have := negOne_mem_ker hn (K := K)
      rw [ker_spinMatrix, MonoidHom.mem_ker] at this
      rw [this, one_smul]
      rfl⟩ : scalarSpin n K) ≠ 1 := fun h => negOneS_ne_one hn h2 (congrArg Subtype.val h)
  have hord : orderOf (⟨negOneS K hn, _⟩ : scalarSpin n K) = 2 :=
    orderOf_eq_prime (hsq _) hN
  exact Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one hsq)
    (hord ▸ Monoid.order_dvd_exponent _)

end Structure

section Odd

variable {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)

theorem actsBy_pairProd_one (ho : Odd n) :
    ActsBy (plusFrame n K hn) (pairProd K hn 1 ((n - 1) / 2))
      (fun p => if p = ⟨0, by omega⟩ then 1 else -1) := by
  refine (actsBy_pairProd hn 1 (by omega)).congr (funext fun p => ?_)
  obtain ⟨k, hk⟩ := ho
  by_cases hp : p = ⟨0, by omega⟩
  · rw [ite_eq_right (by rw [hp]; simp), ite_eq_left hp]
  · have hp0 : p.val ≠ 0 := fun h => hp (Fin.ext h)
    rw [ite_eq_left (by omega), ite_eq_right hp]

theorem exists_sq_eq_neg_one_of_actsBy (h2 : (2 : K) ≠ 0) {g : spinGroup (quadPlus n K)}
    (hg : ActsBy (plusFrame n K hn) g (fun p => if p = ⟨0, by omega⟩ then -1 else 1)) :
    ∃ c : K, c ^ 2 = -1 ∧ (g : CliffordAlgebra (quadPlus n K)) =
      algebraMap K (CliffordAlgebra (quadPlus n K)) c * planeUnit (plusFrame n K hn) ⟨0, by omega⟩ := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨c, hc⟩ := exists_eq_planeUnit hn (g := g) (k := ⟨0, by omega⟩)
    (fun r => by rw [hg]; beta_reduce; rw [ite_eq_left rfl, neg_one_smul])
    (fun m hm r => by rw [hg]; beta_reduce; rw [ite_eq_right hm, one_smul])
  exact ⟨c, sq_eq_neg_one_of_eq_planeUnit _ hc, hc⟩

include hn in
theorem card_scalarSpin_of_not_isSquare (h2 : (2 : K) ≠ 0) (ho : Odd n)
    (hsq : ¬IsSquare (-1 : K)) : Nat.card (scalarSpin n K) = 2 := by
  have hset : ((scalarSpin n K : Subgroup _) : Set (spinGroup (quadPlus n K))) =
      {1, negOneS K hn} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨c, hc, hxc⟩ := exists_sign_of_mem hn hx
      rcases hc with rfl | rfl
      · exact eq_one_or_eq_negOneS_of_mem_ker hn
          (mem_ker_of_forall_eq fun v => by rw [hxc, one_smul])
      · exfalso
        have hx' : ActsBy (plusFrame n K hn) x fun _ => -1 := fun m r => hxc _
        obtain ⟨c', hc', -⟩ := exists_sq_eq_neg_one_of_actsBy hn h2
          ((hx'.mul (actsBy_pairProd_one hn ho)).congr (funext fun p => by
            simp only [Pi.mul_apply]
            split_ifs <;> norm_num))
        exact hsq ⟨c', by rw [← hc', pow_two]⟩
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact mem_of_spinAction_eq_smul (c := 1) fun v => by
          have := negOne_mem_ker hn (K := K)
          rw [ker_spinMatrix, MonoidHom.mem_ker] at this
          rw [this, one_smul]
          rfl
  have h1 : Nat.card (scalarSpin n K) =
      ((scalarSpin n K : Subgroup _) : Set (spinGroup (quadPlus n K))).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_pair (negOneS_ne_one hn h2).symm]

include hn in
theorem card_scalarSpin_of_isSquare (h2 : (2 : K) ≠ 0) (ho : Odd n) {ι : Kˣ} (hι : ι ^ 2 = -1) :
    Nat.card (scalarSpin n K) = 4 ∧ IsCyclic (scalarSpin n K) := by
  set F := plusFrame n K hn
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  set A := F.longTorus h01 true true ι * F.longTorus h01 true false ι
  set w := pairProd K hn 1 ((n - 1) / 2)
  have hA := actsBy_longTorus_mul_longTorus F h01 hι
  have hy : ActsBy F (A * w) fun _ => -1 :=
    (hA.mul (actsBy_pairProd_one hn ho)).congr (funext fun p => by
      simp only [Pi.mul_apply]
      split_ifs <;> norm_num)
  have hcard := card_scalarSpin_of_actsBy_neg hn h2 hy
  refine ⟨hcard, ?_⟩
  obtain ⟨c, hc, hAc⟩ := exists_sq_eq_neg_one_of_actsBy hn h2 hA
  have hAA : A * A = negOneS K hn := by
    refine Subtype.ext ?_
    rw [Submonoid.coe_mul, hAc, spinGroup.coe_negOne, mul_assoc, ← mul_assoc (planeUnit F _),
      ← Algebra.commutes, mul_assoc, planeUnit_mul_self, mul_one, ← map_mul, ← pow_two, hc,
      map_neg, map_one]
  have hwA : Commute w A :=
    (commute_pairProd_longTorus hn 1 _ h01 true true ι).mul_right
      (commute_pairProd_longTorus hn 1 _ h01 true false ι)
  have hyy : A * w * (A * w) = negOneS K hn := by
    calc A * w * (A * w) = A * (w * A) * w := by group
      _ = A * (A * w) * w := by rw [hwA.eq]
      _ = A * A * (w * w) := by group
      _ = negOneS K hn := by rw [hAA, pairProd_mul_self, mul_one]
  have hymem := mem_of_actsBy_neg hn hy
  set y : scalarSpin n K := ⟨A * w, hymem⟩
  have hy2' : (y : spinGroup (quadPlus n K)) ^ 2 = negOneS K hn := by
    rw [pow_two]
    exact hyy
  have hy2 : y ^ 2 ≠ 1 := fun h => negOneS_ne_one hn h2 (by
    have := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one, hy2'] at this
    exact this)
  have hy4 : y ^ 4 = 1 := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hy2',
      pow_two, negOneS_mul_self]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 4 := orderOf_eq_prime_pow (n := 1) (p := 2) (by simpa using hy2)
    (by simpa using hy4)
  have : Finite (scalarSpin n K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact isCyclic_of_orderOf_eq_card y (hord.trans hcard.symm)

end Odd

end CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

module

public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Graded

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def BlockDiag
    (M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) :
    Prop :=
  ∀ a e, a ≠ e → M a e ≠ 0 → (∃ t, a = .inr (.inr t)) ∧ ∃ t, e = .inr (.inr t)

theorem blockDiag_one : BlockDiag n (1 : Matrix _ _ K) := fun _ _ hae h =>
  absurd (Matrix.one_apply_ne hae) h

theorem BlockDiag.apply_eq_zero {M : Matrix _ _ K} (hM : BlockDiag n M)
    {a e : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2} (hae : a ≠ e)
    (h : (∀ t, a ≠ .inr (.inr t)) ∨ ∀ t, e ≠ .inr (.inr t)) : M a e = 0 := by
  by_contra h0
  obtain ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩ := hM a e hae h0
  rcases h with h | h
  · exact h t ht
  · exact h t' ht'

theorem blockDiag_mul {M N : Matrix _ _ K} (hM : BlockDiag n M) (hN : BlockDiag n N) :
    BlockDiag n (M * N) := by
  intro a e hae hne
  by_contra h
  apply hne
  rw [not_and_or] at h
  rcases h with h | h
  · push Not at h
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hN.apply_eq_zero n hae (Or.inl h), mul_zero]
    · intro x _ hx
      rw [hM.apply_eq_zero n (Ne.symm hx) (Or.inl h), zero_mul]
    · simp
  · push Not at h
    rw [Matrix.mul_apply, Finset.sum_eq_single e]
    · rw [hM.apply_eq_zero n hae (Or.inr h), zero_mul]
    · intro x _ hx
      rw [hN.apply_eq_zero n hx (Or.inr h), mul_zero]
    · simp

theorem BlockDiag.mul_apply_minusPos {M N : Matrix _ _ K} (hM : BlockDiag n M) (l : Fin (n - 1))
    (r : Bool) :
    (M * N) (minusPos n l r) (minusPos n l r) =
      M (minusPos n l r) (minusPos n l r) * N (minusPos n l r) (minusPos n l r) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (minusPos n l r)]
  · intro x _ hx
    rw [hM.apply_eq_zero n (Ne.symm hx) (Or.inl (minusPos_ne_inr_inr n l r)), zero_mul]
  · simp

theorem blockDiag_mat_of {g : spinGroup (quadMinus n K b c)}
    (hv : ∀ l r, ∃ μ : K, spinAction (quadMinus n K b c) g (minusVec n l r) = μ • minusVec n l r)
    (hA : ∀ p, ∃ q, spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n q) :
    BlockDiag n (mat n g) := by
  intro a e hae hne
  rw [mat_apply] at hne
  rcases e with l | l | t
  · obtain ⟨μ, hμ⟩ := hv l true
    rw [minusVec_eq_single] at hμ
    rw [show minusPos n l true = .inl l from rfl] at hμ
    rw [hμ, Pi.smul_apply, Pi.single_eq_of_ne hae, smul_zero] at hne
    exact absurd rfl hne
  · obtain ⟨μ, hμ⟩ := hv l false
    rw [minusVec_eq_single] at hμ
    rw [show minusPos n l false = .inr (.inl l) from rfl] at hμ
    rw [hμ, Pi.smul_apply, Pi.single_eq_of_ne hae, smul_zero] at hne
    exact absurd rfl hne
  · obtain ⟨q, hq⟩ := hA (Pi.single t 1)
    have hs : (Pi.single (.inr (.inr t)) 1 : Vm n K) = planeVec n (Pi.single t 1) := by
      funext x
      rcases x with k | k | t' <;> simp [planeVec, Pi.single_apply]
    rw [hs, hq] at hne
    refine ⟨?_, t, rfl⟩
    rcases a with k | k | t'
    · exact absurd rfl hne
    · exact absurd rfl hne
    · exact ⟨t', rfl⟩

theorem mat_minusPos_of_smul {g : spinGroup (quadMinus n K b c)} {l : Fin (n - 1)} {r : Bool}
    {μ : K} (h : spinAction (quadMinus n K b c) g (minusVec n l r) = μ • minusVec n l r) :
    mat n g (minusPos n l r) (minusPos n l r) = μ := by
  rw [mat_apply, ← minusVec_eq_single, h, minusVec_eq_single, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one]

theorem prod_ite_ite {m : ℕ} (S : Finset (Fin m)) {j j' : Fin m} (hjj' : j ≠ j') (x y : K) :
    ∏ l ∈ S, (if l = j then x else if l = j' then y else 1) =
      (if j ∈ S then x else 1) * (if j' ∈ S then y else 1) := by
  have h : ∀ l, (if l = j then x else if l = j' then y else 1) =
      (if l = j then x else 1) * (if l = j' then y else 1) := fun l => by
    by_cases hl : l = j
    · subst hl
      simp [hjj']
    · simp [hl]
  simp only [h, Finset.prod_mul_distrib, Finset.prod_ite_eq']

theorem spinAction_longTorus_eVec {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (τ : Kˣ)
    (l : Fin (n - 1)) :
    spinAction (quadMinus n K b c)
        ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ) (minusVec n l true) =
      (if l = j then (τ : K) else if l = ⟨j.val + 1, hj⟩ then ((τ⁻¹ : Kˣ) : K) else 1) •
        minusVec n l true := by
  have h := (minusFrame n b c).spinAction_longTorus_vec (succ_ne_of_lt n hj) true false τ l true
  simp only [minusFrame_vec] at h
  rw [h]
  congr 1
  by_cases h1 : l = j
  · subst h1
    simp [longCoroot, succ_ne_of_lt n hj]
  · by_cases h2 : l = ⟨j.val + 1, hj⟩
    · subst h2
      simp [longCoroot, h1]
    · simp [longCoroot, h1, h2]

theorem longTorus_diag (j : Fin (n - 1)) (hj : j.val + 1 < n - 1) (τ : Kˣ) :
    (∀ l r, ∃ μ : K, spinAction (quadMinus n K b c)
      ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ) (minusVec n l r) =
        μ • minusVec n l r) ∧
    ∀ p, spinAction (quadMinus n K b c)
      ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ) (planeVec n p) =
        planeVec n p :=
  ⟨fun l r => ⟨_, (minusFrame n b c).spinAction_longTorus_vec (succ_ne_of_lt n hj) true false τ
    l r⟩, fun p => spinAction_longTorus_planeVec n (succ_ne_of_lt n hj) true false τ p⟩

theorem shortTorusElt_diag (k : Fin (n - 1)) {a : Fin 2 → K} (ha : a ≠ 0) :
    (∀ l r, ∃ μ : K, spinAction (quadMinus n K b c) (shortTorusElt n hirr k a) (minusVec n l r) =
        μ • minusVec n l r) ∧
    ∀ p, ∃ q, spinAction (quadMinus n K b c) (shortTorusElt n hirr k a) (planeVec n p) =
      planeVec n q :=
  ⟨fun l r => ⟨_, spinAction_shortTorusElt_minusVec n hirr k ha l r⟩,
    fun p => ⟨_, spinAction_shortTorusElt_planeVec n hirr k ha p⟩⟩

theorem blockDiag_mat_of_mem_minusTorus [Finite K] (k : Fin (n - 1))
    {g : spinGroup (quadMinus n K b c)} (hg : g ∈ minusTorus n hirr k) : BlockDiag n (mat n g) := by
  by_cases hk : k.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hk] at hg
    obtain ⟨τ, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := longTorus_diag n k hk τ
    exact blockDiag_mat_of n h1 fun p => ⟨p, h2 p⟩
  · rw [minusTorus_of_not_lt n hirr hk] at hg
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr k).mp hg
    obtain ⟨h1, h2⟩ := shortTorusElt_diag n hirr k ha
    exact blockDiag_mat_of n h1 h2

theorem blockDiag_mat_of_mem_iSup [Finite K] {g : spinGroup (quadMinus n K b c)}
    {S : Set (Fin (n - 1))} (hg : g ∈ ⨆ k ∈ S, minusTorus n hirr k) : BlockDiag n (mat n g) := by
  rw [iSup_subtype'] at hg
  refine Subgroup.iSup_induction _ hg (C := fun g => BlockDiag n (mat n g))
    (fun k y hy => blockDiag_mat_of_mem_minusTorus n hirr k.1 hy) ?_ fun x y hx hy => ?_
  · rw [mat_one]
    exact blockDiag_one n
  · rw [mat_mul]
    exact blockDiag_mul n hx hy

theorem mat_eq_one_of_spinAction_eq_one {g : spinGroup (quadMinus n K b c)}
    (h : spinAction (quadMinus n K b c) g = 1) : mat n g = 1 := by
  ext a e
  rw [mat_apply, h]
  simp [Matrix.one_apply, Pi.single_apply]

theorem minusDatum_torus_inf_posPart {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (⨆ i, minusTorus n hirr i) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ ∧ 0 < ht γ},
        minusRootGroup n hirr γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  have hD : BlockDiag n (mat n x) := by
    refine Subgroup.iSup_induction _ hxt (C := fun g => BlockDiag n (mat n g))
      (fun k y hy => blockDiag_mat_of_mem_minusTorus n hirr k hy) ?_ fun y z hy hz => ?_
    · rw [mat_one]
      exact blockDiag_one n
    · rw [mat_mul]
      exact blockDiag_mul n hy hz
  have hI := idBelow_of_mem_iSup n hirr 1 _ (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hxp
  refine eq_one_of_mat_eq_one n hirr ?_ (posPart_le_fixPosTestElt n hirr hxp)
  ext a e
  by_cases hae : a = e
  · subst hae
    exact hI a a (by simp)
  · by_cases hA : (∃ t, a = .inr (.inr t)) ∧ ∃ t, e = .inr (.inr t)
    · obtain ⟨⟨t, rfl⟩, ⟨t', rfl⟩⟩ := hA
      exact hI _ _ (by simp [minusWt_inr_inr])
    · rw [Matrix.one_apply_ne hae]
      by_contra h0
      exact hA (hD a e hae h0)

theorem fieldCoord_algebraMap_mul (r : K) (t : ShortField b c) :
    fieldCoord (algebraMap K (ShortField b c) r * t) = r • fieldCoord t := by
  ext k
  fin_cases k <;> simp [fieldCoord, QuadraticAlgebra.algebraMap_eq]

theorem fieldCoord_algebraMap (r : K) :
    fieldCoord (algebraMap K (ShortField b c) r) = r • planeOne := by
  ext k
  fin_cases k <;> simp [fieldCoord, QuadraticAlgebra.algebraMap_eq, planeOne]

theorem shortWeylElt_conj_of_scalar (k : Fin (n - 1)) (g : spinGroup (quadMinus n K b c)) (r : Kˣ)
    (he : spinAction (quadMinus n K b c) g (minusVec n k true) = (r : K) • minusVec n k true)
    (hf : spinAction (quadMinus n K b c) g (minusVec n k false) =
      ((r⁻¹ : Kˣ) : K) • minusVec n k false)
    (hA : ∀ p, spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n p) (a : Fin 2 → K) :
    g * shortWeylElt n hirr k a * g⁻¹ = shortWeylElt n hirr k ((r : K) • a) := by
  have hx := fun p => conj_twShortRoot n hirr g k true he (hA p)
  have hy := fun p => conj_twShortRoot n hirr g k false hf (hA p)
  simp only [twShortRoot_true, twShortRoot_false] at hx hy
  have e : ∀ x y z : spinGroup (quadMinus n K b c),
      g * (x * y * z) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹) := fun x y z => by
    group
  rw [shortWeylElt, e, hx, hy, shortWeylElt, planeNorm_smul, smul_smul, smul_smul]
  congr 4
  have hr : (r : K) ≠ 0 := r.ne_zero
  rw [Units.val_inv_eq_inv_val]
  congr 1
  rw [pow_two, mul_inv ((r : K) * r)]
  calc (r : K)⁻¹ * (planeNorm b c a)⁻¹ = ((r : K) * r)⁻¹ * r * (planeNorm b c a)⁻¹ := by
        rw [mul_inv_rev, mul_assoc ((r : K)⁻¹) ((r : K)⁻¹) (r : K), inv_mul_cancel₀ hr, mul_one]
    _ = ((r : K) * r)⁻¹ * (planeNorm b c a)⁻¹ * r := by ring

theorem shortTorusElt_conj_of_scalar [Finite K] (k : Fin (n - 1))
    (g : spinGroup (quadMinus n K b c)) (r : Kˣ)
    (he : spinAction (quadMinus n K b c) g (minusVec n k true) = (r : K) • minusVec n k true)
    (hf : spinAction (quadMinus n K b c) g (minusVec n k false) =
      ((r⁻¹ : Kˣ) : K) • minusVec n k false)
    (hA : ∀ p, spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n p)
    {a : Fin 2 → K} (ha : a ≠ 0) :
    g * shortTorusElt n hirr k a * g⁻¹ = shortTorusElt n hirr k a := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  set R := shortRels n hirr k
  have hC : ∀ s t : ShortField b c, s ≠ 0 → t ≠ 0 → R.h (s * t) = R.h s * R.h t :=
    fun s t hs ht => R.h_mul hs ht
  obtain ⟨t, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
  have ht : t ≠ 0 := fun h => ha (by rw [h]; ext k; fin_cases k <;> rfl)
  set r' := algebraMap K (ShortField b c) (r : K)
  have hr' : r' ≠ 0 := fun h => r.ne_zero ((map_eq_zero_iff _ (algebraMap K _).injective).mp h)
  have e1 : g * shortTorusElt n hirr k (fieldCoord t) * g⁻¹ =
      shortWeylElt n hirr k (fieldCoord (r' * t)) *
        (shortWeylElt n hirr k (fieldCoord r'))⁻¹ := by
    rw [shortTorusElt, shortWeyl, fieldCoord_algebraMap_mul, fieldCoord_algebraMap,
      ← shortWeylElt_conj_of_scalar n hirr k g r he hf hA,
      ← shortWeylElt_conj_of_scalar n hirr k g r he hf hA]
    group
  have e2 : R.w (r' * t) * (R.w r')⁻¹ = R.h (r' * t) * (R.h r')⁻¹ := by
    rw [R.w_eq_h_mul (r' * t), R.w_eq_h_mul r']
    group
  rw [e1, ← shortRels_w, ← shortRels_w, e2, hC _ _ hr' ht, (R.commute_h hr' ht).eq,
    mul_inv_cancel_right, shortRels_h]

theorem spinAction_longTorus_minusVec_not {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (τ : Kˣ)
    (k : Fin (n - 1)) :
    spinAction (quadMinus n K b c)
        ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ) (minusVec n k false) =
      (((τ ^ longCoroot j ⟨j.val + 1, hj⟩ true false k true)⁻¹ : Kˣ) : K) • minusVec n k false := by
  have h := (minusFrame n b c).spinAction_longTorus_vec (succ_ne_of_lt n hj) true false τ k false
  simp only [minusFrame_vec] at h
  rw [h, ← zpow_neg, ← longCoroot_not, Bool.not_true]

theorem minusDatum_torus_commute [Finite K] (i j : Fin (n - 1)) (h : spinGroup (quadMinus n K b c))
    (hh : h ∈ minusTorus n hirr i) (h' : spinGroup (quadMinus n K b c))
    (hh' : h' ∈ minusTorus n hirr j) : Commute h h' := by
  have mixed : ∀ {a d : Fin (n - 1)} (ha : a.val + 1 < n - 1) (hd : ¬d.val + 1 < n - 1) (τ : Kˣ)
      {g : spinGroup (quadMinus n K b c)}, g ∈ minusTorus n hirr d →
      Commute ((minusFrame n b c).longTorus (succ_ne_of_lt n ha) true false τ) g := by
    intro a d ha hd τ g hg
    rw [minusTorus_of_not_lt n hirr hd] at hg
    obtain ⟨x, hx, rfl⟩ := (mem_shortTorus_iff n hirr d).mp hg
    have he := (minusFrame n b c).spinAction_longTorus_vec (succ_ne_of_lt n ha) true false τ d true
    simp only [minusFrame_vec] at he
    have key := shortTorusElt_conj_of_scalar n hirr d _ _ he
      (spinAction_longTorus_minusVec_not n ha τ d)
      (spinAction_longTorus_planeVec n (succ_ne_of_lt n ha) true false τ) hx
    exact (mul_inv_eq_iff_eq_mul.mp key)
  by_cases hi : i.val + 1 < n - 1
  · by_cases hj : j.val + 1 < n - 1
    · rw [minusTorus_of_lt n hirr hi] at hh
      rw [minusTorus_of_lt n hirr hj] at hh'
      obtain ⟨τ, rfl⟩ := hh
      obtain ⟨σ, rfl⟩ := hh'
      exact (minusFrame n b c).commute_longTorus_longTorus _ _ _ τ _ _ _ σ
    · rw [minusTorus_of_lt n hirr hi] at hh
      obtain ⟨τ, rfl⟩ := hh
      exact mixed hi hj τ hh'
  · by_cases hj : j.val + 1 < n - 1
    · rw [minusTorus_of_lt n hirr hj] at hh'
      obtain ⟨σ, rfl⟩ := hh'
      exact (mixed hj hi σ hh).symm
    · have hij : i = j := Fin.ext (by omega)
      subst hij
      rw [minusTorus_of_not_lt n hirr hi] at hh hh'
      exact shortTorus_commute n hirr i hh hh'

theorem longTorus_mem_fixPosTestElt {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (τ : Kˣ) :
    (minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ ∈ fixPosTestElt n := by
  rw [HypFrame.longTorus_apply]
  refine (Subgroup.closure_le _).mpr ?_ (mem_closure_upperSL2_lowerSL2 _ _)
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · change ((((minusFrame n b c).longSL2 (succ_ne_of_lt n hj) true false (upperSL2 x)) :
      spinGroup (quadMinus n K b c)) : CliffordAlgebra (quadMinus n K b c)) * posTestElt n =
        posTestElt n
    rw [HypFrame.longSL2_upperSL2, (minusFrame n b c).longRoot_swap]
    exact (minusFrame n b c).toHypFrame.longRoot_mul_testElt _ false true _ rfl
  · change ((((minusFrame n b c).longSL2 (succ_ne_of_lt n hj) true false (lowerSL2 x)) :
      spinGroup (quadMinus n K b c)) : CliffordAlgebra (quadMinus n K b c)) * posTestElt n =
        posTestElt n
    rw [HypFrame.longSL2_lowerSL2, Bool.not_false, Bool.not_true, (minusFrame n b c).longRoot_swap]
    exact (minusFrame n b c).toHypFrame.longRoot_mul_testElt _ false true _ rfl

theorem mat_longTorus_eVec {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (τ : Kˣ) (l : Fin (n - 1)) :
    mat n ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ) (minusPos n l true)
        (minusPos n l true) =
      if l = j then (τ : K) else if l = ⟨j.val + 1, hj⟩ then ((τ⁻¹ : Kˣ) : K) else 1 :=
  mat_minusPos_of_smul n (spinAction_longTorus_eVec n hj τ l)

@[expose] def prefixProd (k : Fin (n - 1))
    (M : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) : K :=
  ∏ l ∈ Finset.univ.filter (fun l : Fin (n - 1) => l.val ≤ k.val), M (minusPos n l true)
    (minusPos n l true)

theorem prefixProd_mul (k : Fin (n - 1)) {M N : Matrix _ _ K} (hM : BlockDiag n M) :
    prefixProd n k (M * N) = prefixProd n k M * prefixProd n k N := by
  rw [prefixProd, prefixProd, prefixProd, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => hM.mul_apply_minusPos n l true

theorem prefixProd_longTorus (k : Fin (n - 1)) {j : Fin (n - 1)} (hj : j.val + 1 < n - 1)
    (τ : Kˣ) :
    prefixProd n k (mat n ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ)) =
      (if j.val ≤ k.val then (τ : K) else 1) *
        (if j.val + 1 ≤ k.val then ((τ⁻¹ : Kˣ) : K) else 1) := by
  rw [prefixProd]
  simp only [mat_longTorus_eVec n hj τ]
  rw [prod_ite_ite _ (succ_ne_of_lt n hj)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem minusDatum_torus_iSupIndep {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : iSupIndep (minusTorus n hirr) := by
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  rw [iSup_subtype'] at hx
  by_cases hk : k.val + 1 < n - 1
  ·
    have hP : BlockDiag n (mat n x) ∧ prefixProd n k (mat n x) = 1 := by
      refine Subgroup.iSup_induction _ hx (C := fun g =>
        BlockDiag n (mat n g) ∧ prefixProd n k (mat n g) = 1) (fun j y hy => ?_) ?_
        fun y z hy hz => ?_
      · refine ⟨blockDiag_mat_of_mem_minusTorus n hirr j.1 hy, ?_⟩
        by_cases hj : j.1.val + 1 < n - 1
        · rw [minusTorus_of_lt n hirr hj] at hy
          obtain ⟨τ, rfl⟩ := hy
          rw [prefixProd_longTorus n k hj τ]
          have hjk : j.1.val ≠ k.val := fun h => j.2 (Fin.ext h)
          by_cases hlt : j.1.val < k.val
          · rw [ite_eq_left (by omega), ite_eq_left (by omega), Units.mul_inv]
          · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_one]
        · rw [minusTorus_of_not_lt n hirr hj] at hy
          obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr j.1).mp hy
          refine Finset.prod_eq_one fun l hl => ?_
          rw [mat_minusPos_of_smul n (spinAction_shortTorusElt_minusVec n hirr j.1 ha l true),
            shortTorusScalar, ite_eq_right_iff.mpr fun h => ?_]
          rw [Finset.mem_filter] at hl
          rw [h] at hl
          omega
      · rw [mat_one]
        refine ⟨blockDiag_one n, Finset.prod_eq_one fun l _ => ?_⟩
        exact Matrix.one_apply_eq _
      · rw [mat_mul]
        exact ⟨blockDiag_mul n hy.1 hz.1, by rw [prefixProd_mul n k hy.1, hy.2, hz.2, mul_one]⟩
    rw [minusTorus_of_lt n hirr hk] at hxk
    obtain ⟨σ, rfl⟩ := hxk
    have h1 := hP.2
    rw [prefixProd_longTorus n k hk σ, ite_eq_left le_rfl, ite_eq_right (by omega),
      mul_one] at h1
    rw [show σ = 1 from Units.ext h1, map_one]
  ·
    have hP : BlockDiag n (mat n x) ∧
        (∏ l, mat n x (minusPos n l true) (minusPos n l true)) = 1 ∧
        (∀ p, spinAction (quadMinus n K b c) x (planeVec n p) = planeVec n p) ∧
        x ∈ fixPosTestElt n := by
      refine Subgroup.iSup_induction _ hx (C := fun g =>
        BlockDiag n (mat n g) ∧ (∏ l, mat n g (minusPos n l true) (minusPos n l true)) = 1 ∧
          (∀ p, spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n p) ∧
          g ∈ fixPosTestElt n) (fun j y hy => ?_) ?_ fun y z hy hz => ?_
      · have hj : j.1.val + 1 < n - 1 := by
          by_contra hj
          exact j.2 (Fin.ext (by omega))
        refine ⟨blockDiag_mat_of_mem_minusTorus n hirr j.1 hy, ?_⟩
        rw [minusTorus_of_lt n hirr hj] at hy
        obtain ⟨τ, rfl⟩ := hy
        refine ⟨?_, spinAction_longTorus_planeVec n _ true false τ,
          longTorus_mem_fixPosTestElt n hj τ⟩
        simp only [mat_longTorus_eVec n hj τ]
        rw [prod_ite_ite _ (succ_ne_of_lt n hj), ite_eq_left (Finset.mem_univ _),
          ite_eq_left (Finset.mem_univ _), Units.mul_inv]
      · rw [mat_one]
        exact ⟨blockDiag_one n, Finset.prod_eq_one fun l _ => Matrix.one_apply_eq _,
          fun p => by rw [map_one, LinearEquiv.coe_one, id_eq], one_mem _⟩
      · refine ⟨by rw [mat_mul]; exact blockDiag_mul n hy.1 hz.1, ?_, fun p => ?_,
          mul_mem hy.2.2.2 hz.2.2.2⟩
        · rw [mat_mul, ← Finset.prod_congr rfl fun l _ => (hy.1.mul_apply_minusPos n l true).symm,
            Finset.prod_mul_distrib, hy.2.1, hz.2.1, mul_one]
        · rw [map_mul, LinearEquiv.mul_apply, hz.2.2.1, hy.2.2.1]
    rw [minusTorus_of_not_lt n hirr hk] at hxk
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr k).mp hxk
    obtain ⟨-, hprod, hA, hT⟩ := hP
    have hN : planeNorm b c a = 1 := by
      rw [← hprod]
      simp only [mat_minusPos_of_smul n (spinAction_shortTorusElt_minusVec n hirr k ha _ true),
        shortTorusScalar, ite_true]
      rw [Finset.prod_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ k)]
    have hact : spinAction (quadMinus n K b c) (shortTorusElt n hirr k a) = 1 := by
      have := (minusFrame n b c).toHypFrame.spinAction_eq_of_vec (g := shortTorusElt n hirr k a)
        (h := 1) (fun l r => ?_) (fun v hv => ?_) (fun v _ => by
          rw [map_one, LinearEquiv.coe_one, id_eq])
      · rwa [map_one] at this
      · simp only [minusFrame_vec]
        rw [spinAction_shortTorusElt_minusVec n hirr k ha, map_one, LinearEquiv.coe_one, id_eq,
          shortTorusScalar]
        split_ifs <;> simp [hN]
      · rw [eq_planeVec_of_polar_minusVec n b c hv, hA]
    exact eq_one_of_mat_eq_one n hirr (mat_eq_one_of_spinAction_eq_one n hact) hT

end CFSG.LieType.Universal.Spin.Twisted

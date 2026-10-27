module

public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.ClassicalGroups.Unitary


open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ} [NeZero m]

@[expose] def u0 (m : ℕ) [NeZero m] : Fin m → K := Pi.single 0 1 + Pi.single 1 1

theorem fin_zero_ne_one (hm : 2 ≤ m) : (0 : Fin m) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_one'] at h'
  rw [Nat.mod_eq_of_lt (by omega)] at h'
  omega

@[simp] theorem u0_zero (hm : 2 ≤ m) : u0 (K := K) m 0 = 1 := by
  have h01 : (0 : Fin m) ≠ 1 := fin_zero_ne_one hm
  simp [u0, Pi.single_eq_of_ne h01]

theorem u0_one (hm : 2 ≤ m) : u0 (K := K) m 1 = 1 := by
  have h10 : (1 : Fin m) ≠ 0 := (fin_zero_ne_one hm).symm
  simp [u0, Pi.single_eq_of_ne h10]

theorem u0_eq_zero_of_ne {i : Fin m} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    u0 (K := K) m i = 0 := by
  simp [u0, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1]

theorem u0_ne_zero (hm : 2 ≤ m) : u0 (K := K) m ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [u0_zero (K := K) hm] at this
  exact one_ne_zero this

@[expose] def u0Perp (σ : K ≃+* K) (m : ℕ) [NeZero m] : Submodule K (Fin m → K) :=
  LinearMap.ker (hermL σ (u0 m))

@[simp] theorem mem_u0Perp {v : Fin m → K} :
    v ∈ u0Perp σ m ↔ herm σ (u0 m) v = 0 :=
  Iff.rfl

@[expose] def u0Span (m : ℕ) [NeZero m] : Submodule K (Fin m → K) := Submodule.span K {u0 m}

theorem u0_mem_u0Span : u0 (K := K) m ∈ u0Span (K := K) m :=
  Submodule.mem_span_singleton_self _

theorem herm_u0_u0 (hm : 2 ≤ m) [CharP K 2] :
    herm σ (u0 (K := K) m) (u0 (K := K) m) = 0 := by
  have h01 : (0 : Fin m) ≠ 1 := fin_zero_ne_one hm
  simp [u0, herm_add_left, herm_add_right, herm_single_left, herm_single_right,
    Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h01.symm, CharTwo.add_self_eq_zero]

theorem u0Span_le_u0Perp (hm : 2 ≤ m) [CharP K 2] :
    u0Span (K := K) m ≤ u0Perp σ m := by
  rw [u0Span, Submodule.span_le]
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact (mem_u0Perp (σ := σ) (v := u0 (K := K) m)).mpr (herm_u0_u0 (σ := σ) hm)

@[expose] def u0SpanPerp (σ : K ≃+* K) (m : ℕ) [NeZero m] : Submodule K (u0Perp σ m) :=
  (u0Span (K := K) m).comap (u0Perp σ m).subtype

@[expose] def tailIdx (hm : 2 ≤ m) (j : Fin (m - 2)) : Fin m :=
  ⟨j.1 + 2, by have := j.2; omega⟩

theorem tailIdx_injective (hm : 2 ≤ m) : Function.Injective (tailIdx hm) := by
  intro j k h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simp [tailIdx] at h'
  omega

theorem tailIdx_ne_zero (hm : 2 ≤ m) (j : Fin (m - 2)) : tailIdx hm j ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp [tailIdx] at h'

theorem tailIdx_ne_one (hm : 2 ≤ m) (j : Fin (m - 2)) : tailIdx hm j ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h'
  simp [tailIdx] at h'

@[expose] def tailProj (hm : 2 ≤ m) : (Fin m → K) →ₗ[K] (Fin (m - 2) → K) where
  toFun v j := v (tailIdx hm j)
  map_add' x y := by
    funext j
    rfl
  map_smul' c x := by
    funext j
    rfl

@[simp] theorem tailProj_apply (hm : 2 ≤ m) (v : Fin m → K) (j : Fin (m - 2)) :
    tailProj (K := K) hm v j = v (tailIdx hm j) := rfl

@[expose] noncomputable def tailVec (hm : 2 ≤ m) (w : Fin (m - 2) → K) : Fin m → K :=
  ∑ j : Fin (m - 2), w j • Pi.single (tailIdx hm j) (1 : K)

theorem herm_sum_right {ι : Type*} (x : Fin m → K) (s : Finset ι) (f : ι → Fin m → K) :
    herm σ x (∑ i ∈ s, f i) = ∑ i ∈ s, herm σ x (f i) :=
  map_sum (hermL σ x) f s

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin m → K) (y : Fin m → K) :
    herm σ (∑ i ∈ s, f i) y = ∑ i ∈ s, herm σ (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

theorem tailVec_apply_of_ne (hm : 2 ≤ m) {w : Fin (m - 2) → K} {i : Fin m}
    (hi : ∀ j : Fin (m - 2), tailIdx hm j ≠ i) : tailVec (K := K) hm w i = 0 := by
  rw [tailVec, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  simp only [Pi.smul_apply, Pi.single_eq_of_ne (hi j).symm, smul_zero]

theorem tailProj_tailVec (hm : 2 ≤ m) (w : Fin (m - 2) → K) :
    tailProj (K := K) hm (tailVec (K := K) hm w) = w := by
  funext j
  rw [tailProj_apply, tailVec, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hne : tailIdx hm j ≠ tailIdx hm k := by
      intro h
      exact hkj (tailIdx_injective hm h.symm)
    simp [Pi.single_eq_of_ne hne]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem tailVec_mem_u0Perp [CharP K 2] (hm : 2 ≤ m) (w : Fin (m - 2) → K) :
    tailVec (K := K) hm w ∈ u0Perp σ m := by
  rw [mem_u0Perp, tailVec, herm_sum_right]
  apply Finset.sum_eq_zero
  intro j _
  rw [herm_smul_right, herm_single_right]
  have h : u0 (K := K) m (tailIdx hm j) = 0 :=
    u0_eq_zero_of_ne (tailIdx_ne_zero hm j) (tailIdx_ne_one hm j)
  rw [h, map_zero, zero_mul, mul_zero]

theorem herm_tailVec (hm : 2 ≤ m) (w w' : Fin (m - 2) → K) :
    herm σ (tailVec (K := K) hm w) (tailVec (K := K) hm w') = herm σ w w' := by
  rw [tailVec, tailVec, herm_sum_left]
  rw [herm_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm_sum_right]
  rw [Finset.sum_eq_single j]
  · simp [herm_smul_left, herm_smul_right, herm_single_left, herm_single_right]
    ring
  · intro k _ hkj
    have hne : tailIdx hm j ≠ tailIdx hm k := by
      intro h
      exact hkj (tailIdx_injective hm h.symm)
    simp [herm_smul_left, herm_smul_right, herm_single_left, herm_single_right,
      Pi.single_eq_of_ne hne.symm]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem herm_tailVec_u0 (hm : 2 ≤ m) (w : Fin (m - 2) → K) :
    herm σ (tailVec (K := K) hm w) (u0 (K := K) m) = 0 := by
  rw [u0, herm_add_right, herm_single_right, herm_single_right]
  have h0 : tailVec (K := K) hm w 0 = 0 :=
    tailVec_apply_of_ne hm (fun j => tailIdx_ne_zero hm j)
  have h1 : tailVec (K := K) hm w 1 = 0 :=
    tailVec_apply_of_ne hm (fun j => tailIdx_ne_one hm j)
  simp [h0, h1]

@[expose] def tailProjPerp (hm : 2 ≤ m) : u0Perp σ m →ₗ[K] (Fin (m - 2) → K) :=
  (tailProj (K := K) hm).comp (u0Perp σ m).subtype

theorem tailProjPerp_surjective [CharP K 2] (hm : 2 ≤ m) :
    Function.Surjective (tailProjPerp (σ := σ) hm) := by
  intro w
  exact ⟨⟨tailVec hm w, tailVec_mem_u0Perp (σ := σ) hm w⟩, tailProj_tailVec hm w⟩

theorem tailProjPerp_eq_tailProj (hm : 2 ≤ m) (x : u0Perp σ m) :
    tailProjPerp (σ := σ) hm x = tailProj (K := K) hm x.1 := rfl

theorem single_tailIdx_mem_u0Perp (hm : 2 ≤ m) (j : Fin (m - 2)) :
    Pi.single (tailIdx hm j) (1 : K) ∈ u0Perp σ m := by
  rw [mem_u0Perp, herm_single_right]
  rw [u0_eq_zero_of_ne (tailIdx_ne_zero hm j) (tailIdx_ne_one hm j), map_zero, zero_mul]

theorem u0_add_single_tailIdx_mem_u0Perp [CharP K 2] (hm : 2 ≤ m) (j : Fin (m - 2)) :
    u0 (K := K) m + Pi.single (tailIdx hm j) (1 : K) ∈ u0Perp σ m :=
  (u0Perp σ m).add_mem ((mem_u0Perp (σ := σ) (v := u0 (K := K) m)).mpr
    (herm_u0_u0 (σ := σ) hm)) (single_tailIdx_mem_u0Perp (σ := σ) hm j)

@[expose] noncomputable def u0AddSingle [CharP K 2] (hm : 2 ≤ m) (j : Fin (m - 2)) :
    u0Perp σ m :=
  ⟨u0 (K := K) m + Pi.single (tailIdx hm j) (1 : K),
    u0_add_single_tailIdx_mem_u0Perp (σ := σ) hm j⟩

@[simp] theorem u0AddSingle_val [CharP K 2] (hm : 2 ≤ m) (j : Fin (m - 2)) :
    (u0AddSingle (σ := σ) hm j).1 = u0 (K := K) m + Pi.single (tailIdx hm j) (1 : K) := rfl

theorem tailProj_u0 (hm : 2 ≤ m) :
    tailProj (K := K) hm (u0 (K := K) m) = 0 := by
  funext j
  rw [tailProj_apply, u0]
  simp [Pi.single_eq_of_ne (tailIdx_ne_zero hm j), Pi.single_eq_of_ne (tailIdx_ne_one hm j)]

theorem tailProj_single_tailIdx (hm : 2 ≤ m) (j : Fin (m - 2)) :
    tailProj (K := K) hm (Pi.single (tailIdx hm j) (1 : K)) = Pi.single j 1 := by
  funext k
  rw [tailProj_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : k = j
  · subst h
    simp
  · have hne : tailIdx hm k ≠ tailIdx hm j := fun hh => h (tailIdx_injective hm hh)
    simp [h, hne]

theorem ker_tailProjPerp [CharP K 2] (hm : 2 ≤ m) :
    LinearMap.ker (tailProjPerp (σ := σ) hm) = u0SpanPerp σ m := by
  ext x
  rw [LinearMap.mem_ker]
  change (tailProjPerp (σ := σ) hm x = 0) ↔ x.1 ∈ u0Span (K := K) m
  constructor
  · intro hx
    have hx' : tailProj (K := K) hm x.1 = 0 := hx
    have hx0 : ∀ j : Fin (m - 2), x.1 (tailIdx hm j) = 0 := by
      intro j
      have := congrFun hx' j
      simpa [tailProj_apply] using this
    have hxmem : herm σ (u0 (K := K) m) x.1 = 0 := x.2
    have hv0 : x.1 0 + x.1 1 = 0 := by
      simpa [u0, herm_add_left, herm_single_left] using hxmem
    have h10 : x.1 1 = x.1 0 := by
      have hneg : x.1 1 = -x.1 0 := by linear_combination hv0
      rw [hneg, CharTwo.neg_eq]
    have hdecomp : x.1 = x.1 0 • u0 (K := K) m := by
      funext i
      by_cases hi0 : i = 0
      · subst hi0
        simp [u0, Pi.single_eq_of_ne (fin_zero_ne_one hm)]
      by_cases hi1 : i = 1
      · subst hi1
        simp [u0, Pi.single_eq_of_ne (fin_zero_ne_one hm).symm, h10]
      · have hi2 : 2 ≤ i.1 := by
          have h0 : i.1 ≠ 0 := by intro h; exact hi0 (Fin.ext (by simpa using h))
          have h1 : i.1 ≠ 1 := by
            intro h
            apply hi1
            apply Fin.ext
            rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
            exact h
          omega
        have hvi : x.1 i = 0 := by
          let j : Fin (m - 2) := ⟨i.1 - 2, by omega⟩
          have hidx : tailIdx hm j = i := by
            apply Fin.ext
            simp [tailIdx, j]
            omega
          rw [← hidx, hx0 j]
        rw [hvi]
        simp [u0, hi0, hi1]
    exact Submodule.mem_span_singleton.mpr ⟨x.1 0, hdecomp.symm⟩
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    have hu0 : tailProj (K := K) hm (u0 (K := K) m) = 0 := by
      funext j
      rw [tailProj_apply, u0]
      simp [Pi.single_eq_of_ne (tailIdx_ne_zero hm j),
        Pi.single_eq_of_ne (tailIdx_ne_one hm j)]
    rw [tailProjPerp_eq_tailProj, ← hc, map_smul, hu0, smul_zero]

abbrev u0Quot (σ : K ≃+* K) (m : ℕ) [NeZero m] : Type _ :=
  u0Perp σ m ⧸ u0SpanPerp σ m

@[expose] noncomputable def perpQuotEquiv [CharP K 2] (hm : 3 ≤ m) :
    u0Quot σ m ≃ₗ[K] (Fin (m - 2) → K) :=
  let hm2 : 2 ≤ m := by omega
  (Submodule.quotEquivOfEq (LinearMap.ker (tailProjPerp (σ := σ) hm2))
    (u0SpanPerp σ m) (ker_tailProjPerp (σ := σ) hm2)).symm.trans
    (LinearMap.quotKerEquivOfSurjective (tailProjPerp (σ := σ) hm2)
      (tailProjPerp_surjective (σ := σ) hm2))

theorem eq_smul_u0_add_tailVec [CharP K 2] (hm : 2 ≤ m) {x : Fin m → K}
    (hx : x ∈ u0Perp σ m) :
    x = x 0 • u0 (K := K) m + tailVec (K := K) hm (tailProj (K := K) hm x) := by
  have hxmem : herm σ (u0 (K := K) m) x = 0 := hx
  have hx10 : x 1 = x 0 := by
    have hv0 : x 0 + x 1 = 0 := by
      simpa [u0, herm_add_left, herm_single_left] using hxmem
    have hneg : x 1 = -x 0 := by linear_combination hv0
    rw [hneg, CharTwo.neg_eq]
  funext i
  by_cases hi0 : i = 0
  · subst hi0
    have htail0 : tailVec (K := K) hm (tailProj (K := K) hm x) 0 = 0 :=
      tailVec_apply_of_ne hm (fun j => tailIdx_ne_zero hm j)
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, htail0, add_zero, u0_zero (K := K) hm, mul_one]
  by_cases hi1 : i = 1
  · subst hi1
    have htail1 : tailVec (K := K) hm (tailProj (K := K) hm x) 1 = 0 :=
      tailVec_apply_of_ne hm (fun j => tailIdx_ne_one hm j)
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, htail1, add_zero, u0_one (K := K) hm, mul_one]
    exact hx10
  · have hi2 : 2 ≤ i.1 := by
      have h0 : i.1 ≠ 0 := by intro h; exact hi0 (Fin.ext (by simpa using h))
      have h1 : i.1 ≠ 1 := by
        intro h
        apply hi1
        apply Fin.ext
        rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
        exact h
      omega
    have htail : tailVec (K := K) hm (tailProj (K := K) hm x) i = x i := by
      let j : Fin (m - 2) := ⟨i.1 - 2, by omega⟩
      have hidx : tailIdx hm j = i := by
        apply Fin.ext
        simp [tailIdx, j]
        omega
      have h := congrFun (tailProj_tailVec hm (tailProj (K := K) hm x)) j
      rw [tailProj_apply] at h
      rw [← hidx]
      exact h
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u0_eq_zero_of_ne hi0 hi1, mul_zero, zero_add]
    exact htail.symm

theorem herm_tailProj_of_mem_u0Perp [CharP K 2] (hm : 2 ≤ m)
    {x y : Fin m → K} (hx : x ∈ u0Perp σ m) (hy : y ∈ u0Perp σ m) :
    herm σ (tailProj (K := K) hm x) (tailProj (K := K) hm y) = herm σ x y := by
  have hx' := eq_smul_u0_add_tailVec (σ := σ) hm hx
  have hy' := eq_smul_u0_add_tailVec (σ := σ) hm hy
  conv_rhs => rw [hx', hy']
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
  have h1 : herm σ (u0 (K := K) m) (tailVec (K := K) hm (tailProj (K := K) hm y)) = 0 :=
    tailVec_mem_u0Perp (σ := σ) hm _
  have h2 : herm σ (tailVec (K := K) hm (tailProj (K := K) hm x)) (u0 (K := K) m) = 0 :=
    herm_tailVec_u0 hm _
  rw [herm_u0_u0 (σ := σ) hm, h1, h2, herm_tailVec]
  ring


@[simp] theorem perpQuotEquiv_mk [CharP K 2] (hm : 3 ≤ m) (x : u0Perp σ m) :
    perpQuotEquiv (σ := σ) hm (Submodule.Quotient.mk x) =
      tailProj (K := K) (by omega) x.1 := by
  let hm2 : 2 ≤ m := by omega
  simp only [perpQuotEquiv]
  rw [LinearEquiv.trans_apply]
  have h1 : (Submodule.quotEquivOfEq (LinearMap.ker (tailProjPerp (σ := σ) hm2))
      (u0SpanPerp σ m) (ker_tailProjPerp (σ := σ) hm2)).symm
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
    rw [← Submodule.quotEquivOfEq_mk (p := LinearMap.ker (tailProjPerp (σ := σ) hm2))
      (p' := u0SpanPerp σ m) (h := ker_tailProjPerp (σ := σ) hm2) x]
    exact LinearEquiv.symm_apply_apply _ _
  rw [h1, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact tailProjPerp_eq_tailProj hm2 x

theorem perpQuotEquiv_mk_u0_add_single [CharP K 2] (hm : 3 ≤ m) (j : Fin (m - 2))
    (x : u0Perp σ m)
    (hx : x.1 = u0 (K := K) m + Pi.single (tailIdx (by omega) j) (1 : K)) :
    perpQuotEquiv (σ := σ) hm (Submodule.Quotient.mk x) = Pi.single j 1 := by
  rw [perpQuotEquiv_mk, hx, map_add, tailProj_u0, tailProj_single_tailIdx, zero_add]

theorem perpQuotEquiv_u0AddSingle [CharP K 2] (hm : 3 ≤ m) (j : Fin (m - 2)) :
    perpQuotEquiv (σ := σ) hm
      (Submodule.Quotient.mk (u0AddSingle (σ := σ) (by omega) j)) = Pi.single j 1 := by
  rw [perpQuotEquiv_mk_u0_add_single (σ := σ) hm j _ rfl]

theorem herm_u0_add_single [CharP K 2] (hm : 3 ≤ m) (i j : Fin (m - 2)) :
    herm σ (u0 (K := K) m + Pi.single (tailIdx (by omega) i) (1 : K))
        (u0 (K := K) m + Pi.single (tailIdx (by omega) j) (1 : K)) =
      if i = j then 1 else 0 := by
  let hm2 : 2 ≤ m := by omega
  let x : Fin m → K := u0 (K := K) m + Pi.single (tailIdx hm2 i) (1 : K)
  let y : Fin m → K := u0 (K := K) m + Pi.single (tailIdx hm2 j) (1 : K)
  have hx : x ∈ u0Perp σ m := u0_add_single_tailIdx_mem_u0Perp (σ := σ) hm2 i
  have hy : y ∈ u0Perp σ m := u0_add_single_tailIdx_mem_u0Perp (σ := σ) hm2 j
  have hxy : herm σ x y = if i = j then 1 else 0 := by
    rw [← herm_tailProj_of_mem_u0Perp (σ := σ) hm2 hx hy]
    rw [show tailProj (K := K) hm2 x = Pi.single i 1 by
      rw [map_add, tailProj_u0, tailProj_single_tailIdx, zero_add]]
    rw [show tailProj (K := K) hm2 y = Pi.single j 1 by
      rw [map_add, tailProj_u0, tailProj_single_tailIdx, zero_add]]
    rw [herm_single_left, map_one, one_mul, Pi.single_apply]
  simpa [x, y] using hxy

theorem herm_perpQuotEquiv [CharP K 2] (hm : 3 ≤ m) (x y : u0Perp σ m) :
    herm σ (perpQuotEquiv (σ := σ) hm (Submodule.Quotient.mk x))
        (perpQuotEquiv (σ := σ) hm (Submodule.Quotient.mk y)) = herm σ x.1 y.1 := by
  rw [perpQuotEquiv_mk, perpQuotEquiv_mk]
  exact herm_tailProj_of_mem_u0Perp (σ := σ) (by omega) x.2 y.2

@[expose] def perp (σ : K ≃+* K) (e : Fin m → K) : Submodule K (Fin m → K) :=
  LinearMap.ker (hermL σ e)

@[simp] theorem mem_perp {e v : Fin m → K} :
    v ∈ perp σ e ↔ herm σ e v = 0 :=
  Iff.rfl

@[expose] def spanVec (e : Fin m → K) : Submodule K (Fin m → K) := Submodule.span K {e}

@[expose] def spanVecPerp (σ : K ≃+* K) (e : Fin m → K) : Submodule K (perp σ e) :=
  (spanVec e).comap (perp σ e).subtype

theorem spanVec_le_perp [CharP K 2] {e : Fin m → K} (he : herm σ e e = 0) :
    spanVec e ≤ perp σ e := by
  rw [spanVec, Submodule.span_le]
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]
  exact (mem_perp (σ := σ) (e := e) (v := e)).mpr he

@[expose] noncomputable def smulPerp (g : SUid σ m) {e : Fin m → K} (hge : g • e = u0 m) :
    perp σ e →ₗ[K] perp σ (u0 m) where
  toFun x := ⟨g • x.1, by
    rw [mem_perp, ← hge, herm_smul_smul]
    exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add g x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact smul_comm g c x.1

@[expose] noncomputable def smulPerpInv (g : SUid σ m) {e : Fin m → K} (hge : g • e = u0 m) :
    perp σ (u0 m) →ₗ[K] perp σ e where
  toFun x := ⟨g⁻¹ • x.1, by
    have he : e = g⁻¹ • u0 m := by rw [← hge, inv_smul_smul]
    rw [mem_perp, he, herm_smul_smul]
    exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add g⁻¹ x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact smul_comm g⁻¹ c x.1

@[expose] noncomputable def smulPerpEquiv (g : SUid σ m) {e : Fin m → K} (hge : g • e = u0 m) :
    perp σ e ≃ₗ[K] perp σ (u0 m) where
  toLinearMap := smulPerp g hge
  invFun := smulPerpInv g hge
  left_inv x := by
    show (smulPerpInv g hge) ((smulPerp g hge) x) = x
    apply Subtype.ext
    show g⁻¹ • (g • x.1) = x.1
    exact inv_smul_smul g x.1
  right_inv x := by
    show (smulPerp g hge) ((smulPerpInv g hge) x) = x
    apply Subtype.ext
    show g • (g⁻¹ • x.1) = x.1
    exact smul_inv_smul g x.1

theorem smulPerpEquiv_apply (g : SUid σ m) {e : Fin m → K} (hge : g • e = u0 m)
    (x : perp σ e) : (smulPerpEquiv g hge x).1 = g • x.1 := by
  change (smulPerp g hge x).1 = g • x.1
  rfl

theorem herm_smulPerpEquiv (g : SUid σ m) {e : Fin m → K} (hge : g • e = u0 m)
    (x y : perp σ e) :
    herm σ (smulPerpEquiv g hge x).1 (smulPerpEquiv g hge y).1 = herm σ x.1 y.1 := by
  rw [smulPerpEquiv_apply, smulPerpEquiv_apply]
  exact herm_smul_smul σ g x.1 y.1

@[expose] noncomputable def eTailMap [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) : perp σ e →ₗ[K] (Fin (m - 2) → K) :=
  (tailProjPerp (σ := σ) (by omega)).comp (smulPerp g hge)

theorem eTailMap_apply [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) (x : perp σ e) :
    eTailMap hm g hge x = tailProj (K := K) (by omega) (g • x.1) := by
  change tailProj (K := K) (by omega) ((smulPerp g hge x).1) =
    tailProj (K := K) (by omega) (g • x.1)
  rfl

theorem eTailMap_surjective [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) : Function.Surjective (eTailMap (σ := σ) hm g hge) := by
  intro w
  obtain ⟨y, hy⟩ := tailProjPerp_surjective (σ := σ) (by omega) w
  let y' : perp σ (u0 m) := y
  refine ⟨smulPerpInv g hge y', ?_⟩
  rw [eTailMap_apply]
  rw [← smulPerpEquiv_apply (g := g) (hge := hge) (x := smulPerpInv g hge y')]
  have hright : (smulPerpEquiv g hge) (smulPerpInv g hge y') = y' :=
    (smulPerpEquiv g hge).right_inv y'
  rw [hright]
  exact hy

theorem ker_eTailMap [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) :
    LinearMap.ker (eTailMap (σ := σ) hm g hge) = spanVecPerp σ e := by
  ext x
  rw [LinearMap.mem_ker]
  change eTailMap (σ := σ) hm g hge x = 0 ↔ x.1 ∈ spanVec e
  rw [eTailMap_apply]
  have hker : tailProj (K := K) (by omega) (g • x.1) = 0 ↔
      g • x.1 ∈ u0Span (K := K) m := by
    constructor
    · intro h
      have h' : (⟨g • x.1, (smulPerp g hge x).2⟩ : u0Perp σ m) ∈
          LinearMap.ker (tailProjPerp (σ := σ) (by omega)) := h
      rw [ker_tailProjPerp (σ := σ) (by omega)] at h'
      exact h'
    · intro h
      have h' : (⟨g • x.1, (smulPerp g hge x).2⟩ : u0Perp σ m) ∈ u0SpanPerp σ m := h
      rw [← ker_tailProjPerp (σ := σ) (by omega)] at h'
      exact h'
  rw [hker]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have he : g⁻¹ • u0 (K := K) m = e := by rw [← hge, inv_smul_smul]
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    calc
      c • e = c • (g⁻¹ • u0 m) := by rw [he]
      _ = g⁻¹ • (c • u0 m) := (smul_comm g⁻¹ c (u0 m)).symm
      _ = g⁻¹ • (g • x.1) := by rw [hc]
      _ = x.1 := inv_smul_smul g x.1
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    calc
      c • u0 m = c • (g • e) := by rw [hge]
      _ = g • (c • e) := (smul_comm g c e).symm
      _ = g • x.1 := by rw [hc]

noncomputable def eQuotEquivOfSmul [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) :
    (perp σ e ⧸ spanVecPerp σ e) ≃ₗ[K] (Fin (m - 2) → K) :=
  (Submodule.quotEquivOfEq (spanVecPerp σ e) (LinearMap.ker (eTailMap (σ := σ) hm g hge))
    (ker_eTailMap (σ := σ) hm g hge).symm).trans
    (LinearMap.quotKerEquivOfSurjective (eTailMap (σ := σ) hm g hge)
      (eTailMap_surjective (σ := σ) hm g hge))

@[simp] theorem eQuotEquivOfSmul_mk [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m)
    {e : Fin m → K} (hge : g • e = u0 m) (x : perp σ e) :
    eQuotEquivOfSmul (σ := σ) hm g hge (Submodule.Quotient.mk x) =
      tailProj (K := K) (by omega) (g • x.1) := by
  simp only [eQuotEquivOfSmul]
  rw [LinearEquiv.trans_apply]
  have h1 : (Submodule.quotEquivOfEq (spanVecPerp σ e)
      (LinearMap.ker (eTailMap (σ := σ) hm g hge))
      (ker_eTailMap (σ := σ) hm g hge).symm) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
    Submodule.quotEquivOfEq_mk (p := spanVecPerp σ e)
      (p' := LinearMap.ker (eTailMap (σ := σ) hm g hge))
      (h := (ker_eTailMap (σ := σ) hm g hge).symm) x
  rw [h1, LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact eTailMap_apply hm g hge x

theorem herm_eQuotEquivOfSmul [CharP K 2] (hm : 3 ≤ m) (g : SUid σ m) {e : Fin m → K}
    (hge : g • e = u0 m) (x y : perp σ e) :
    herm σ (eQuotEquivOfSmul (σ := σ) hm g hge (Submodule.Quotient.mk x))
        (eQuotEquivOfSmul (σ := σ) hm g hge (Submodule.Quotient.mk y)) = herm σ x.1 y.1 := by
  rw [eQuotEquivOfSmul_mk, eQuotEquivOfSmul_mk]
  rw [← smulPerpEquiv_apply (g := g) (hge := hge) (x := x),
    ← smulPerpEquiv_apply (g := g) (hge := hge) (x := y)]
  rw [herm_tailProj_of_mem_u0Perp (σ := σ) (by omega)
    (smulPerpEquiv g hge x).2 (smulPerpEquiv g hge y).2]
  exact herm_smulPerpEquiv g hge x y

theorem exists_mem_T_smul_eq_u0 [CharP K 2] (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    {e : Fin m → K} (he0 : e ≠ 0) (he : herm σ e e = 0) :
    ∃ g : SUid σ m, g ∈ T σ m ∧ g • e = u0 m :=
  exists_mem_T_smul_eq_of_iso hσ hm he0 he (u0_ne_zero (by omega)) (herm_u0_u0 (σ := σ) (by omega))

theorem exists_eQuotEquiv_isometry [CharP K 2] (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    {e : Fin m → K} (he0 : e ≠ 0) (he : herm σ e e = 0) :
    ∃ φ : (perp σ e ⧸ spanVecPerp σ e) ≃ₗ[K] (Fin (m - 2) → K),
      ∀ x y : perp σ e,
        herm σ (φ (Submodule.Quotient.mk x)) (φ (Submodule.Quotient.mk y)) =
          herm σ x.1 y.1 := by
  obtain ⟨g, -, hge⟩ := exists_mem_T_smul_eq_u0 (σ := σ) hσ hm he0 he
  exact ⟨eQuotEquivOfSmul (σ := σ) hm g hge,
    herm_eQuotEquivOfSmul (σ := σ) hm g hge⟩

theorem tv_smul_eq_self_of_herm_eq_zero (hσ : IsUnitaryInvolution σ) {e v : Fin m → K}
    (hev : herm σ e v = 0) (hv : herm σ v v = 0) {c : K} (hc : c + σ c = 0) :
    tv hσ.invol hv hc • e = e := by
  rw [tv_smul, herm_eq_zero_comm σ hσ.invol hev, mul_zero, zero_smul, add_zero]

theorem tv_mem_perp (hσ : IsUnitaryInvolution σ) {e v : Fin m → K}
    (hev : herm σ e v = 0) (hv : herm σ v v = 0) {c : K} (hc : c + σ c = 0)
    {x : Fin m → K} (hx : x ∈ perp σ e) : tv hσ.invol hv hc • x ∈ perp σ e := by
  rw [mem_perp] at hx ⊢
  rw [tv_smul, herm_add_right, herm_smul_right, hx, hev, mul_zero, add_zero]

theorem tv_induced_quot (hσ : IsUnitaryInvolution σ) {e v : Fin m → K}
    (hev : herm σ e v = 0) (hv : herm σ v v = 0) {c : K} (hc : c + σ c = 0)
    (x : perp σ e) :
    Submodule.Quotient.mk (p := spanVecPerp σ e)
        (⟨tv hσ.invol hv hc • x.1,
          tv_mem_perp hσ hev hv hc x.2⟩ : perp σ e) =
      Submodule.Quotient.mk (p := spanVecPerp σ e) x +
        (c * herm σ v x.1) •
          Submodule.Quotient.mk (p := spanVecPerp σ e)
            (⟨v, (mem_perp (σ := σ) (e := e) (v := v)).mpr hev⟩ : perp σ e) := by
  have h : (⟨tv hσ.invol hv hc • x.1,
      tv_mem_perp hσ hev hv hc x.2⟩ : perp σ e) =
      x + (c * herm σ v x.1) •
        (⟨v, (mem_perp (σ := σ) (e := e) (v := v)).mpr hev⟩ : perp σ e) := by
    apply Subtype.ext
    simp [tv_smul]
  rw [h, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]

theorem isUnitaryInvolution_unitaryInvolution_gf4 :
    IsUnitaryInvolution
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) :=
  isUnitaryInvolution_unitaryInvolution (K := GaloisField 2 2) (p := 2) (f := 1) (by
    rw [GaloisField.card 2 2 (by omega)]
    norm_num)

theorem exists_eQuotEquiv_isometry_gf4 (hm : 3 ≤ m)
    {e : Fin m → GaloisField 2 2} (he0 : e ≠ 0)
    (he : herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) e e = 0) :
    ∃ φ : (perp (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) e ⧸
        spanVecPerp (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) e) ≃ₗ[
          GaloisField 2 2] (Fin (m - 2) → GaloisField 2 2),
      ∀ x y : perp (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) e,
        herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1)
          (φ (Submodule.Quotient.mk x)) (φ (Submodule.Quotient.mk y)) =
          herm (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1) x.1 y.1 :=
  exists_eQuotEquiv_isometry
    (σ := CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 2) 2 1)
    isUnitaryInvolution_unitaryInvolution_gf4 hm he0 he

end CFSG.ClassicalGroups.Unitary

module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryCommutator

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix SymplecticTorusWeyl CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {r : ℕ} {K : Type*} [Field K]

section Block

variable {a b : Fin r ⊕ Fin r}

variable (a b) in
@[expose] def rpBlock (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  pairMat a b g * pairMat a.swap b.swap (adjugate g)ᵀ

theorem rpBlock_mul (h : coordIdx a ≠ coordIdx b) (g g' : Matrix (Fin 2) (Fin 2) K) :
    rpBlock a b (g * g') = rpBlock a b g * rpBlock a b g' := by
  have hc : Commute (pairMat a b g') (pairMat a.swap b.swap (adjugate g)ᵀ) :=
    (isSupp_pairMat _).commute (isSupp_pairMat _) (disjoint_pair_swap h)
  rw [rpBlock, rpBlock, rpBlock, pairMat_mul (ne_of_coordIdx_ne h), adjugate_mul_distrib,
    transpose_mul, pairMat_mul (swap_ne_swap_of_coordIdx_ne h)]
  simp only [mul_assoc]
  rw [← mul_assoc (pairMat a b g'), hc.eq, mul_assoc]

theorem rpBlock_upper (h : coordIdx a ≠ coordIdx b) (t : K) :
    rpBlock a b !![1, t; 0, 1] = 1 + t • rpMat K a b := by
  have hadj : (adjugate !![(1 : K), t; 0, 1])ᵀ = !![1, 0; -t, 1] := by
    rw [adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [rpBlock, hadj, pairMat_upper (ne_of_coordIdx_ne h),
    pairMat_lower (swap_ne_swap_of_coordIdx_ne h), add_mul, one_mul, mul_add, mul_one,
    single_mul_single_of_ne _ _ _ _ (swap_ne_self b).symm, add_zero, rpMat, smul_sub,
    smul_single, smul_single, smul_eq_mul, mul_one, ← single_neg]
  abel

theorem rpBlock_lower (h : coordIdx a ≠ coordIdx b) (t : K) :
    rpBlock a b !![1, 0; t, 1] = 1 + t • rpMat K b a := by
  have hadj : (adjugate !![(1 : K), 0; t, 1])ᵀ = !![1, -t; 0, 1] := by
    rw [adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [rpBlock, hadj, pairMat_lower (ne_of_coordIdx_ne h),
    pairMat_upper (swap_ne_swap_of_coordIdx_ne h), add_mul, one_mul, mul_add, mul_one,
    single_mul_single_of_ne _ _ _ _ (swap_ne_self a).symm, add_zero, rpMat, smul_sub,
    smul_single, smul_single, smul_eq_mul, mul_one, ← single_neg]
  abel

theorem rpBlock_diag (h : coordIdx a ≠ coordIdx b) (u v : K) :
    rpBlock a b !![u, 0; 0, v] = diagonal fun x =>
      (if x = a then u else if x = b then v else 1) *
        (if x = a.swap then v else if x = b.swap then u else 1) := by
  have hadj : (adjugate !![u, 0; 0, v])ᵀ = !![v, 0; 0, u] := by
    rw [adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [rpBlock, hadj, pairMat_diag (ne_of_coordIdx_ne h),
    pairMat_diag (swap_ne_swap_of_coordIdx_ne h), diagonal_mul_diagonal]

end Block

section Torus

theorem autMat_torusElt (d : Fin r → Kˣ) :
    autMat (torusElt r K d) = diagonal fun x => ((Sum.elim d d⁻¹ x : Kˣ) : K) := by
  ext x y
  rw [autMat_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, torusElt_apply,
    diagonal_apply, Pi.single_apply]
  by_cases hxy : x = y <;> simp [hxy]

theorem sumElim_zpow_eq (α : Fin r → ℤ) (c : Kˣ) (x : Fin r ⊕ Fin r) :
    Sum.elim (fun i => c ^ α i) (fun i => c ^ α i)⁻¹ x = c ^ (coordWt x ⬝ᵥ α) := by
  rcases x with i | i
  · simp [eps, single_dotProduct]
  · simp [eps, single_dotProduct, _root_.zpow_neg]

theorem rpBlock_diag_eq_autMat_torusElt {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b)
    (c : Kˣ) :
    rpBlock a b !![(c : K), 0; 0, ((c⁻¹ : Kˣ) : K)] =
      autMat (torusElt r K fun i => c ^ (coordWt a - coordWt b) i) := by
  rw [rpBlock_diag h, autMat_torusElt]
  congr 1
  funext x
  rw [sumElim_zpow_eq, dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct]
  have h1 := ne_of_coordIdx_ne h
  have h2 := ne_swap_of_coordIdx_ne h
  have h3 := ne_swap_of_coordIdx_ne (Ne.symm h)
  by_cases hxa : x = a
  · subst hxa
    simp [h1, h2, (swap_ne_self x).symm]
  by_cases hxb : x = b
  · subst hxb
    simp [Ne.symm h1, h3, (swap_ne_self x).symm]
  by_cases hxa' : x = a.swap
  · subst hxa'
    simp [hxb, swap_ne_swap_of_ne h1, swap_ne_self]
  by_cases hxb' : x = b.swap
  · subst hxb'
    simp [hxa, hxb, hxa']
  · simp [hxa, hxb, hxa', hxb']

end Torus

section RankOne

variable (r K) in
@[expose] noncomputable def rootN (α : Fin r → ℤ) (c : K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  rootElt r K α c * rootElt r K (-α) (-c⁻¹) * rootElt r K α c

variable (r K) in
@[expose] noncomputable def rootH (α : Fin r → ℤ) (c : K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  rootN r K α c * (rootN r K α 1)⁻¹

theorem rootN_mem (α : Fin r → ℤ) (c : K) :
    rootN r K α c ∈ orthElementaryGroup (quadPlus r K) :=
  mul_mem (mul_mem (rootElt_mem _ _) (rootElt_mem _ _)) (rootElt_mem _ _)

theorem rootH_mem (α : Fin r → ℤ) (c : K) :
    rootH r K α c ∈ orthElementaryGroup (quadPlus r K) :=
  mul_mem (rootN_mem α c) (inv_mem (rootN_mem α 1))

theorem rootN_one_inv (α : Fin r → ℤ) : (rootN r K α 1)⁻¹ = rootN r K α (-1) := by
  rw [rootN, rootN, _root_.mul_inv_rev, _root_.mul_inv_rev, rootElt_inv, rootElt_inv]
  simp only [inv_neg, inv_one, neg_neg, mul_assoc]

theorem exists_autMat_rootElt_eq_rpBlock {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a b : Fin r ⊕ Fin r, coordIdx a ≠ coordIdx b ∧ coordWt a - coordWt b = α ∧
      (∀ t : K, autMat (rootElt r K α t) = rpBlock a b !![1, t; 0, 1]) ∧
      ∀ t : K, autMat (rootElt r K (-α) t) = rpBlock a b !![1, 0; t, 1] := by
  obtain ⟨a, b, hab, hw, h1, h2⟩ := exists_rootElt_eq_rpElt (K := K) hα
  exact ⟨a, b, hab, hw, fun t => by rw [h1, autMat_rpElt hab, rpBlock_upper hab],
    fun t => by rw [h2, autMat_rpElt (Ne.symm hab), rpBlock_lower hab]⟩

theorem upper_mul_lower_mul_upper {c : K} (hc : c ≠ 0) :
    !![1, c; 0, 1] * !![1, 0; -c⁻¹, 1] * !![1, c; 0, 1] = !![0, c; -c⁻¹, (0 : K)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, hc]

theorem autMat_rootN {α : Fin r → ℤ} {a b : Fin r ⊕ Fin r} (hab : coordIdx a ≠ coordIdx b)
    (h1 : ∀ t : K, autMat (rootElt r K α t) = rpBlock a b !![1, t; 0, 1])
    (h2 : ∀ t : K, autMat (rootElt r K (-α) t) = rpBlock a b !![1, 0; t, 1]) {c : K}
    (hc : c ≠ 0) : autMat (rootN r K α c) = rpBlock a b !![0, c; -c⁻¹, 0] := by
  rw [rootN, map_mul, map_mul, h1, h2, ← rpBlock_mul hab, ← rpBlock_mul hab,
    upper_mul_lower_mul_upper hc]

theorem rootH_eq_torusElt {α : Fin r → ℤ} (hα : α ∈ roots r) (c : Kˣ) :
    rootH r K α c = torusElt r K fun i => c ^ α i := by
  obtain ⟨a, b, hab, rfl, h1, h2⟩ := exists_autMat_rootElt_eq_rpBlock (K := K) hα
  apply autMat_injective
  rw [rootH, rootN_one_inv, map_mul, autMat_rootN hab h1 h2 c.ne_zero,
    autMat_rootN hab h1 h2 (neg_ne_zero.mpr one_ne_zero), ← rpBlock_mul hab,
    ← rpBlock_diag_eq_autMat_torusElt hab c]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem rootN_one_sq_eq_torusElt {α : Fin r → ℤ} (hα : α ∈ roots r) :
    rootN r K α 1 ^ 2 = torusElt r K fun i => (-1 : Kˣ) ^ α i := by
  obtain ⟨a, b, hab, rfl, h1, h2⟩ := exists_autMat_rootElt_eq_rpBlock (K := K) hα
  apply autMat_injective
  rw [pow_two, map_mul, autMat_rootN hab h1 h2 one_ne_zero, ← rpBlock_mul hab,
    ← rpBlock_diag_eq_autMat_torusElt hab (-1)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

theorem sl2_rank_one_factorization {t : K} (ht : t ≠ 0) :
    !![0, 1; -1, (0 : K)] * !![1, t; 0, 1] =
      !![1, -t⁻¹; 0, 1] * !![-t⁻¹, 0; 0, (-t⁻¹)⁻¹] * !![1, 0; t⁻¹, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, ht]

theorem rootN_one_mul_rootElt {α : Fin r → ℤ} (hα : α ∈ roots r) {t : K} (ht : t ≠ 0) :
    rootN r K α 1 * rootElt r K α t =
      rootElt r K α (-t⁻¹) * rootH r K α (-t⁻¹) * rootElt r K (-α) t⁻¹ := by
  have hu : (-t⁻¹ : K) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht)
  have hH := rootH_eq_torusElt (K := K) hα (Units.mk0 _ hu)
  obtain ⟨a, b, hab, rfl, h1, h2⟩ := exists_autMat_rootElt_eq_rpBlock (K := K) hα
  rw [Units.val_mk0] at hH
  apply autMat_injective
  rw [map_mul, map_mul, map_mul, hH, autMat_rootN hab h1 h2 one_ne_zero, h1, h1, h2,
    ← rpBlock_diag_eq_autMat_torusElt hab, ← rpBlock_mul hab, ← rpBlock_mul hab,
    ← rpBlock_mul hab, Units.val_inv_eq_inv_val, Units.val_mk0, inv_one]
  exact congrArg _ (sl2_rank_one_factorization ht)

end RankOne


theorem orthogonal_geometry_split_root_rank_one_factorization {K : Type*} [Field K] {r : ℕ}
    {α : Fin r → ℤ} (hα : α ∈ roots r) :
    (∀ c : K, c ≠ 0 → rootH r K α c ∈ torus r K) ∧ rootN r K α 1 ^ 2 ∈ torus r K ∧
      (∀ t : K, t ≠ 0 → rootN r K α 1 * rootElt r K α t =
        rootElt r K α (-t⁻¹) * rootH r K α (-t⁻¹) * rootElt r K (-α) t⁻¹) ∧
      ∀ i : Fin r, weylElt r K i = rootN r K (simpleRoot r i) 1 := by
  refine ⟨fun c hc => ⟨rootH_mem α c, fun i => Units.mk0 c hc ^ α i, ?_⟩,
    ⟨pow_mem (rootN_mem α 1) 2, fun i => (-1 : Kˣ) ^ α i, ?_⟩,
    fun t ht => rootN_one_mul_rootElt hα ht, fun i => ?_⟩
  · have := rootH_eq_torusElt (K := K) hα (Units.mk0 c hc)
    rw [Units.val_mk0] at this
    exact this.symm
  · exact (rootN_one_sq_eq_torusElt hα).symm
  · rw [weylElt, rootN, inv_one]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

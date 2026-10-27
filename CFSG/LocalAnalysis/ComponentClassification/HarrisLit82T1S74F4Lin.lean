module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F2Lin

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {K : Type} [Field K]

noncomputable abbrev gTwo (K : Type) [Field K] :
    (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K) :=
  eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)

theorem eichOne_apply (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) x =
      x + polar (quadOdd 3 K) x (oddVec 3 K 1 true) • oddVec 3 K 0 true -
        polar (quadOdd 3 K) x (oddVec 3 K 0 true) • oddVec 3 K 1 true := by
  rw [eichler_apply (quadOdd_oddVec 3 K 1 true) (by rw [polar_quadOdd_oddVec]; simp),
    quadOdd_oddVec, zero_mul, add_zero]

theorem eichTwo_apply_vec {i : Fin 3} (hi : i ≠ 2) (s : Bool) :
    eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) (oddVec 3 K i s) = oddVec 3 K i s := by
  refine eichler_apply_of_polar_eq_zero ?_ (polar_quadOdd_oddVec_oddZ 3 K i s)
  rw [polar_quadOdd_oddVec, ite_eq_right_iff]
  exact fun h => absurd h.1 hi

theorem gTwo_mem_orthogonalGroup :
    gTwo K ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  mul_mem (eichler_mem_orthogonalGroup _ _ _) (eichler_mem_orthogonalGroup _ _ _)

theorem gTwo_apply (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    gTwo K x = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) x +
      polar (quadOdd 3 K) x (oddVec 3 K 1 true) • oddVec 3 K 0 true -
        polar (quadOdd 3 K) x (oddVec 3 K 0 true) • oddVec 3 K 1 true := by
  rw [LinearEquiv.mul_apply, eichOne_apply, map_sub, map_add, map_smul, map_smul,
    eichTwo_apply_vec (i := 0) (by decide) true, eichTwo_apply_vec (i := 1) (by decide) true]

theorem polar_gTwo_apply_vec (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) {i : Fin 3} (hi : i ≠ 2) :
    polar (quadOdd 3 K) (gTwo K x) (oddVec 3 K i true) =
      polar (quadOdd 3 K) x (oddVec 3 K i true) := by
  have hb : ∀ j : Fin 3, polar (quadOdd 3 K) (oddVec 3 K i true) (oddVec 3 K j true) = 0 :=
    fun j => by rw [polar_quadOdd_oddVec]; simp
  have hfix : gTwo K (oddVec 3 K i true) = oddVec 3 K i true := by
    rw [LinearEquiv.mul_apply, eichler_apply_of_polar_eq_zero (hb 1) (hb 0),
      eichTwo_apply_vec hi true]
  rw [← hfix, polar_map_of_mem gTwo_mem_orthogonalGroup, hfix]

theorem gTwo_sq_sub (x : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    gTwo K (gTwo K x) - (2 : K) • gTwo K x + x =
      (-2 * polar (quadOdd 3 K) x (oddVec 3 K 2 true)) • oddVec 3 K 2 true := by
  rw [gTwo_apply (gTwo K x), polar_gTwo_apply_vec x (by decide : (1 : Fin 3) ≠ 2),
    polar_gTwo_apply_vec x (by decide : (0 : Fin 3) ≠ 2), gTwo_apply x, map_sub, map_add,
    map_smul, map_smul, eichTwo_apply_vec (i := 0) (by decide) true,
    eichTwo_apply_vec (i := 1) (by decide) true, ← eichlerThree_sq_sub x]
  module

variable {h : (Fin 3 ⊕ Fin 3 ⊕ Unit → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 ⊕ Unit → K)}

theorem apply_eTwo_of_commute_gTwo (h2 : (2 : K) ≠ 0) (hc : h * gTwo K = gTwo K * h) :
    h (oddVec 3 K 2 true) =
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) • oddVec 3 K 2 true := by
  have hE : ∀ v, h (gTwo K v) = gTwo K (h v) := fun v => LinearEquiv.congr_fun hc v
  have h1 := gTwo_sq_sub (K := K) (oddVec 3 K 2 false)
  have h3 := gTwo_sq_sub (K := K) (h (oddVec 3 K 2 false))
  rw [polar_fTwo_eTwo, mul_one] at h1
  have h4 := congrArg h h1
  simp only [map_add, map_sub, map_smul, hE] at h4
  rw [h3] at h4
  have h5 : (-2 : K) • h (oddVec 3 K 2 true) = (-2 : K) •
      (polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) • oddVec 3 K 2 true) := by
    rw [smul_smul, ← h4]
  exact smul_right_injective _ (neg_ne_zero.mpr h2) h5

theorem lam_of_commute_gTwo (h2 : (2 : K) ≠ 0) (hO : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v)
    (hc : h * gTwo K = gTwo K * h) :
    polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) *
      polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) = 1 := by
  have h1 := polar_apply_of_map hO (oddVec 3 K 2 true) (oddVec 3 K 2 false)
  rw [apply_eTwo_of_commute_gTwo h2 hc, polar_smul_left, polar_eTwo_fTwo,
    polar_comm (quadOdd 3 K) (oddVec 3 K 2 true) (h (oddVec 3 K 2 false)), smul_eq_mul] at h1
  exact h1

theorem exists_conj_eichTwo (h2 : (2 : K) ≠ 0) (hO : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v)
    (hc : h * gTwo K = gTwo K * h) :
    ∃ a b : K, h * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * h⁻¹ =
      eichler (quadOdd 3 K) (oddVec 3 K 2 true)
        (oddZ 3 K + a • oddVec 3 K 0 true + b • oddVec 3 K 1 true) := by
  obtain ⟨ε, hε⟩ : ∃ ε, polar (quadOdd 3 K) (h (oddVec 3 K 2 false)) (oddVec 3 K 2 true) = ε :=
    ⟨_, rfl⟩
  have he := apply_eTwo_of_commute_gTwo h2 hc
  have hl := lam_of_commute_gTwo h2 hO hc
  rw [hε] at he hl
  have hgz : gTwo K (oddZ 3 K) = oddZ 3 K - (2 : K) • oddVec 3 K 2 true := by
    rw [gTwo_apply, eichlerThree_apply, polar_z_eTwo, polar_z_z, polar_comm,
      polar_quadOdd_oddVec_oddZ, polar_comm, polar_quadOdd_oddVec_oddZ]
    module
  have hv : h (gTwo K (oddZ 3 K)) = gTwo K (h (oddZ 3 K)) := LinearEquiv.congr_fun hc (oddZ 3 K)
  rw [hgz, map_sub, map_smul, he, gTwo_apply, eichlerThree_apply] at hv
  simp only [polar_vecT, polar_vecZ] at hv
  obtain ⟨u, hu⟩ : ∃ u, h (oddZ 3 K) = u := ⟨_, rfl⟩
  rw [hu] at hv
  have z2 : u (.inr (.inl 2)) = 0 := by
    have := congrFun hv (.inr (.inr ()))
    simp [oddZ] at this
    exact this
  have z1 : u (.inr (.inl 1)) = 0 := by
    have := congrFun hv (.inl 0)
    simp [oddZ] at this
    exact this
  have z0 : u (.inr (.inl 0)) = 0 := by
    have := congrFun hv (.inl 1)
    simp [oddZ] at this
    linear_combination this
  have zz : u (.inr (.inr ())) = ε := by
    have c3 := congrFun hv (.inl 2)
    simp [oddZ] at c3
    have h2' : (2 : K) * (u (.inr (.inr ())) - ε) = 0 := by
      linear_combination -c3 - z2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2').resolve_left h2)
  refine ⟨ε * u (.inl 0), ε * u (.inl 1), ?_⟩
  have hw : ε • u = oddZ 3 K + (ε * u (.inl 0)) • oddVec 3 K 0 true +
      (ε * u (.inl 1)) • oddVec 3 K 1 true + (ε * u (.inl 2)) • oddVec 3 K 2 true := by
    funext σ
    rcases σ with i | i | ⟨⟩
    · fin_cases i <;> simp [oddZ]
    · fin_cases i <;> simp [oddZ, z0, z1, z2]
    · simp [oddZ, zz, hl]
  rw [eichler_conj (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hO), he,
    eichler_smul_left, hu, hw, eichler_add_smul_self (quadOdd_oddVec 3 K 2 true)]

theorem apply_planeL_of_commute_eichOne (hO : ∀ v, quadOdd 3 K (h v) = quadOdd 3 K v)
    (hc : h * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
      eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * h) :
    h (oddVec 3 K 0 true) =
        polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 1 true) • oddVec 3 K 0 true -
          polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 0 true) • oddVec 3 K 1 true ∧
      h (oddVec 3 K 1 true) =
        -polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 1 true) • oddVec 3 K 0 true +
          polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 0 true) • oddVec 3 K 1 true ∧
      polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 1 true) *
          polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 0 true) -
        polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 0 true) *
          polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 1 true) = 1 := by
  have hb : ∀ (i j : Fin 3) (s t : Bool), polar (quadOdd 3 K) (oddVec 3 K i s) (oddVec 3 K j t) =
      if i = j ∧ s = !t then 1 else 0 := polar_quadOdd_oddVec 3 K
  have b11 : polar (quadOdd 3 K) (oddVec 3 K 1 false) (oddVec 3 K 1 true) = 1 := by
    rw [hb]; simp
  have b10 : polar (quadOdd 3 K) (oddVec 3 K 1 false) (oddVec 3 K 0 true) = 0 := by
    rw [hb]; simp
  have b01 : polar (quadOdd 3 K) (oddVec 3 K 0 false) (oddVec 3 K 1 true) = 0 := by
    rw [hb]; simp
  have b00 : polar (quadOdd 3 K) (oddVec 3 K 0 false) (oddVec 3 K 0 true) = 1 := by
    rw [hb]; simp
  have k1 : h (eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)
      (oddVec 3 K 1 false)) = eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)
      (h (oddVec 3 K 1 false)) := LinearEquiv.congr_fun hc (oddVec 3 K 1 false)
  have k0 : h (eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)
      (oddVec 3 K 0 false)) = eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)
      (h (oddVec 3 K 0 false)) := LinearEquiv.congr_fun hc (oddVec 3 K 0 false)
  rw [eichOne_apply, eichOne_apply, map_sub, map_add, map_smul, map_smul, b11, b10, one_smul,
    zero_smul, sub_zero] at k1
  rw [eichOne_apply, eichOne_apply, map_sub, map_add, map_smul, map_smul, b01, b00, one_smul,
    zero_smul, add_zero] at k0
  have he0 : h (oddVec 3 K 0 true) =
      polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 1 true) • oddVec 3 K 0 true -
        polar (quadOdd 3 K) (h (oddVec 3 K 1 false)) (oddVec 3 K 0 true) • oddVec 3 K 1 true := by
    linear_combination (norm := module) k1
  have he1 : h (oddVec 3 K 1 true) =
      -polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 1 true) • oddVec 3 K 0 true +
        polar (quadOdd 3 K) (h (oddVec 3 K 0 false)) (oddVec 3 K 0 true) • oddVec 3 K 1 true := by
    linear_combination (norm := module) -k0
  refine ⟨he0, he1, ?_⟩
  have hd := polar_apply_of_map hO (oddVec 3 K 0 true) (oddVec 3 K 0 false)
  rw [he0, polar_sub_left, polar_smul_left, polar_smul_left,
    polar_comm (quadOdd 3 K) (oddVec 3 K 0 true) (h (oddVec 3 K 0 false)),
    polar_comm (quadOdd 3 K) (oddVec 3 K 1 true) (h (oddVec 3 K 0 false)),
    polar_comm (quadOdd 3 K) (oddVec 3 K 0 true) (oddVec 3 K 0 false), b00, smul_eq_mul,
    smul_eq_mul] at hd
  linear_combination hd

end CFSG.ComponentClassification.HarrisLit.T1.S74

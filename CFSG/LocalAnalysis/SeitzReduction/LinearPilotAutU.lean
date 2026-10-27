module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutUBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Pointwise

variable {n : ℕ} {K : Type*} [Field K]

section Basic

theorem proj_transvection_mem_projUnitriangular {i j : Fin n} (hij : i < j) (c : K) :
    proj n K (Matrix.SpecialLinearGroup.transvection hij.ne c) ∈ projUnitriangular n K :=
  Subgroup.mem_map_of_mem _ (transvection_mem_unitriangular hij c)

theorem single_apply_self_eq_zero {i j : Fin n} (hij : i ≠ j) (c : K) (k : Fin n) :
    single i j c k k = 0 :=
  single_apply_of_ne _ _ _ _ _ fun h => hij (h.1.trans h.2.symm)

theorem ne_zero_of_eq_scalar_add_single (hn : 2 ≤ n) (A : GL (Fin n) K) {a b : K}
    (h : (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) a + single (firstIdx hn) (lastIdx hn) b) :
    a ≠ 0 := by
  rintro rfl
  have hv : (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (firstIdx hn) 1 = 0 := by
    rw [h]
    funext k
    simp only [map_zero, zero_add, mulVec_single_one, col_apply, Pi.zero_apply]
    exact single_apply_of_ne _ _ _ _ _ fun h' => firstIdx_ne_lastIdx hn h'.2.symm
  have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero A) hv)
    (firstIdx hn)
  rw [Pi.single_eq_same, Pi.zero_apply] at this
  exact one_ne_zero this

theorem single_mul_single_self_eq_zero {i j : Fin n} (hij : i ≠ j) (c d : K) :
    single i j c * single i j d = 0 :=
  single_mul_single_of_ne _ _ _ _ hij.symm _

end Basic

section Standard

theorem conjAut_mem_range_conj_of_commute (hn : 2 ≤ n) (A : GL (Fin n) K)
    (h : ∀ i j : Fin n, i < j → Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K)) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hA := eq_scalar_add_single_of_commute hn h
  set i₀ := firstIdx hn with hi₀
  set l := lastIdx hn with hl
  have hi₀l : i₀ ≠ l := firstIdx_ne_lastIdx hn
  set a := (A : Matrix (Fin n) (Fin n) K) i₀ i₀ with ha
  set b := (A : Matrix (Fin n) (Fin n) K) i₀ l with hb
  have ha0 : a ≠ 0 := ne_zero_of_eq_scalar_add_single hn A hA
  set T := Matrix.SpecialLinearGroup.transvection hi₀l (b / a) with hT
  have hAT : A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0) *
      Matrix.SpecialLinearGroup.toGL T := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      hT, Matrix.SpecialLinearGroup.transvection_coe, Units.val_mk0, scalar_apply,
      ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_one_eq_diagonal,
      ← scalar_apply, smul_single, smul_eq_mul, mul_div_cancel₀ _ ha0]
    exact hA
  refine ⟨proj n K T, ?_⟩
  rw [hAT, map_mul, conjAut_scalar, one_mul, conjAut_toGL]

theorem mem_range_conj_of_fix_projUnitriangular [Finite K] (hn : 3 ≤ n)
    (β : MulAut (projectiveSL n K)) (hβ : ∀ u ∈ projUnitriangular n K, β u = u) :
    β ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation hn).2 β
  have hfix : ∀ {i j : Fin n} (hij : i < j) (c : K),
      (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε)
          (proj n K (Matrix.SpecialLinearGroup.transvection hij.ne c)) =
        proj n K (Matrix.SpecialLinearGroup.transvection hij.ne c) :=
    fun hij c => hβ _ (proj_transvection_mem_projUnitriangular hij c)
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · simp only [pow_zero, mul_one] at hfix ⊢
    have hcomm : ∀ i j : Fin n, i < j →
        Commute (single i j (1 : K)) (A : Matrix (Fin n) (Fin n) K) := by
      intro i j hij
      have h1 := single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hij.ne 1 1 (hfix hij 1)
      rw [map_one] at h1
      exact h1
    have hσ : σ = 1 := by
      ext c
      have hn2 : 2 ≤ n := by omega
      set i₀ := firstIdx hn2
      set l := lastIdx hn2
      have hlt : i₀ < l := firstIdx_lt_lastIdx hn2
      have h1 := single_mul_eq_of_conjAut_mul_fieldAut_apply A σ hlt.ne c c (hfix hlt c)
      have h2 : single i₀ l c * (A : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * single i₀ l c := by
        have hc : single i₀ l c = c • single i₀ l (1 : K) := by
          rw [smul_single, smul_eq_mul, mul_one]
        rw [hc, Matrix.smul_mul, Matrix.mul_smul, (hcomm _ _ hlt).eq]
      rw [h2] at h1
      have h3 := congrArg (fun M => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M) h1
      simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h3
      have h4 := congrFun (congrFun h3 i₀) l
      rw [single_apply_same, single_apply_same] at h4
      rw [RingAut.one_apply]
      exact h4.symm
    subst hσ
    rw [map_one, mul_one]
    exact conjAut_mem_range_conj_of_commute (by omega) A hcomm
  · exfalso
    rw [pow_one] at hfix
    refine false_of_single_mul_eq_neg_mul_single hn A fun j hj => ?_
    have hlt : (⟨0, by omega⟩ : Fin n) < j := by
      rw [Fin.lt_def]
      rcases hj with hj | hj <;> simp [hj]
    rw [single_mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_apply A σ hlt.ne 1 1 (hfix hlt 1),
      map_one, ← single_neg, Matrix.mul_neg]

theorem commute_single_of_commute_proj {Z : SpecialLinearGroup (Fin n) K} {i j : Fin n}
    (hij : i ≠ j)
    (h : proj n K (Matrix.SpecialLinearGroup.transvection hij 1) * proj n K Z =
      proj n K Z * proj n K (Matrix.SpecialLinearGroup.transvection hij 1)) :
    Commute (single i j (1 : K)) (Z : Matrix (Fin n) (Fin n) K) := by
  set u := Matrix.SpecialLinearGroup.transvection hij (1 : K)
  have h1 : proj n K (Z * u * Z⁻¹) = proj n K u := by
    rw [map_mul, map_mul, map_inv, ← h, mul_inv_cancel_right]
  have hZ : ((Z * u * Z⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Matrix.SpecialLinearGroup.toGL Z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (1 + single i j 1) *
        (((Matrix.SpecialLinearGroup.toGL Z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  exact mul_eq_of_proj_eq (Matrix.SpecialLinearGroup.toGL Z) hZ
    (Matrix.SpecialLinearGroup.transvection_coe hij 1) (single_mul_single_self_eq_zero hij _ _)
    (single_mul_single_self_eq_zero hij _ _) (single_apply_self_eq_zero hij 1 i) h1

theorem exists_eq_proj_transvection_of_commute (hn : 2 ≤ n) {z : projectiveSL n K}
    (hz : ∀ u ∈ projUnitriangular n K, u * z = z * u) :
    ∃ b : K, z = proj n K (Matrix.SpecialLinearGroup.transvection (firstIdx_ne_lastIdx hn) b) := by
  obtain ⟨Z, rfl⟩ := proj_surjective n K z
  have hcomm : ∀ i j : Fin n, i < j → Commute (single i j (1 : K)) (Z : Matrix (Fin n) (Fin n) K) :=
    fun i j hij => commute_single_of_commute_proj hij.ne
      (hz _ (proj_transvection_mem_projUnitriangular hij 1))
  have hZ := eq_scalar_add_single_of_commute hn hcomm
  set i₀ := firstIdx hn with hi₀
  set l := lastIdx hn with hl
  have hi₀l : i₀ ≠ l := firstIdx_ne_lastIdx hn
  set a := (Z : Matrix (Fin n) (Fin n) K) i₀ i₀ with ha
  set b := (Z : Matrix (Fin n) (Fin n) K) i₀ l with hb
  have ha0 : a ≠ 0 := ne_zero_of_eq_scalar_add_single hn (Matrix.SpecialLinearGroup.toGL Z) hZ
  set T := Matrix.SpecialLinearGroup.transvection hi₀l (b / a) with hT
  have hZT : (Z : Matrix (Fin n) (Fin n) K) = a • (T : Matrix (Fin n) (Fin n) K) := by
    rw [hT, Matrix.SpecialLinearGroup.transvection_coe, smul_add, smul_one_eq_diagonal,
      ← scalar_apply, smul_single, smul_eq_mul, mul_div_cancel₀ _ ha0]
    exact hZ
  have han : a ^ n = 1 := by
    have h := congrArg Matrix.det hZT
    simp only [Matrix.SpecialLinearGroup.det_coe, det_smul, Fintype.card_fin, mul_one] at h
    exact h.symm
  refine ⟨b / a, (proj_eq_proj_iff.mpr ⟨Units.mk0 a ha0, ?_, ?_⟩).symm⟩
  · ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, han, Units.val_one]
  · simp only [Matrix.SpecialLinearGroup.coe_mul, hZT, Matrix.mul_smul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Units.val_mk0, smul_one_eq_diagonal, ← scalar_apply]

end Standard

section Sylow

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_conj_projUnitriangular (hn : 1 ≤ n) (U : Sylow p (projectiveSL n K)) :
    ∃ g : projectiveSL n K, ∀ x, x ∈ (U : Subgroup (projectiveSL n K)) ↔
      g⁻¹ * x * g ∈ projUnitriangular n K := by
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) p hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (projectiveSL n K) U₀ U
  refine ⟨g, fun x => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hU₀,
    ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem mem_range_conj_of_fix_sylow (hn : 3 ≤ n) (U : Sylow p (projectiveSL n K))
    (β : MulAut (projectiveSL n K)) (hβ : ∀ u ∈ (U : Subgroup (projectiveSL n K)), β u = u) :
    β ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  obtain ⟨g, hg⟩ := exists_conj_projUnitriangular (by omega) U
  have h := mem_range_conj_of_fix_projUnitriangular hn
    ((MulAut.conj g)⁻¹ * β * MulAut.conj g) fun u hu => by
      have hgu : g * u * g⁻¹ ∈ (U : Subgroup (projectiveSL n K)) := by
        rw [hg]
        simpa [mul_assoc] using hu
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hβ _ hgu, MulAut.inv_apply,
        MulAut.conj_symm_apply]
      group
  obtain ⟨x, hx⟩ := h
  refine ⟨g * x * g⁻¹, ?_⟩
  rw [map_mul, map_mul, hx, map_inv]
  group

theorem exists_conj_eq_transvection_of_commute_sylow (hn : 2 ≤ n)
    (U : Sylow p (projectiveSL n K)) {z : projectiveSL n K}
    (hz : ∀ u ∈ (U : Subgroup (projectiveSL n K)), u * z = z * u) :
    ∃ (g : projectiveSL n K) (b : K),
      (∀ x, x ∈ (U : Subgroup (projectiveSL n K)) ↔ g⁻¹ * x * g ∈ projUnitriangular n K) ∧
      z = g * proj n K (Matrix.SpecialLinearGroup.transvection (firstIdx_ne_lastIdx hn) b) *
        g⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_projUnitriangular (by omega) U
  obtain ⟨b, hb⟩ := exists_eq_proj_transvection_of_commute hn (z := g⁻¹ * z * g) fun u hu => by
    have hgu : g * u * g⁻¹ ∈ (U : Subgroup (projectiveSL n K)) := by
      rw [hg]
      simpa [mul_assoc] using hu
    have h := hz _ hgu
    calc u * (g⁻¹ * z * g) = g⁻¹ * ((g * u * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * u * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * z * g * u := by group
  refine ⟨g, b, hg, ?_⟩
  rw [← hb]
  group

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem isInvolutionClass_one_proj_transvection [CharP K 2] {i j : Fin n} (hij : i ≠ j) {b : K}
    (hb : b ≠ 0) :
    IsInvolutionClass 1 (proj n K (Matrix.SpecialLinearGroup.transvection hij b)) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · rw [← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  · rw [Matrix.SpecialLinearGroup.transvection_coe, add_sub_cancel_left]
    have hcolj : (single i j b).col j = b • Pi.single i 1 := by
      funext a
      simp [Matrix.col_apply, single_apply, Pi.single_apply, eq_comm]
    refine rank_eq_one_of_col_mem (v := b • Pi.single i 1) ?_ (fun k => ?_) (j₀ := j) ?_
    · exact smul_ne_zero hb (Pi.single_ne_zero_iff.2 one_ne_zero)
    · by_cases hk : k = j
      · subst hk
        rw [hcolj]
        exact Submodule.mem_span_singleton_self _
      · rw [show (single i j b).col k = 0 by
          funext a
          simp [Matrix.col_apply, Ne.symm hk]]
        exact Submodule.zero_mem _
    · exact hcolj

theorem isInvolutionClass_one_of_mem_centralizer_sylow [CharP K 2] (hn : 2 ≤ n)
    (U : Sylow 2 (projectiveSL n K)) {z : projectiveSL n K} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup (projectiveSL n K)), u * z = z * u) : IsInvolutionClass 1 z := by
  obtain ⟨g, b, -, rfl⟩ := exists_conj_eq_transvection_of_commute_sylow hn U hz
  have hb : b ≠ 0 := by
    rintro rfl
    rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one, mul_one, mul_inv_cancel] at hz1
    exact hz1 rfl
  obtain ⟨g', rfl⟩ := proj_surjective n K g
  have h := (isInvolutionClass_one_proj_transvection (firstIdx_ne_lastIdx hn) hb).conjAut
    (Matrix.SpecialLinearGroup.toGL g')
  rwa [conjAut_toGL, MulAut.conj_apply] at h

end Sylow

section Transport

variable {X : Type*} [Group X] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem mulAut_congr_conj {Y : Type*} [Group Y] (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

omit [CharP K p] in
theorem exists_sylow_map_of_mulEquiv (e : X ≃* projectiveSL n K) (U : Sylow p X) :
    ∃ U' : Sylow p (projectiveSL n K), ∀ x : X,
      x ∈ (U : Subgroup X) ↔ e x ∈ (U' : Subgroup (projectiveSL n K)) := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  refine ⟨U.mapSurjective (f := e.toMonoidHom) e.surjective, fun x => ?_⟩
  change x ∈ (U : Subgroup X) ↔ e x ∈ (U : Subgroup X).map e.toMonoidHom
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mem_range_conj_of_fix_sylow_of_mulEquiv (hn : 3 ≤ n) (e : X ≃* projectiveSL n K)
    (U : Sylow p X) (β : MulAut X) (hβ : ∀ u ∈ (U : Subgroup X), β u = u) :
    β ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨U', hU'⟩ := exists_sylow_map_of_mulEquiv e U
  obtain ⟨y, hy⟩ := mem_range_conj_of_fix_sylow hn U' (MulAut.congr e β) fun u hu => by
    obtain ⟨x, rfl⟩ := e.surjective u
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hβ x ((hU' x).2 hu)]
  refine ⟨e.symm y, ?_⟩
  apply (MulAut.congr e).injective
  rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, ← hy]

omit [Fact p.Prime] [CharP K p] in
theorem isInvolutionClass_one_of_commute_sylow_of_mulEquiv [CharP K 2] (hn : 2 ≤ n)
    (e : X ≃* projectiveSL n K) (U : Sylow 2 X) {z : X} (hz1 : z ≠ 1)
    (hz : ∀ u ∈ (U : Subgroup X), u * z = z * u) : IsInvolutionClass 1 (e z) := by
  obtain ⟨U', hU'⟩ := exists_sylow_map_of_mulEquiv e U
  refine isInvolutionClass_one_of_mem_centralizer_sylow hn U'
    (fun h => hz1 (e.injective (h.trans (map_one e).symm))) fun u hu => ?_
  obtain ⟨x, rfl⟩ := e.surjective u
  rw [← map_mul, ← map_mul, hz x ((hU' x).2 hu)]

end Transport

end CFSG.SeitzReduction.LinearPilot

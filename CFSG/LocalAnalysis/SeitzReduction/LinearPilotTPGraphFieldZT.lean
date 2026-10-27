module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreConj
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPGraphFieldCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.LinearGroups
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.UnitaryPilot (IsUnitaryTransvection isUnitaryTransvection_of_commute_sylow
  exists_conj_eq_stdTransvection exists_eq_hermTransvection_of_mem_isotropicTransvectionGroup)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.UnbalancedCatalog (conjAut_eq_conjAut_iff)

theorem rank_eq_one_of_forall_mulVec {n : ℕ} {K : Type*} [Field K]
    (M : Matrix (Fin n) (Fin n) K) (a : Fin n → K) (hM : ∀ x, ∃ t : K, M *ᵥ x = t • a)
    (hM0 : ∃ x, M *ᵥ x ≠ 0) : M.rank = 1 := by
  obtain ⟨x₀, hx₀⟩ := hM0
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hM x₀
    rw [smul_zero] at ht
    exact hx₀ ht
  have hle : LinearMap.range M.mulVecLin ≤ K ∙ a := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨t, ht⟩ := hM x
    rw [Matrix.mulVecLin_apply, ht]
    exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self a)
  have h1 : M.rank ≤ 1 := by
    have := Submodule.finrank_mono hle
    rwa [finrank_span_singleton ha0] at this
  have h2 : M.rank ≠ 0 := by
    intro h0
    rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    apply hx₀
    have := LinearMap.congr_fun h0 x₀
    rwa [Matrix.mulVecLin_apply] at this
  omega

variable {e : ℕ} {K : Type} [Field K] {n : ℕ}

theorem isInvolutionClass_one_of_isUnitaryTransvection (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    {E : unitaryPSU h n ≃* unitaryCore 2 e K n}
    (hE : ∀ g, MulAut.conj (E (unitaryProj h n g) : projectiveSL n K) = conjAut n K g)
    {w : unitaryPSU h n} (hw : IsUnitaryTransvection h w) :
    IsInvolutionClass 1 (E w : projectiveSL n K) := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨hw1, ℓ, hℓ, hwℓ⟩ := hw
  obtain ⟨a, ha0, ha, rfl⟩ := UnitaryHigher.exists_eq_span_of_mem_isotropicLines hℓ
  obtain ⟨y, hy, rfl⟩ := mem_map.1 hwℓ
  obtain ⟨c, -, hyc⟩ := exists_eq_hermTransvection_of_mem_isotropicTransvectionGroup h ha hy
  have hyx : ∀ x, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      x + (c * stdHermForm h n a x) • a := fun x => by
    have := LinearMap.congr_fun hyc x
    rwa [Matrix.mulVecLin_apply, hermTransvection_apply] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw1
    have hy1 : y = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Matrix.ext_iff_mulVec]
      intro x
      rw [hyx, zero_mul, zero_smul, add_zero]
      simp
    rw [hy1, map_one]
  let g : SpecialLinearGroup (Fin n) K :=
    ⟨((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ((mem_unitarySU_iff h).1 y.2).1⟩
  have hgE : proj n K g = (E (unitaryProj h n y) : projectiveSL n K) := by
    apply CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conj_injective_projectiveSL
      (F := K) hn
    rw [hE, ← conjAut_toGL]
    exact congrArg (conjAut n K) (Units.ext rfl)
  rw [← hgE]
  have hgx : ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x = x + (c * stdHermForm h n a x) • a :=
    hyx
  refine ⟨g, rfl, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, hgx, hgx, Matrix.one_mulVec, map_add, map_smul, ha, smul_zero,
      add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  · refine rank_eq_one_of_forall_mulVec _ a (fun x => ⟨c * stdHermForm h n a x, ?_⟩) ?_
    · rw [Matrix.sub_mulVec, hgx, Matrix.one_mulVec, add_sub_cancel_left]
    · by_contra hall
      push Not at hall
      apply ha0
      refine stdHermForm_separatingLeft h n a fun x => ?_
      have h1 := hall x
      rw [Matrix.sub_mulVec, hgx, Matrix.one_mulVec, add_sub_cancel_left] at h1
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact (mul_eq_zero.1 h2).resolve_left hc0
      · exact absurd h2 ha0

theorem isUnitaryTransvection_of_isInvolutionClass_one (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    {E : unitaryPSU h n ≃* unitaryCore 2 e K n}
    (hE : ∀ g, MulAut.conj (E (unitaryProj h n g) : projectiveSL n K) = conjAut n K g)
    {w : unitaryPSU h n} (hw : IsInvolutionClass 1 (E w : projectiveSL n K)) :
    IsUnitaryTransvection h w := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨u, rfl⟩ := unitaryProj_surjective h n w
  set H := stdHermForm h n with hH
  have hsym : ∀ x y, h.bar (H x y) = H y x := fun x y => by
    simp only [hH, stdHermForm_apply, map_sum, map_mul, h.bar_bar]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  set i2 : Fin n := ⟨2, by omega⟩ with hi2
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [i0, i2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
  obtain ⟨c', hc'⟩ := exists_conj_eq_xab h01 hw
  obtain ⟨s, rfl⟩ := proj_surjective n K c'
  set g := s⁻¹ * SpecialLinearGroup.transvection h01 (1 : K) * s with hg
  have hyg : (E (unitaryProj h n u) : projectiveSL n K) = proj n K g := by
    rw [hg, map_mul, map_mul, map_inv, ← xab_def, ← hc']
    group
  have hss : ((s : Matrix (Fin n) (Fin n) K) *
      ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hss' : (((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (s : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set a : Fin n → K :=
    ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i0 1 with ha
  set b : Fin n → K := fun j => (s : Matrix (Fin n) (Fin n) K) i1 j with hb
  have hbx : ∀ x, b ⬝ᵥ x = ((s : Matrix (Fin n) (Fin n) K) *ᵥ x) i1 := fun x => rfl
  have hgx : ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x = x + (b ⬝ᵥ x) • a := by
    intro x
    rw [hg, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, hss', Matrix.one_mulVec, one_mul, hbx]
  have hba : b ⬝ᵥ a = 0 := by
    rw [hbx, ha, Matrix.mulVec_mulVec, hss, Matrix.one_mulVec, Pi.single_eq_of_ne h01.symm]
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v => ((s : Matrix (Fin n) (Fin n) K) *ᵥ v) i0) h0
    simp only [ha, Matrix.mulVec_mulVec, hss, Matrix.one_mulVec, Pi.single_eq_same,
      Matrix.mulVec_zero, Pi.zero_apply] at h1
    exact one_ne_zero h1
  set y₀ : Fin n → K :=
    ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i1 1 with hy₀
  have hby₀ : b ⬝ᵥ y₀ = 1 := by
    rw [hbx, hy₀, Matrix.mulVec_mulVec, hss, Matrix.one_mulVec, Pi.single_eq_same]
  have hcg : conjAut n K (SpecialLinearGroup.toGL g) = conjAut n K (u : GL (Fin n) K) := by
    rw [← hE u, hyg, conjAut_toGL]
  obtain ⟨l, hl⟩ := (conjAut_eq_conjAut_iff hn _ _).mp hcg
  have hgmat : (g : Matrix (Fin n) (Fin n) K) =
      (((u : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) l : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := congrArg Units.val hl
  have hgu : ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x =
      (l : K) • (((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) := by
    intro x
    rw [hgmat, Units.val_mul, ← Matrix.mulVec_mulVec, GeneralLinearGroup.coe_scalar, scalar_apply,
      ← smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]
  have hisou : ∀ x y, H (((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)
      (((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) = H x y :=
    ((mem_unitarySU_iff_isometry h).1 u.2).2
  have hisog : ∀ x y, H ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = h.bar (l : K) * (l : K) * H x y := by
    intro x y
    rw [hgu, hgu, LinearMap.map_smulₛₗ₂, map_smul, hisou, smul_eq_mul, smul_eq_mul, mul_assoc]
  obtain ⟨v, hv0, hbv, hav⟩ : ∃ v : Fin n → K, v ≠ 0 ∧ b ⬝ᵥ v = 0 ∧ H a v = 0 := by
    set M : Matrix (Fin n) (Fin n) K :=
      Matrix.of fun i j => if i = i0 then b j else if i = i1 then h.bar (a j) else 0 with hM
    have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i2 fun j => by
      simp [hM, h20, h21]
    obtain ⟨v, hv0, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine ⟨v, hv0, ?_, ?_⟩
    · have h1 := congrFun hMv i0
      simpa [hM, Matrix.mulVec, dotProduct] using h1
    · have h1 := congrFun hMv i1
      simpa [hM, Matrix.mulVec, dotProduct, h01.symm, hH, stdHermForm_apply] using h1
  have hgv : (g : Matrix (Fin n) (Fin n) K) *ᵥ v = v := by rw [hgx, hbv, zero_smul, add_zero]
  have hva : H v a = 0 := by rw [← hsym, hav, map_zero]
  have hN : h.bar (l : K) * (l : K) = 1 := by
    obtain ⟨z, hz⟩ : ∃ z, H v z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0 (stdHermForm_separatingLeft h n v hall)
    have h1 := hisog v z
    rw [hgv, hgx z, map_add, map_smul, hva, smul_zero, add_zero] at h1
    exact (mul_right_cancel₀ hz (by rw [one_mul]; exact h1.symm))
  have hiso : ∀ x y, H ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = H x y := fun x y => by
    rw [hisog, hN, one_mul]
  have hexp : ∀ x y, (b ⬝ᵥ y) * H x a + h.bar (b ⬝ᵥ x) * H a y +
      h.bar (b ⬝ᵥ x) * (b ⬝ᵥ y) * H a a = 0 := by
    intro x y
    have h1 := hiso x y
    rw [hgx, hgx, LinearMap.map_add₂, map_add, map_add, LinearMap.map_smulₛₗ₂,
      LinearMap.map_smulₛₗ₂, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul] at h1
    linear_combination h1
  set κ := H a y₀ + H a a with hκ
  have hκx : ∀ x, H a x = -(b ⬝ᵥ x) * h.bar κ := by
    intro x
    have h1 := hexp x y₀
    rw [hby₀, one_mul, mul_one] at h1
    have h2 := congrArg h.bar h1
    rw [map_add, map_add, map_mul, map_mul, h.bar_bar, hsym, map_zero] at h2
    rw [hκ, map_add]
    linear_combination h2
  have hκ0 : h.bar κ ≠ 0 := by
    intro h0
    apply ha0
    refine stdHermForm_separatingLeft h n a fun x => ?_
    rw [hκx x, h0, mul_zero]
  set d := -(h.bar κ)⁻¹ with hd
  have hd0 : d ≠ 0 := neg_ne_zero.2 (inv_ne_zero hκ0)
  have hbd : ∀ x, b ⬝ᵥ x = d * H a x := by
    intro x
    rw [hκx x, hd]
    field_simp
  have haa : H a a = 0 := by
    have h1 := hbd a
    rw [hba] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hd0
  have htr : d + h.bar d = 0 := by
    obtain ⟨x₁, hx₁⟩ : ∃ x, H a x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact ha0 (stdHermForm_separatingLeft h n a hall)
    have h1 := hexp x₁ x₁
    rw [haa, mul_zero, add_zero, hbd x₁, map_mul, hsym a x₁] at h1
    have hB0 : H x₁ a ≠ 0 := by
      rw [← hsym a x₁]
      exact (map_ne_zero h.bar).2 hx₁
    have h2 : (d + h.bar d) * (H a x₁ * H x₁ a) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (mul_ne_zero hx₁ hB0)
  have hgSU : SpecialLinearGroup.toGL g ∈ unitarySU 2 e K n :=
    (mem_unitarySU_iff_isometry h).2 ⟨g.2, hiso⟩
  have hug : unitaryProj h n u = unitaryProj h n ⟨SpecialLinearGroup.toGL g, hgSU⟩ := by
    rw [unitaryProj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      unitaryScalars_eq h (by omega), mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
      MonoidHom.mem_range]
    refine ⟨l, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    change _ = (u : GL (Fin n) K)⁻¹ * SpecialLinearGroup.toGL g
    rw [hl, inv_mul_cancel_left]
  refine ⟨?_, K ∙ a, UnitaryHigher.span_mem_isotropicLines ha0 haa, ?_⟩
  · intro h1
    apply hw.ne_one one_ne_zero
    rw [h1, map_one, OneMemClass.coe_one]
  · rw [hug]
    refine mem_map_of_mem _ (Subgroup.subset_closure ⟨a, Submodule.mem_span_singleton_self a, d,
      (h.mem_traceZero).2 htr, ?_⟩)
    refine LinearMap.ext fun x => ?_
    rw [Matrix.mulVecLin_apply, hermTransvection_apply]
    change (g : Matrix (Fin n) (Fin n) K) *ᵥ x = _
    rw [hgx, hbd]

theorem centralizesSylow_of_isUnitaryTransvection (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    {w : unitaryPSU h n} (hw : IsUnitaryTransvection h w) (hw2 : w * w = 1) :
    CentralizesSylow 2 w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.SeitzReduction.UnitaryPilot.finite_unitaryPSU h n
  obtain ⟨U⟩ : Nonempty (Sylow 2 (unitaryPSU h n)) := inferInstance
  have hw1 : w ≠ 1 := hw.1
  have h2 : 2 ∣ Nat.card (unitaryPSU h n) := by
    have ho : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hw2]) hw1
    have h3 := orderOf_dvd_natCard w
    rwa [ho] at h3
  have hU : (U : Subgroup (unitaryPSU h n)) ≠ ⊥ := U.ne_bot_of_dvd_card h2
  have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot _).2 hU
  have hZ := U.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center U)
  set z₀ : unitaryPSU h n := ((z : U) : unitaryPSU h n) with hz₀
  have hz₀c : ∀ u ∈ (U : Subgroup (unitaryPSU h n)), u * z₀ = z₀ * u := by
    intro u hu
    have h1 := Subgroup.mem_center_iff.1 z.2 ⟨u, hu⟩
    exact congrArg Subtype.val h1
  have hz₀1 : z₀ ≠ 1 := by
    intro h0
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h0
  have hz₀t : IsUnitaryTransvection h z₀ :=
    isUnitaryTransvection_of_commute_sylow h (by omega) U hz₀1 hz₀c
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨g₁, hg₁⟩ := exists_conj_eq_stdTransvection h hn hw h01
  obtain ⟨g₂, hg₂⟩ := exists_conj_eq_stdTransvection h hn hz₀t h01
  have hwz : w = MulAut.conj (g₁⁻¹ * g₂) z₀ := by
    rw [MulAut.conj_apply]
    have e1 : w = g₁⁻¹ * (g₁ * w * g₁⁻¹) * g₁ := by group
    rw [e1, hg₁, ← hg₂]
    group
  rw [hwz]
  exact CentralizesSylow.map_mulEquiv (MulAut.conj (g₁⁻¹ * g₂)) ⟨U, hz₀c⟩

theorem twoCentralTransvection_perfectCore_graphField (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    TwoCentralTransvection n K (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  intro z hz hz1 hzc
  have heq := perfectCore_autFixSubgroup_graphField h hn hnq σ hσ
  obtain ⟨E, hE⟩ := exists_unitaryCoreEquiv h hn σ hσ
  set ψ := (MulEquiv.subgroupCongr heq).trans E.symm with hψ
  have hEψ : (E (ψ ⟨z, hz⟩) : projectiveSL n K) = z := by
    rw [hψ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨S, hS⟩ := hzc.map_mulEquiv ψ
  have hw1 : ψ ⟨z, hz⟩ ≠ 1 := by
    intro h0
    apply hz1
    rw [← hEψ, h0, map_one, OneMemClass.coe_one]
  have ht := isUnitaryTransvection_of_commute_sylow h (by omega) S hw1 hS
  have h1 := isInvolutionClass_one_of_isUnitaryTransvection h hn hE ht
  rwa [hEψ] at h1

theorem centralizesSylow_perfectCore_graphField (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) {y : projectiveSL n K}
    (hy : y ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)))
    (hyt : IsInvolutionClass 1 y) :
    CentralizesSylow 2 (⟨y, hy⟩ : perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have := CFSG.SeitzReduction.UnitaryPilot.finite_unitaryPSU h n
  have heq := perfectCore_autFixSubgroup_graphField h hn hnq σ hσ
  obtain ⟨E, hE⟩ := exists_unitaryCoreEquiv h hn σ hσ
  set ψ := (MulEquiv.subgroupCongr heq).trans E.symm with hψ
  have hEψ : (E (ψ ⟨y, hy⟩) : projectiveSL n K) = y := by
    rw [hψ, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have ht : IsUnitaryTransvection h (ψ ⟨y, hy⟩) :=
    isUnitaryTransvection_of_isInvolutionClass_one h hn hE (by rw [hEψ]; exact hyt)
  have hyy : y * y = 1 := by
    obtain ⟨g, hg, hgg, -⟩ := hyt
    rw [← hg, ← map_mul, hgg, map_one]
  have hw2 : ψ ⟨y, hy⟩ * ψ ⟨y, hy⟩ = 1 := by
    rw [← map_mul, ← map_one ψ]
    congr 1
    exact Subtype.ext hyy
  have hc := (centralizesSylow_of_isUnitaryTransvection h hn ht hw2).map_mulEquiv ψ.symm
  rwa [MulEquiv.symm_apply_apply] at hc

end CFSG.SeitzReduction.LinearPilot

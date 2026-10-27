module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityCommon
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityIsotropic
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldProjection

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.LinearGroups
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBGraphField
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {p e n : ℕ}

theorem conjAut_mul_fieldAut_eq_one_of_centralizes (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (φ : K ≃+* K)
    (hc : ∀ g ∈ unitarySU p e K n, conjAut n K A * fieldAut n K φ * conjAut n K g *
      (conjAut n K A * fieldAut n K φ)⁻¹ = conjAut n K g) :
    conjAut n K A * fieldAut n K φ = 1 := by
  have := h.finite
  have : NeZero n := ⟨by omega⟩
  obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  have htv : ∀ v : Fin n → K, stdHermForm h n v v = 0 → ∃ g : GL (Fin n) K,
      (∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x = x + (τ * stdHermForm h n v x) • v) ∧
        A * GeneralLinearGroup.map (φ : K →+* K) g = g * A := by
    intro v hv
    obtain ⟨g, hg⟩ := exists_mem_unitarySU_hermTransvection h hv hτ
    have hgx : ∀ x, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
        x + (τ * stdHermForm h n v x) • v := fun x => by
      have := LinearMap.congr_fun hg x
      rwa [Matrix.mulVecLin_apply, hermTransvection_apply] at this
    have hunip : (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
        (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro y
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.one_mulVec, hgx, add_sub_cancel_left, hgx, add_sub_cancel_left,
        Matrix.zero_mulVec]
      simp [hv]
    have h1 := hc g g.2
    rw [conj_conjAut_fieldAut] at h1
    have h2 := eq_of_conjAut_eq_of_unipotent hn (unipotent_conj (unipotent_map _ hunip)) hunip h1
    exact ⟨g, hgx, mul_inv_eq_iff_eq_mul.mp h2⟩
  let T : (Fin n → K) →ₛₗ[(φ : K →+* K)] (Fin n → K) :=
    { toFun := fun x => (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (x i)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add]
        rw [← Matrix.mulVec_add]
        rfl
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← Matrix.mulVec_smul]
        rfl }
  have hTapply : ∀ x, T x = (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (x i) := fun _ => rfl
  have hTinj : Function.Injective T := by
    intro x y hxy
    rw [hTapply, hTapply] at hxy
    have h1 := congrArg (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) hxy
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
    funext i
    exact φ.injective (congrFun h1 i)
  have hTg : ∀ g : GL (Fin n) K, A * GeneralLinearGroup.map (φ : K →+* K) g = g * A →
      ∀ x, T ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) = (g : Matrix (Fin n) (Fin n) K) *ᵥ T x := by
    intro g hg x
    rw [hTapply, hTapply]
    have hφg : (fun i => φ (((g : Matrix (Fin n) (Fin n) K) *ᵥ x) i)) =
        ((GeneralLinearGroup.map (φ : K →+* K) g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          fun i => φ (x i) := by
      funext i
      have h1 := RingHom.map_mulVec (φ : K →+* K) (g : Matrix (Fin n) (Fin n) K) x i
      simp only [RingEquiv.coe_toRingHom] at h1
      rw [h1]
      rfl
    rw [hφg, Matrix.mulVec_mulVec, ← Units.val_mul, hg, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hstar : ∀ v, stdHermForm h n v v = 0 → ∀ x,
      φ (τ * stdHermForm h n v x) • T v = (τ * stdHermForm h n v (T x)) • v := by
    intro v hv x
    obtain ⟨g, hgx, hgA⟩ := htv v hv
    have h1 := hTg g hgA x
    rw [hgx, hgx, map_add, map_smulₛₗ] at h1
    simpa using add_left_cancel h1
  have hline : ∀ v, stdHermForm h n v v = 0 → ∃ μ : K, T v = μ • v := by
    intro v hv
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, map_zero, smul_zero]⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x, stdHermForm h n v x ≠ 0 := by
      by_contra! hall
      exact hv0 (stdHermForm_separatingLeft h n v hall)
    have hne : φ (τ * stdHermForm h n v x₀) ≠ 0 :=
      (map_ne_zero φ).mpr (mul_ne_zero hτ0 hx₀)
    refine ⟨(φ (τ * stdHermForm h n v x₀))⁻¹ * (τ * stdHermForm h n v (T x₀)), ?_⟩
    rw [mul_smul, ← hstar v hv x₀, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hperp : ∀ v, stdHermForm h n v v = 0 → ∀ x, stdHermForm h n v x = 0 →
      stdHermForm h n v (T x) = 0 := by
    intro v hv x hx
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    have h1 := hstar v hv x
    rw [hx, mul_zero, map_zero, zero_smul, eq_comm, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hτ0
    · exact absurd h1 hv0
  obtain ⟨hφ1, μ, hμ⟩ := semilinear_eq_smul_of_isotropic h (stdHermForm_isSymm h n)
    (stdHermForm_separatingLeft h n) (by rw [Module.finrank_fin_fun]; exact hn) T hTinj hline
    hperp
  have hφx : ∀ y : K, φ y = y := fun y => by rw [hφ1]; rfl
  have hAμ : (A : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) μ := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    have h1 := hμ x
    simp only [hTapply, hφx] at h1
    rw [h1]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hAc : A ∈ center (GL (Fin n) K) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨μ, hAμ.symm⟩
  rw [GeneralLinearGroup.center_eq_range_scalar] at hAc
  obtain ⟨c, hc⟩ := hAc
  rw [← hc, conjAut_scalar, hφ1, map_one, one_mul]

theorem linear_graph_field_full_centralizer_rigidity (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ((conjAut n K).comp (unitarySU p e K n).subtype).ker = unitaryScalars h n ∧
      (∃ ι : unitaryPSU h n ≃* (unitarySU p e K n).map (conjAut n K),
        ∀ g, (ι (unitaryProj h n g) : MulAut (projectiveSL n K)) = conjAut n K g) ∧
      (unitarySU p e K n).map (conjAut n K) ≤
        (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ∧
      (centralizer {fieldAut n K σ * dualAut n K} : Set (MulAut (projectiveSL n K))) =
        {α | ∃ B : GL (Fin n) K,
          ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1 ∧
          ∃ (φ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
            α = conjAut n K B * fieldAut n K φ * dualAut n K ^ ε} ∧
      (unitarySU p e K n).map (conjAut n K) ≤ centralizer {fieldAut n K σ * dualAut n K} ∧
      (((unitarySU p e K n).map (conjAut n K)).subgroupOf
        (centralizer {fieldAut n K σ * dualAut n K})).Normal ∧
      centralizer (((unitarySU p e K n).map (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
          Set (MulAut (projectiveSL n K))) =
        zpowers (fieldAut n K σ * dualAut n K) := by
  have := h.finite
  have : NeZero n := ⟨by omega⟩
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ, h.bar_bar]
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two, RingAut.mul_apply, hσσ]
    rfl
  have hσne : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [← hσ, h1]
    rfl
  have hmapσ : ∀ M : Matrix (Fin n) (Fin n) K, M.map σ = M.map h.bar := fun M => by
    ext i j
    simp [hσ]
  have hU : ∀ B : GL (Fin n) K,
      ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1 ↔
        B ∈ Uid σ n := by
    intro B
    rw [mem_Uid_iff, conjTr, hmapσ]
  have hSU : ∀ g : GL (Fin n) K, g ∈ unitarySU p e K n ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 ∧ g ∈ Uid σ n := by
    intro g
    rw [mem_unitarySU_iff h, hU]
  have hinvT : ∀ B ∈ Uid σ n,
      GeneralLinearGroup.inverseTranspose B = GeneralLinearGroup.map (σ : K →+* K) B := by
    intro B hB
    rw [mem_Uid_iff] at hB
    apply Units.ext
    rw [GeneralLinearGroup.coe_inverseTranspose]
    have h1 : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        conjTr σ (B : Matrix (Fin n) (Fin n) K) := by
      calc ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          _ = conjTr σ (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) *
              ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [hB, Matrix.one_mul]
          _ = conjTr σ (B : Matrix (Fin n) (Fin n) K) := by
            rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [h1, conjTr, transpose_transpose]
    rfl
  have hfixU : ∀ B ∈ Uid σ n,
      GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose B) = B := by
    intro B hB
    rw [hinvT B hB]
    exact GeneralLinearGroup.ext fun i j => by simp [hσσ]
  have hβc : ∀ A : GL (Fin n) K, fieldAut n K σ * dualAut n K * conjAut n K A =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose A)) *
        (fieldAut n K σ * dualAut n K) := by
    intro A
    rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, fieldAut_mul_conjAut, mul_assoc]
  have hθf : ∀ φ : K ≃+* K, Commute (fieldAut n K σ * dualAut n K) (fieldAut n K φ) :=
    fun φ => (fieldAut_commute σ φ).mul_left (fieldAut_commute_dualAut φ).symm
  have hθd : Commute (fieldAut n K σ * dualAut n K) (dualAut n K) :=
    (fieldAut_commute_dualAut σ).mul_left (Commute.refl _)
  set G : Set (GL (Fin n) K) :=
    {B | ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1}
    with hGdef
  have hG : ∀ A : GL (Fin n) K, Commute (fieldAut n K σ * dualAut n K) (conjAut n K A) ↔
      ∃ B ∈ G, conjAut n K A = conjAut n K B := by
    intro A
    have hcomm : Commute (fieldAut n K σ * dualAut n K) (conjAut n K A) ↔
        conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose A)) = conjAut n K A := by
      change fieldAut n K σ * dualAut n K * conjAut n K A =
        conjAut n K A * (fieldAut n K σ * dualAut n K) ↔ _
      rw [hβc]
      exact mul_left_inj _
    rw [hcomm]
    constructor
    · intro h1
      obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h1
      have hfix : ProjGenLinGroup.mk A ∈ fixedPGL n K σ := by
        change pglGraphFieldAut n K σ (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A
        rw [pglGraphFieldAut_mk]
        change ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose A)) = _
        rw [hc, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
      rw [fixedPGL_eq_unitary_image n K (by omega) σ hσ2 hσne] at hfix
      obtain ⟨B, hB, hBA⟩ := hfix
      obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hBA
      exact ⟨B, (hU B).mpr hB, by rw [← hu, map_mul, conjAut_scalar, mul_one]⟩
    · rintro ⟨B, hB, hAB⟩
      have e1 : ∀ X : GL (Fin n) K, conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose X)) = fieldAut n K σ * dualAut n K *
            conjAut n K X * (fieldAut n K σ * dualAut n K)⁻¹ := fun X => by
        rw [hβc, mul_inv_cancel_right]
      rw [e1, hAB, ← e1, hfixU B ((hU B).mp hB)]
  have hSG : ∀ B ∈ G, ∀ g ∈ unitarySU p e K n, B * g * B⁻¹ ∈ unitarySU p e K n := by
    intro B hB g hg
    obtain ⟨hgdet, hgU⟩ := (hSU g).mp hg
    have hBU := (hU B).mp hB
    refine (hSU _).mpr ⟨?_, mul_mem (mul_mem hBU hgU) (inv_mem hBU)⟩
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hgdet, mul_one, ← det_mul,
      Units.mul_inv, det_one]
  have hSφ : ∀ φ : K ≃+* K, ∀ g ∈ unitarySU p e K n,
      GeneralLinearGroup.map (φ : K →+* K) g ∈ unitarySU p e K n := by
    intro φ g hg
    rw [mem_unitarySU_iff h] at hg ⊢
    obtain ⟨hgdet, hgU⟩ := hg
    have hcomm : ∀ x, h.bar (φ x) = φ (h.bar x) := fun x => by
      rw [← hσ, ← hσ]
      exact DFunLike.congr_fun (ringAut_commute σ φ) x
    refine ⟨?_, ?_⟩
    · change ((φ : K →+* K).mapMatrix (g : Matrix (Fin n) (Fin n) K)).det = 1
      rw [← RingHom.map_det, hgdet, map_one]
    · have e1 : (((GeneralLinearGroup.map (φ : K →+* K) g : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((GeneralLinearGroup.map (φ : K →+* K) g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (φ : K →+* K).mapMatrix (((g : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (g : Matrix (Fin n) (Fin n) K)) := by
        rw [map_mul]
        congr 1
        ext i j
        simp [hcomm]
      rw [e1, hgU, map_one]
  have hSδ : ∀ g ∈ unitarySU p e K n,
      GeneralLinearGroup.inverseTranspose g ∈ unitarySU p e K n := by
    intro g hg
    rw [hinvT g ((hSU g).mp hg).2]
    exact hSφ σ g hg
  have hNβ : ∀ g ∈ unitarySU p e K n,
      Commute (fieldAut n K σ * dualAut n K) (conjAut n K g) := fun g hg =>
    (hG g).mpr ⟨g, (hU g).mpr ((hSU g).mp hg).2, rfl⟩
  have hCN : centralizer (((unitarySU p e K n).map (conjAut n K) :
      Subgroup (MulAut (projectiveSL n K))) : Set (MulAut (projectiveSL n K))) =
        zpowers (fieldAut n K σ * dualAut n K) := by
    apply le_antisymm
    · intro α hα
      have hsemi : ∀ (A : GL (Fin n) K) (φ : K ≃+* K),
          conjAut n K A * fieldAut n K φ ∈ centralizer (((unitarySU p e K n).map
            (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
              Set (MulAut (projectiveSL n K))) → conjAut n K A * fieldAut n K φ = 1 := by
        intro A φ hAφ
        refine conjAut_mul_fieldAut_eq_one_of_centralizes h hn A φ fun g hg => ?_
        have := mem_centralizer_iff.mp hAφ (conjAut n K g) (mem_map_of_mem _ hg)
        rw [← this, mul_inv_cancel_right]
      obtain ⟨A, φ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 α
      rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
      · rw [pow_zero, mul_one] at hα ⊢
        rw [hsemi A φ hα]
        exact one_mem _
      · rw [pow_one] at hα ⊢
        have hβmem : fieldAut n K σ * dualAut n K ∈ centralizer (((unitarySU p e K n).map
            (conjAut n K) : Subgroup (MulAut (projectiveSL n K))) :
              Set (MulAut (projectiveSL n K))) := by
          rw [mem_centralizer_iff]
          rintro _ ⟨g, hg, rfl⟩
          exact (hNβ g hg).eq.symm
        have hprod : conjAut n K A * fieldAut n K φ * dualAut n K *
            (fieldAut n K σ * dualAut n K) = conjAut n K A * fieldAut n K (φ * σ) := by
          obtain ⟨-, hff, -, hdd, -⟩ := standard_automorphism_transport (n := n) (K := K)
          calc conjAut n K A * fieldAut n K φ * dualAut n K * (fieldAut n K σ * dualAut n K)
              _ = conjAut n K A * fieldAut n K φ * (dualAut n K * fieldAut n K σ) *
                  dualAut n K := by simp only [mul_assoc]
              _ = conjAut n K A * fieldAut n K φ * (fieldAut n K σ * dualAut n K) *
                  dualAut n K := by rw [dualAut_mul_fieldAut]
              _ = conjAut n K A * (fieldAut n K φ * fieldAut n K σ) *
                  (dualAut n K * dualAut n K) := by simp only [mul_assoc]
              _ = conjAut n K A * fieldAut n K (φ * σ) := by rw [hdd, mul_one, hff]
        have h1 := hsemi A (φ * σ) (hprod ▸ mul_mem hα hβmem)
        rw [← hprod] at h1
        rw [mul_eq_one_iff_eq_inv.mp h1]
        exact inv_mem (mem_zpowers _)
    · rw [zpowers_le, mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      exact (hNβ g hg).eq.symm
  have hker : ((conjAut n K).comp (unitarySU p e K n).subtype).ker = unitaryScalars h n := by
    rw [unitaryScalars_eq h (by omega)]
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
      MonoidHom.mem_range]
    change conjAut n K (g : GL (Fin n) K) = 1 ↔ _
    rw [conjAut_eq_one_iff hn]
  have hrange : ((conjAut n K).comp (unitarySU p e K n).subtype).range =
      (unitarySU p e K n).map (conjAut n K) := by
    rw [MonoidHom.range_comp, range_subtype]
  refine ⟨hker, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr hrange),
    fun g => rfl⟩, ?_, ?_, ?_, ?_, hCN⟩
  · rintro _ ⟨g, hg, rfl⟩
    let g' : SpecialLinearGroup (Fin n) K := ⟨(g : Matrix (Fin n) (Fin n) K), ((hSU g).mp hg).1⟩
    refine ⟨proj n K g', ?_⟩
    rw [← conjAut_toGL]
    exact congrArg (conjAut n K) (Units.ext rfl)
  · rw [centralizer_eq_of_conjAut_commute_iff hn hθf hθd G hG]
    rfl
  · rintro _ ⟨g, hg, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hNβ g hg).eq.symm
  · exact normal_of_conjAut_closed hn hθf hθd G hG (unitarySU p e K n) hSG hSφ hSδ

end CFSG.ComponentClassification.UnbalancedCatalog

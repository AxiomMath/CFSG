module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RootAutomorphismLayerKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverMixedInvariance
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic

public section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

section Root

variable (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem hermitianUnipotentPSU_mem_center_iff (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z ∈
        (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ) ↔ z.1.1 = 0 :=
  Subgroup.mem_map_iff_mem (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ)

theorem mem_center_iff_sq_eq_one [CharP K 2] {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ) ↔
      x ∈ unitaryCoverRoot J hJ ∧ x ^ 2 = 1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    rw [← map_pow, pow_two_eq_one_of_fst_eq_zero J hz, map_one]
  · rintro ⟨⟨z, rfl⟩, hz⟩
    refine ⟨z, (pow_two_eq_one_iff J z).1 (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ ?_), rfl⟩
    rw [map_pow, hz, map_one]

theorem map_omega₁_unitaryCoverRoot [CharP K 2] :
    (CFSG.omega₁ (G := unitaryCoverRoot J hJ) (p := 2)).map (unitaryCoverRoot J hJ).subtype =
      (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ) := by
  rw [SuzukiLayerKernel.map_omega₁_subtype,
    ← Subgroup.closure_eq ((unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ))]
  congr 1
  ext x
  exact (mem_center_iff_sq_eq_one J hJ).symm

theorem center_characteristic [CharP K 2] :
    (((unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ)).subgroupOf
      (unitaryCoverRoot J hJ)).Characteristic := by
  have hmem : ∀ x : unitaryCoverRoot J hJ, x ∈ ((unitaryCoverFirstCoord J).ker.map
      (hermitianUnipotentPSU J hJ)).subgroupOf (unitaryCoverRoot J hJ) ↔ x ^ 2 = 1 := fun x => by
    rw [Subgroup.mem_subgroupOf, mem_center_iff_sq_eq_one J hJ, and_iff_right x.2,
      ← Subgroup.coe_pow, ← OneMemClass.coe_one (unitaryCoverRoot J hJ), Subtype.coe_inj]
  refine Subgroup.characteristic_iff_comap_eq.2 fun ϕ => Subgroup.ext fun x => ?_
  rw [Subgroup.mem_comap, hmem, hmem, MulEquiv.coe_toMonoidHom, ← map_pow,
    map_eq_one_iff ϕ ϕ.injective]

end Root

theorem unitaryRoot_layer_kernel [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγU : (unitaryCoverRoot J hJ).map γ.toMonoidHom = unitaryCoverRoot J hJ)
    (hγV : ∀ v ∈ (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ), γ v = v)
    (hγUV : ∀ x ∈ unitaryCoverRoot J hJ,
      x⁻¹ * γ x ∈ (unitaryCoverFirstCoord J).ker.map (hermitianUnipotentPSU J hJ)) :
    ∃ b ∈ unitaryCoverRoot J hJ, γ = MulAut.conj b := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  obtain ⟨-, -, -, -, -, rho, hrho, -, hΩcard, h2tr, hstabα, hstabβ, hnormal, -, -, hTeq, -, -,
    -, -, hreg, -⟩ := unitary_three_point_structure J f hf hcard hfixed hJ
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    MulAction.compHom _ rho
  have : Finite (unitaryIsotropicPoints J) := Nat.finite_of_card_ne_zero (by rw [hΩcard]; omega)
  have : FaithfulSMul (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryIsotropicPoints J) :=
    ⟨fun h => hrho (Equiv.ext h)⟩
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J)
      (unitaryIsotropicPoints J) := ⟨fun b d => by
    by_cases hbd : b = d
    · exact ⟨1, by rw [hbd, one_smul]⟩
    · obtain ⟨g, hg, -⟩ := h2tr b d d b hbd (Ne.symm hbd)
      exact ⟨g, hg⟩⟩
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  set β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  set ψ := hermitianUnipotentPSU J hJ
  set V := (unitaryCoverFirstCoord J).ker.map ψ
  set P := unitaryCoverSylow J f hf hcard hfixed hJ
  have hstab : ∀ ω : unitaryIsotropicPoints J,
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) ω =
      (MulAction.stabilizer (Equiv.Perm (unitaryIsotropicPoints J)) ω).comap rho :=
    fun _ => Subgroup.ext fun _ => Iff.rfl
  have hαβ : α ≠ β := fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h).symm
  have hPα : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) α := by
    rw [hstab, hstabα]
    exact unitary_entire_root_fixes_first_coordinate J hJ
  have hT : MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) α ⊓
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) β =
        (hermitianTorusPSU J hJ).range := by
    rw [hstab, hstab, hstabα, hstabβ, ← hTeq, range_torusPSU]
  have : (V.subgroupOf (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).Characteristic :=
    center_characteristic J hJ
  have hΩ : 3 ≤ Nat.card (unitaryIsotropicPoints J) := by
    rw [hΩcard]
    have : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    have : 2 ≤ (2 ^ f) ^ 3 := by
      calc 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
        _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hψ : ∀ x : unitaryCoverRoot J hJ, ∃ z, ψ z = x := fun x => by
    obtain ⟨z, hz⟩ := x.2
    exact ⟨z, hz⟩
  have hVZ : ∀ v ∈ V, ∀ x ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      v * x = x * v := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_fst_eq_zero J hz w]
  have hPV : ∀ x y : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⧸
      V.subgroupOf (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    obtain ⟨z, hz⟩ := hψ x
    obtain ⟨w, hw⟩ := hψ y
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hz, ← hw, ← map_mul, ← map_inv]
    rw [hermitianUnipotentPSU_mem_center_iff]
    simp only [fst_mul, fst_inv]
    ring
  have hconj : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * ψ z * (hermitianTorusPSU J hJ k)⁻¹ =
        ψ (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  have hfst : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      (hermitianTorusAction J k z).1.1 = (unitaryCoverScalar J k : K) * z.1.1 := fun k z => by
    rw [hermitianTorusAction_fst, unitaryCoverScalar_val]
    ring
  obtain ⟨o, ho⟩ := exists_fst_eq J (2 ^ f) hcard hfixed 1
  refine regular_root_automorphism_layer_kernel hΩ hαβ P hPα
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPα).2 (by
      rw [hstab, hstabα]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (unitary_entire_root_fixes_first_coordinate J hJ)).1 hnormal))
    (fun ω ω' h1 h2 => (hreg ω ω' h1 h2).exists) V
    (Subgroup.map_le_range _ _) hVZ hPV (Or.inr ⟨?_, ?_⟩) γ hγU hγV hγUV
  ·
    intro t ht htriv
    rw [hT] at ht
    obtain ⟨k, rfl⟩ := ht
    have h1 := htriv _ ⟨o, rfl⟩
    rw [hconj, ← map_inv, ← map_mul, hermitianUnipotentPSU_mem_center_iff, fst_mul, fst_inv,
      hfst, ho, mul_one, neg_add_eq_zero] at h1
    have hk : k ∈ (unitaryCoverScalar J).ker := Units.ext h1.symm
    rw [unitaryCoverScalar_ker_eq_torus_ker J hJ] at hk
    exact hk
  ·
    intro ℓ hℓ
    rw [hT] at hℓ
    have hq : 2 < 2 ^ f := by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨⟨_, k, rfl⟩, hne, hnorm⟩ :=
      unitaryCoverScalarImage_exists_norm_one_ne_one J (2 ^ f) hcard hfixed hJ hq
    change (unitaryCoverScalar J k : K) ≠ 1 at hne
    change (unitaryCoverScalar J k : K) * J.conj (unitaryCoverScalar J k : K) = 1 at hnorm
    set t := hermitianTorusPSU J hJ k
    have htV : ∀ v ∈ V, t * v * t⁻¹ = v := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hconj]
      congr 1
      refine coord_ext ?_ ?_
      · rw [hfst, show z.1.1 = 0 from hz, mul_zero]
      · have h1 : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 := by
          rw [← unitaryCoverScalar_norm, hnorm]
        rw [hermitianTorusAction_snd, mul_assoc, h1, mul_one]
    choose w hw using exists_fst_eq J (2 ^ f) hcard hfixed
    let m : K → (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⧸
        V.subgroupOf (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      fun a => QuotientGroup.mk ⟨ψ (w a), ⟨w a, rfl⟩⟩
    have hm : ∀ (z : hermitianUnipotentCoord J),
        (QuotientGroup.mk ⟨ψ z, ⟨z, rfl⟩⟩ : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
          ⧸ V.subgroupOf (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) = m z.1.1 := by
      intro z
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← map_inv, ← map_mul]
      rw [hermitianUnipotentPSU_mem_center_iff, fst_mul, fst_inv, hw]
      ring
    have hmadd : ∀ a b : K, m (a + b) = m a * m b := fun a b => by
      rw [← hw a, ← hw b, ← fst_mul, ← hm, ← hm, ← hm, ← QuotientGroup.mk_mul]
      exact congrArg QuotientGroup.mk (Subtype.ext (map_mul ψ _ _))
    let b : K →+ Additive V :=
      { toFun := fun a => Additive.ofMul (ℓ (m a))
        map_zero' := by
          have h := hmadd 0 0
          rw [add_zero] at h
          have h' : ℓ (m 0) = 1 := by
            have := congrArg ℓ h
            rw [map_mul] at this
            exact left_eq_mul.1 this
          rw [h']
          rfl
        map_add' := fun a c => by
          rw [hmadd, map_mul]
          rfl }
    have hb : b = 0 := unitaryCoverScalarFixedAddHom_eq_zero (unitaryCoverScalar J k : K) hne b
      (fun a => by
        change Additive.ofMul (ℓ (m ((unitaryCoverScalar J k : K) * a))) = Additive.ofMul (ℓ (m a))
        congr 1
        have h := hℓ t ⟨k, rfl⟩ ⟨ψ (w a), ⟨w a, rfl⟩⟩
          ⟨ψ (hermitianTorusAction J k (w a)), ⟨_, rfl⟩⟩ (hconj k (w a)).symm
        rw [hm, hm, hfst, hw, htV _ (ℓ _).2] at h
        exact Subtype.ext h)
    refine MonoidHom.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨z, hz⟩ := hψ x
    have hx : x = ⟨ψ z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
    rw [hx, hm, MonoidHom.one_apply]
    exact congrArg Additive.toMul (DFunLike.congr_fun hb z.1.1)

theorem unitary_rank_one_Sylow_layer_kernel_of_mulEquiv {G : Type*} [Group G] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (Q : Sylow 2 G) (V : Subgroup G)
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup G)) (p := 2)).map (Q : Subgroup G).subtype)
    (γ : MulAut G) (hγQ : (Q : Subgroup G).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup G), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup G), γ = MulAut.conj b := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  obtain ⟨ε, hε⟩ := exists_mulEquiv_map_eq e (unitaryCoverSylow J f hf hcard hfixed hJ) Q
  subst hV
  rw [← hε] at hγQ hγV hγQV ⊢
  exact layerKernel_map ε (unitaryCoverRoot J hJ) (fun γ₀ h₁ h₂ h₃ =>
    unitaryRoot_layer_kernel J f hf hcard hfixed hJ γ₀ h₁
      (by rwa [map_omega₁_unitaryCoverRoot] at h₂) (by rwa [map_omega₁_unitaryCoverRoot] at h₃))
    γ hγQ hγV hγQV

theorem unitary_rank_one_Sylow_layer_kernel {f : ℕ} (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (Q : Sylow 2 (unitaryPSU h 3)) (V : Subgroup (unitaryPSU h 3))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup (unitaryPSU h 3))) (p := 2)).map
      (Q : Subgroup (unitaryPSU h 3)).subtype)
    (γ : MulAut (unitaryPSU h 3)) (hγQ : (Q : Subgroup (unitaryPSU h 3)).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup (unitaryPSU h 3)), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup (unitaryPSU h 3)), γ = MulAut.conj b := by
  have := h.finite
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  exact unitary_rank_one_Sylow_layer_kernel_of_mulEquiv (fieldDataHermitianForm h) f hf
    h.card_eq_sq (card_fixed_fieldDataHermitianForm h) rfl
    ((hypProjTransport h hR).symm.trans
      (UnitaryAutomorphism.hypPSUEquivPSU (J := fieldDataHermitianForm h) h (fun _ => rfl) rfl))
    Q V hV γ hγQ hγV hγQV

end CFSG.ProperTwoGeneratedCore.RootCenter

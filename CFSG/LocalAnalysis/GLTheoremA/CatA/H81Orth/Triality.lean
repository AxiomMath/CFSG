module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.AutModel
public import CFSG.ClassicalInvolution.Q3.Q3TLFam
public import CFSG.ClassicalInvolution.Q3.Q3MFODSimAt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Layer
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81Orth

open Matrix Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Q3.Q3T
open scoped Pointwise

section Eichler

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_eichler_stabilizes (h2 : (2 : K) ≠ 0) {S : Submodule K V}
    (hS : ∀ x ∈ S, Q x = 0) {a b : V} (hQa : Q a = 0) (hab : polar Q a b = 0) (hQb : Q b ≠ 0)
    (h1 : ∀ x ∈ S, eichler Q a b x ∈ S) (h2S : ∀ x ∈ S, eichler Q a ((2 : K) • b) x ∈ S)
    {x : V} (hx : x ∈ S) : polar Q x a = 0 := by
  have hab2 : polar Q a ((2 : K) • b) = 0 := by rw [polar_smul_right, hab, smul_zero]
  set c := polar Q x a with hc
  have hy1 : c • b - (polar Q x b + Q b * c) • a ∈ S := by
    have := S.sub_mem (h1 x hx) hx
    rw [eichler_apply hQa hab] at this
    convert this using 1
    abel
  have hy2 : c • ((2 : K) • b) - (polar Q x ((2 : K) • b) + Q ((2 : K) • b) * c) • a ∈ S := by
    have := S.sub_mem (h2S x hx) hx
    rw [eichler_apply hQa hab2] at this
    convert this using 1
    abel
  have h3 : (2 * Q b * c) • a ∈ S := by
    have := S.sub_mem (S.smul_mem (2 : K) hy1) hy2
    convert this using 1
    rw [polar_smul_right, QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    module
  by_contra hc0
  have ha : a ∈ S := by
    have h4 : (2 * Q b * c) ≠ 0 := mul_ne_zero (mul_ne_zero h2 hQb) hc0
    have := S.smul_mem (2 * Q b * c)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ h4, one_smul] at this
  apply hc0
  rw [hc, QuadraticMap.polar, hS _ (S.add_mem hx ha), hS x hx, hS a ha]
  ring

end Eichler

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

variable {K : Type} [Field K] [Finite K]

theorem exists_of_fixFam_solid_Xstar
    {H : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K)))}
    (h : FixFam (conjugacyFamily (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
      (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.Xstar 4 K (by omega)))) H) :
    ∃ S ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularSubspaces (quadPlus 4 K) 4,
      H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) S := by
  obtain ⟨M, ⟨u, rfl⟩, hHM⟩ := h
  change H ≤ (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K)
    (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.Xstar 4 K (by omega))).map
      (MulAut.conj u).toMonoidHom at hHM
  rw [statedProjectiveSubspaceStabilizer_map_conj] at hHM
  refine ⟨_, ?_, hHM⟩
  obtain ⟨U, rfl⟩ := QuotientGroup.mk'_surjective _ u
  rw [statedProjectiveSubspaceAction_mk_apply]
  have hX : CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.Xstar 4 K (by omega) ∈
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularSubspaces (quadPlus 4 K) 4 := by
    obtain ⟨hd, hs⟩ := Xstar_data (K := K) (n := 4) (by omega)
    exact ⟨hd, fun v hv => by rw [coe_quadPlus]; exact hs v hv⟩
  exact CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.map_mem_singularSubspaces
    (toLinEquiv_mem_orthogonalGroup U.2) hX

theorem exists_similarity_plus_four_of_family {ℓ f : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ f) (hK : Nat.card K = ℓ ^ f)
    (β : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
    (hβ : β • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K)) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) K) (φ : K ≃+* K) (μ : Kˣ),
      (∀ v, quadPlus 4 K ((A : Matrix _ _ K) *ᵥ fun i => φ (v i)) = μ * φ (quadPlus 4 K v)) ∧
      ∀ x : StatedOmega (StatedQuadPlus 4 K), ∃ y : StatedOmega (StatedQuadPlus 4 K),
        (y : GL (Fin 4 ⊕ Fin 4) K) = A * glFieldEquiv _ φ (x : GL _ K) * A⁻¹ ∧
          β (QuotientGroup.mk x) = QuotientGroup.mk y := by
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hγ : MulAut.congr (plusCoordinateEquiv 4 K) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rw [← coordinate_plus_family_eq_matrixImage hT _ hK (MulEquiv.refl _),
      mem_projectivePointFamilyAut_iff]
    have key := familyTransport_automorphism (plusCoordinateEquiv 4 K)
      (statedPointFamily (coe_quadPlus 4 K)) β
    rw [hβ, plusCoordinate_pointFamily] at key
    exact key.symm
  exact CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_of_mem_image
    (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K) β hγ

end Model

section Witt

variable {K : Type} [Field K] [Finite K]

theorem exists_two_hypPairs_and_nonsingular {U : Type} [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (hodd : Odd (Nat.card K)) (QU : QuadraticForm K U)
    (hQU : (polarBilin QU).Nondegenerate) (hdim : 5 ≤ finrank K U) :
    ∃ (P₀ P₁ : HypPair QU) (z : U), P₀.Orth P₁ ∧ z ∈ P₀.perp ∧ z ∈ P₁.perp ∧ QU z ≠ 0 := by
  obtain ⟨m, P, A, horth, -, -, hAperp, -, -, hani, hA2, hdimU, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.finite_odd_quadratic_low_Witt_dimension_bound
      hodd QU hQU).2.1
  have hm : 2 ≤ m := by omega
  have h01 : (P ⟨0, by omega⟩).Orth (P ⟨1, by omega⟩) := horth _ _ (by simp [Fin.ext_iff])
  by_cases hm3 : 3 ≤ m
  · have h02 : (P ⟨0, by omega⟩).Orth (P ⟨2, by omega⟩) := horth _ _ (by simp [Fin.ext_iff])
    have h12 : (P ⟨1, by omega⟩).Orth (P ⟨2, by omega⟩) := horth _ _ (by simp [Fin.ext_iff])
    refine ⟨P ⟨0, by omega⟩, P ⟨1, by omega⟩, (P ⟨2, by omega⟩).e + (P ⟨2, by omega⟩).f, h01,
      ?_, ?_, ?_⟩
    · rw [HypPair.mem_perp, polar_add_right, polar_add_right, h02.ee, h02.ef, h02.fe, h02.ff]
      simp
    · rw [HypPair.mem_perp, polar_add_right, polar_add_right, h12.ee, h12.ef, h12.fe, h12.ff]
      simp
    · rw [QuadraticMap.map_add QU, (P ⟨2, by omega⟩).Q_e, (P ⟨2, by omega⟩).Q_f,
        (P ⟨2, by omega⟩).polar_ef]
      norm_num
  · have hApos : 0 < finrank K A := by omega
    obtain ⟨z, hzA, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (show A ≠ ⊥ from fun h => by rw [h, finrank_bot] at hApos; exact absurd hApos (lt_irrefl 0))
    have hzperp : z ∈ ⨅ i, (P i).perp := hAperp ▸ hzA
    rw [Submodule.mem_iInf] at hzperp
    refine ⟨P ⟨0, by omega⟩, P ⟨1, by omega⟩, z, h01, hzperp _, hzperp _, fun h => hz0 ?_⟩
    have := hani ⟨z, hzA⟩ h
    exact congrArg Subtype.val this

end Witt

section Fix

open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

variable {K : Type} [Field K] [Finite K]

theorem smul_statedPointFamily_eq_of_fixes {ℓ f : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus 4 ℓ f) (hK : Nat.card K = ℓ ^ f)
    (hK2 : ringChar K ≠ 2) {p : ℕ} {y : ↥(orthDerived (quadPlus 4 K))}
    (hy : OddOrderIsometry (quadPlus 4 K) p (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)))
    (hW : 5 ≤ finrank K (fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))))
    (α : MulAut (ProjOrthDerived (quadPlus 4 K)))
    (hαJ : ∀ j ∈ fixedComponentImage (quadPlus 4 K)
      (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)), α j = j) :
    MulAut.congr (statedProjOrthEquiv (coe_quadPlus 4 K)).symm α •
        statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  classical
  have hodd : Odd (Nat.card K) := by
    have := Fintype.ofFinite K
    by_contra h
    apply hK2
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
    exact Nat.not_odd_iff.mp h
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨P₀, P₁, z, h01, hzP₀, hzP₁, hz0⟩ :=
    exists_two_hypPairs_and_nonsingular hodd _ hy.polarBilin_fixed_nondegenerate hW
  rw [HypPair.mem_perp] at hzP₀ hzP₁
  have hpol : ∀ a b : fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
      polar (quadPlus 4 K) (a : Fin 4 ⊕ Fin 4 → K) (b : Fin 4 ⊕ Fin 4 → K) =
        polar ((quadPlus 4 K).comp (fixedSpace
          (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).subtype) a b :=
    fun a b => (polar_comp_subtype _ a b).symm
  have hQu : quadPlus 4 K (P₀.e : Fin 4 ⊕ Fin 4 → K) = 0 := P₀.Q_e
  have hu0 : (P₀.e : Fin 4 ⊕ Fin 4 → K) ≠ 0 := by
    intro h
    have := P₀.polar_ef
    rw [← hpol, h, polar_zero_left] at this
    exact zero_ne_one this
  set e := statedProjOrthEquiv (coe_quadPlus 4 K) with he
  set β := MulAut.congr e.symm α with hβdef
  set H := (fixedComponentImage (quadPlus 4 K)
      (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))).map e.symm.toMonoidHom ⊓
    statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (K ∙ (P₀.e : Fin 4 ⊕ Fin 4 → K))
    with hH
  have hβH : ∀ t ∈ H, β t = t := by
    rintro t ⟨⟨j, hj, rfl⟩, -⟩
    show e.symm (α (e (e.symm j))) = e.symm j
    rw [MulEquiv.apply_symm_apply, hαJ j hj]
  have hHmap : H.map β.toMonoidHom = H := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      show β s ∈ H
      rw [hβH s hs]
      exact hs
    · intro ht
      exact ⟨t, ht, hβH t ht⟩
  have hFH : FixFam (statedPointFamily (coe_quadPlus 4 K)) H :=
    fixFam_point_of_le hu0 hQu inf_le_right
  have hβFH : FixFam (β • statedPointFamily (coe_quadPlus 4 K)) H :=
    (fixFam_smul_iff β hHmap _).mpr hFH
  have hstab : ∀ a b : Fin 4 ⊕ Fin 4 → K,
      a ∈ fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) →
      b ∈ fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) →
      polar (quadPlus 4 K) a b = 0 → polar (quadPlus 4 K) (P₀.e : Fin 4 ⊕ Fin 4 → K) a = 0 →
      polar (quadPlus 4 K) (P₀.e : Fin 4 ⊕ Fin 4 → K) b = 0 →
      ∀ S : Submodule K (Fin 4 ⊕ Fin 4 → K),
        H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) S →
          ∀ v ∈ S, eichler (quadPlus 4 K) a b v ∈ S := by
    intro a b ha hb hab hua hub S hS v hv
    have hES : eichler (quadPlus 4 K) a b ∈ supportedFixedDerived (quadPlus 4 K)
        (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
      eichler_mem_supportedFixedDerived hy hK2 ha hb hab
    set Eω : ↥(orthDerived (quadPlus 4 K)) :=
      ⟨eichler (quadPlus 4 K) a b, hy.supportedFixedDerived_le_orthDerived hES⟩ with hEω
    have hmat : toLinEquiv (Fin 4 ⊕ Fin 4) K
        ((statedOmegaOrthEquiv (coe_quadPlus 4 K)).symm Eω : GL (Fin 4 ⊕ Fin 4) K) =
        eichler (quadPlus 4 K) a b := toLinEquiv_statedOmegaOrthEquiv_symm (coe_quadPlus 4 K) Eω
    have hEu : eichler (quadPlus 4 K) a b (P₀.e : Fin 4 ⊕ Fin 4 → K) = P₀.e :=
      eichler_apply_of_polar_eq_zero hua hub
    have htH : e.symm (projT (quadPlus 4 K) Eω) ∈ H := by
      refine Subgroup.mem_inf.mpr
        ⟨⟨projT (quadPlus 4 K) Eω, ⟨Eω, Subgroup.mem_subgroupOf.mpr hES, rfl⟩, rfl⟩, ?_⟩
      rw [statedProjOrthEquiv_symm_projT, mk_mem_stabilizer_iff, hmat, Submodule.map_span,
        Set.image_singleton, LinearEquiv.coe_coe, hEu]
    have h1 := hS htH
    rw [statedProjOrthEquiv_symm_projT, mk_mem_stabilizer_iff, hmat] at h1
    rw [← h1]
    exact ⟨v, hv, rfl⟩
  have key : ∀ S ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularSubspaces
      (quadPlus 4 K) 4, ¬ H ≤ statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) S := by
    intro S hS hHS
    have hSs : ∀ v ∈ S, quadPlus 4 K v = 0 := hS.2
    have hz2W : (2 : K) • (z : Fin 4 ⊕ Fin 4 → K) ∈
        fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := Submodule.smul_mem _ _ z.2
    have hQz : quadPlus 4 K (z : Fin 4 ⊕ Fin 4 → K) ≠ 0 := hz0
    have huz : polar (quadPlus 4 K) (P₀.e : Fin 4 ⊕ Fin 4 → K) (z : Fin 4 ⊕ Fin 4 → K) = 0 := by
      rw [hpol]; exact hzP₀.1
    have huz2 : polar (quadPlus 4 K) (P₀.e : Fin 4 ⊕ Fin 4 → K)
        ((2 : K) • (z : Fin 4 ⊕ Fin 4 → K)) = 0 := by
      rw [polar_smul_right, huz, smul_zero]
    have horth' : ∀ a : fixedSpace (y : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
        quadPlus 4 K (a : Fin 4 ⊕ Fin 4 → K) = 0 →
        polar (quadPlus 4 K) (a : Fin 4 ⊕ Fin 4 → K) (z : Fin 4 ⊕ Fin 4 → K) = 0 →
        polar (quadPlus 4 K) (P₀.e : Fin 4 ⊕ Fin 4 → K) (a : Fin 4 ⊕ Fin 4 → K) = 0 →
        (a : Fin 4 ⊕ Fin 4 → K) ∈ S := by
      intro a hQa haz hua
      have haz2 : polar (quadPlus 4 K) (a : Fin 4 ⊕ Fin 4 → K)
          ((2 : K) • (z : Fin 4 ⊕ Fin 4 → K)) = 0 := by
        rw [polar_smul_right, haz, smul_zero]
      refine CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_of_forall_polar_eq_zero hS
        fun v hv => ?_
      rw [polar_comm]
      exact polar_eq_zero_of_eichler_stabilizes h2 hSs hQa haz hQz
        (hstab _ _ a.2 z.2 haz hua huz S hHS) (hstab _ _ a.2 hz2W haz2 hua huz2 S hHS) hv
    have he₁ := horth' P₁.e P₁.Q_e (by rw [hpol]; exact hzP₁.1) (by rw [hpol]; exact h01.ee)
    have hf₁ := horth' P₁.f P₁.Q_f (by rw [hpol]; exact hzP₁.2) (by rw [hpol]; exact h01.ef)
    have h1 := P₁.polar_ef
    rw [← hpol, QuadraticMap.polar, hSs _ (S.add_mem he₁ hf₁), hSs _ he₁, hSs _ hf₁] at h1
    norm_num at h1
  have hT : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4 ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have horbit :=
    ((orthogonal_geometry_plus_point_family_orbit hT hK (MulEquiv.refl _)).2.2.1 rfl).1
      (MulAction.mem_orbit _ β)
  rcases horbit with h | h | h
  · exact h
  · exfalso
    rw [h] at hβFH
    obtain ⟨S, hS, hHS⟩ := exists_of_fixFam_solid hβFH
    exact key S hS hHS
  · exfalso
    rw [Set.mem_singleton_iff] at h
    rw [h] at hβFH
    obtain ⟨S, hS, hHS⟩ := exists_of_fixFam_solid_Xstar hβFH
    exact key S hS hHS

end Fix

end CFSG.LocalAnalysis.GLTheoremA.H81Orth

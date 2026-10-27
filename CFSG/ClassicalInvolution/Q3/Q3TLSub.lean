module

public import CFSG.ClassicalInvolution.Q3.Q3TLBlock
public import CFSG.ClassicalInvolution.Q3.Q3TLLin
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.Open (IsSubnormal)
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem conj_comm_of_central {G : Type*} [Group G] {k g h s : G} (hs : ∀ y, s * y = y * s)
    (hk : k * g * k⁻¹ = s * g) (hh : h * g = g * h) :
    k * h * k⁻¹ * g = g * (k * h * k⁻¹) := by
  have hg : g = s⁻¹ * (k * g * k⁻¹) := by rw [hk, inv_mul_cancel_left]
  have hs' : ∀ y, s⁻¹ * y = y * s⁻¹ := fun y => by
    calc s⁻¹ * y = s⁻¹ * (y * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * y) * s⁻¹ := by rw [hs]
      _ = y * s⁻¹ := by group
  calc k * h * k⁻¹ * g = k * h * k⁻¹ * (s⁻¹ * (k * g * k⁻¹)) := by rw [← hg]
    _ = s⁻¹ * (k * (h * g) * k⁻¹) := by
      rw [← mul_assoc, ← hs' (k * h * k⁻¹)]
      group
    _ = s⁻¹ * (k * g * k⁻¹) * (k * h * k⁻¹) := by rw [hh]; group
    _ = g * (k * h * k⁻¹) := by rw [← hg]

variable {K : Type} [Field K]

theorem orthExtend_comm {G : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hc : IsCompl (plusSp G) (minusSp G)) (φ : plusSp G ≃ₗ[K] plusSp G) :
    orthExtend hc φ * G = G * orthExtend hc φ := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl' hc x
  have h1 := orthExtend_apply hc φ ⟨u, hu⟩ ⟨w, hw⟩
  have h2 := orthExtend_apply hc φ ⟨u, hu⟩ (-⟨w, hw⟩)
  simp only [Submodule.coe_neg] at h1 h2
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, mem_plusSp.mp hu, mem_minusSp.mp hw,
    ← sub_eq_add_neg, sub_eq_add_neg, h2, h1, map_add, mem_plusSp.mp (φ ⟨u, hu⟩).2,
    mem_minusSp.mp hw]

omit [Field K] in
theorem normal_map_centralizer {E P : Type*} [Group E] [Group P] (π : E →* P)
    (hπ : Function.Surjective π) (hker : ∀ k ∈ π.ker, ∀ y, k * y = y * k) (x : E) :
    ((Subgroup.centralizer ({x} : Set E)).map π).subgroupOf
      (Subgroup.centralizer ({π x} : Set P)) |>.Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_le_iff_le_comap.mpr fun h hh => by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hh])]
  rintro _ d ⟨h, hh, rfl⟩ hd
  obtain ⟨k, rfl⟩ := hπ d
  have hs : k * x * k⁻¹ * x⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      (Subgroup.mem_centralizer_singleton_iff.mp hd)]
    group
  have hk : k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
  refine ⟨k * h * k⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by
    rw [map_mul, map_mul, map_inv]⟩
  exact conj_comm_of_central (hker _ hs) hk (Subgroup.mem_centralizer_singleton_iff.mp hh)

theorem ePHom_toLinEquiv (h : StatedOmega (StatedQuadPlus 4 K)) :
    ePHom K ⟨toLinEquiv _ K h.val, toLinEquiv_mem_elementaryGroup h.2⟩ = QuotientGroup.mk h := by
  rw [ePHom_apply]
  congr 1
  exact Subtype.ext ((toLinEquiv _ K).symm_apply_apply h.val)

section Chain

variable (g : StatedOmega (StatedQuadPlus 4 K))
  (hc : IsCompl (plusSp (toLinEquiv _ K g.val)) (minusSp (toLinEquiv _ K g.val)))
  (horth : ∀ u ∈ plusSp (toLinEquiv _ K g.val), ∀ w ∈ minusSp (toLinEquiv _ K g.val),
    polar (quadPlus 4 K) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 K).comp (plusSp (toLinEquiv _ K g.val)).subtype)}
  (h : P₁.Orth P₂) (hdim : finrank K (plusSp (toLinEquiv _ K g.val)) = 4)

@[expose] noncomputable def blockP :
    elementaryGroup ((quadPlus 4 K).comp (plusSp (toLinEquiv _ K g.val)).subtype) →*
      StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
  (ePHom K).comp (blockHom (quadPlus 4 K) hc horth)

include hc horth h hdim in
theorem range_thetaL_sup_eq_top :
    ((thetaL h hdim).codRestrict _ (thetaL_mem_elementaryGroup h hdim)).range ⊔
      ((thetaR h hdim).codRestrict _ (thetaR_mem_elementaryGroup h hdim)).range = ⊤ := by
  have hQp := nondegenerate_comp_subtype (nondegenerate_polarBilin_quadPlus 4 K) hc horth
  set Ep := elementaryGroup ((quadPlus 4 K).comp (plusSp (toLinEquiv _ K g.val)).subtype)
  have e1 : Ep.subtype.comp ((thetaL h hdim).codRestrict _ (thetaL_mem_elementaryGroup h hdim)) =
      thetaL h hdim := MonoidHom.ext fun _ => rfl
  have e2 : Ep.subtype.comp ((thetaR h hdim).codRestrict _ (thetaR_mem_elementaryGroup h hdim)) =
      thetaR h hdim := MonoidHom.ext fun _ => rfl
  apply Subgroup.map_injective (Subgroup.subtype_injective _)
  calc _ = (thetaL h hdim).range ⊔ (thetaR h hdim).range := by
        rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range, e1, e2]
    _ = Ep := (elementaryGroup_eq_sup h hdim hQp).symm
    _ = (⊤ : Subgroup Ep).map Ep.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem range_blockP_eq : (blockP g hc horth).range =
    (rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range := by
  rw [MonoidHom.range_eq_map, ← range_thetaL_sup_eq_top g hc horth h hdim, Subgroup.map_sup,
    MonoidHom.map_range, MonoidHom.map_range]
  rfl

@[expose] noncomputable def cZero : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 K))) :=
  (Subgroup.centralizer ({g} : Set (StatedOmega (StatedQuadPlus 4 K)))).map (QuotientGroup.mk' _)

theorem range_blockP_le_cZero : (blockP g hc horth).range ≤ cZero g := by
  rintro _ ⟨φ, rfl⟩
  refine ⟨⟨(toLinEquiv _ K).symm (blockHom (quadPlus 4 K) hc horth φ),
    symm_mem_statedOmega (blockHom (quadPlus 4 K) hc horth φ).2⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
  apply Subtype.ext
  apply (toLinEquiv _ K).injective
  simp only [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply, coe_blockHom]
  exact orthExtend_comm hc _

theorem blockP_normal_cZero : ((blockP g hc horth).range.subgroupOf (cZero g)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (range_blockP_le_cZero g hc horth)]
  rintro _ _ ⟨φ, rfl⟩ ⟨k, hk, rfl⟩
  have hkg := congrArg (fun y : StatedOmega (StatedQuadPlus 4 K) => toLinEquiv _ K y.val)
    (Subgroup.mem_centralizer_singleton_iff.mp hk)
  simp only [Subgroup.coe_mul, map_mul] at hkg
  have hW := mem_stabSub_plusSp hkg
  have hW' := mem_stabSub_minusSp hkg
  have hmem := Subgroup.mem_map_of_mem (ePHom K) (conj_blockHom_mem_range hc horth
    (b := ⟨_, toLinEquiv_mem_elementaryGroup k.2⟩) hW hW' ⟨φ, rfl⟩)
  rw [map_mul, map_mul, map_inv, ePHom_toLinEquiv] at hmem
  have hrange : (blockP g hc horth).range =
      (blockHom (quadPlus 4 K) hc horth).range.map (ePHom K) :=
    MonoidHom.range_comp _ _
  rw [hrange]
  exact hmem

theorem mk_ker_comm : ∀ k ∈ (QuotientGroup.mk' ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
    (StatedOmega (StatedQuadPlus 4 K)))).ker, ∀ y, k * y = y * k := by
  intro k hk y
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hk
  obtain ⟨c, hcs⟩ := mem_scalars.mp hk
  apply Subtype.ext
  apply (toLinEquiv _ K).injective
  refine LinearEquiv.ext fun v => ?_
  simp only [Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, hcs, map_smul]

theorem cZero_normal : ((cZero g).subgroupOf (Subgroup.centralizer
    ({(QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))} : Set _))).Normal :=
  normal_map_centralizer _ (QuotientGroup.mk'_surjective _) mk_ker_comm g

theorem cZero_le : cZero g ≤ Subgroup.centralizer
    ({(QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))} : Set _) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (QuotientGroup.mk (k * g) : StatedProj (StatedOmega (StatedQuadPlus 4 K))) =
    QuotientGroup.mk (g * k)
  rw [Subgroup.mem_centralizer_singleton_iff.mp hk]

theorem rhoL_normal : ((rhoL hc horth h hdim).range.subgroupOf
    ((rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
  refine sup_le Subgroup.le_normalizer ?_
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A, by rw [← rhoL_rhoR_comm, mul_inv_cancel_right]⟩
  · rintro ⟨A, hA⟩
    refine ⟨A, mul_left_cancel (a := rhoR hc horth h hdim B) ?_⟩
    rw [← rhoL_rhoR_comm, hA]
    group

theorem rhoR_normal : ((rhoR hc horth h hdim).range.subgroupOf
    ((rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
  refine sup_le ?_ Subgroup.le_normalizer
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨B, by rw [rhoL_rhoR_comm, mul_inv_cancel_right]⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, mul_left_cancel (a := rhoL hc horth h hdim A) ?_⟩
    rw [rhoL_rhoR_comm, hB]
    group

theorem isSubnormal_block : IsSubnormal ((rhoL hc horth h hdim).range ⊔
    (rhoR hc horth h hdim).range) (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))} : Set _)) := by
  rw [← range_blockP_eq g hc horth h hdim]
  exact IsSubnormal.step (range_blockP_le_cZero g hc horth) (blockP_normal_cZero g hc horth)
    (isSubnormal_of_normal_subgroupOf (cZero_le g) (cZero_normal g))

theorem isSubnormal_rhoL_range : IsSubnormal (rhoL hc horth h hdim).range (Subgroup.centralizer
    ({(QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))} : Set _)) :=
  IsSubnormal.step le_sup_left (rhoL_normal g hc horth h hdim)
    (isSubnormal_block g hc horth h hdim)

theorem isSubnormal_rhoR_range : IsSubnormal (rhoR hc horth h hdim).range (Subgroup.centralizer
    ({(QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K)))} : Set _)) :=
  IsSubnormal.step le_sup_right (rhoR_normal g hc horth h hdim)
    (isSubnormal_block g hc horth h hdim)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3T

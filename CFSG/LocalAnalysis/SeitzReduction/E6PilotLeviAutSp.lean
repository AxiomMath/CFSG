module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAutBasic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Ree (ReeTag)

theorem isAutConj_spRootSL2 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → ℤ) : IsAutConj (F4Pilot.spRootSL2 n K v) := by
  intro α
  obtain ⟨s, σ, h⟩ := F4Pilot.exists_eq_conj_mul_fieldSp hn α
  refine ⟨s, ?_⟩
  have e : (F4Pilot.spRootSL2 n K v).map α.toMonoidHom =
      ((F4Pilot.spRootSL2 n K v).map (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp
        n K σ).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [h g, MulAut.conj_apply]
  rw [e, F4Pilot.map_fieldSp_spRootSL2]

local instance e6PilotLeviAutSpNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance e6PilotLeviAutSpNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Model


variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def yLeviSpHom : ↥(StatedSp 3 K) →* ModGL .E6 K :=
  (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom.comp
    ((yGamma K).subtype.comp ((yPsi K).symm.toMonoidHom.comp
      ((F4Pilot.graphAutF4 K).toMonoidHom.comp (F4Pilot.c3LeviHom K))))

theorem yLeviSpHom_injective : Function.Injective (yLeviSpHom K) :=
  (MulAut.conj _).injective.comp ((yGamma K).subtype_injective.comp
    ((yPsi K).symm.injective.comp ((F4Pilot.graphAutF4 K).injective.comp
      F4Pilot.c3LeviHom_injective)))

theorem range_yLeviSpHom : (yLeviSpHom K).range = yLeviGL K := by
  have hid : (((yLeviF4 K).subgroupOf (yGamma K)).map (yPsi K).toMonoidHom).map
      (yPsi K).symm.toMonoidHom = (yLeviF4 K).subgroupOf (yGamma K) := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id _
    ext x
    simp
  rw [yLeviSpHom, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_comp, F4Pilot.range_c3LeviHom, F4Pilot.map_graphAutF4_C3Levi (K := K),
    ← map_yPsi_yLeviF4, hid, subgroupOf_map_subtype, inf_of_le_left yLeviF4_le_yGamma,
    yLeviGL_eq_map_yLeviF4]

theorem yLeviSpHom_mem_adjointGroup (g : ↥(StatedSp 3 K)) :
    yLeviSpHom K g ∈ adjointGroup .E6 K :=
  yLeviGL_le_adjointGroup (range_yLeviSpHom (K := K) ▸ ⟨g, rfl⟩)

variable (K) in
@[expose] noncomputable def yLeviSpEquiv : ↥(StatedSp 3 K) ≃* yLevi K :=
  (MonoidHom.ofInjective (f := (yLeviSpHom K).codRestrict (adjointGroup .E6 K)
      yLeviSpHom_mem_adjointGroup) fun _ _ h => yLeviSpHom_injective (congrArg Subtype.val h)).trans
    (MulEquiv.subgroupCongr (by
      apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
      rw [yLevi, subgroupOf_map_subtype, inf_of_le_left yLeviGL_le_adjointGroup,
        ← range_yLeviSpHom, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
      rfl))

theorem subtype_comp_yLeviSpEquiv :
    ((adjointGroup .E6 K).subtype.comp (yLevi K).subtype).comp (yLeviSpEquiv K).toMonoidHom =
      yLeviSpHom K := by
  ext g
  rfl

theorem map_yPsi_symm_rootSubgroup_single_one :
    (((rootSubgroup .F4 K (Pi.single 1 1)).subgroupOf (adjointGroup .F4 K)).map
      (yPsi K).symm.toMonoidHom).map (yGamma K).subtype = rootSubgroup .E6 K (Pi.single 3 1) := by
  have hS : Set.range (pinnedX .F4 K (Pi.single (1 : Fin Tag.F4.rank) 1)) ⊆
      adjointGroup .F4 K := by
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ c
  have hval : ∀ c : K, (yPsi K).symm ⟨xUnit .F4 K 1 c, xUnit_mem_adjointGroup 1 c⟩ =
      ⟨f4OrbitXUnit K 1 c, f4OrbitXUnit_mem 1 c⟩ := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (coe_yPsi_f4OrbitXUnit 1 c).symm
  rw [rootSubgroup, closure_subgroupOf_eq hS, MonoidHom.map_closure, MonoidHom.map_closure,
    rootSubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, ⟨c, hc⟩, rfl⟩, rfl⟩
    have hx : x = ⟨xUnit .F4 K 1 c, xUnit_mem_adjointGroup 1 c⟩ :=
      Subtype.ext (hc.symm.trans (by rw [pinnedX_single]))
    subst hx
    refine ⟨c, ?_⟩
    change pinnedX .E6 K (Pi.single 3 1) c =
      (((yPsi K).symm ⟨xUnit .F4 K 1 c, xUnit_mem_adjointGroup 1 c⟩ : yGamma K) : ModGL .E6 K)
    rw [hval, pinnedX_single]
    exact (f4OrbitXUnit_one c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨⟨xUnit .F4 K 1 c, xUnit_mem_adjointGroup 1 c⟩, ⟨c, by rw [pinnedX_single]; rfl⟩,
      rfl⟩, ?_⟩
    change (((yPsi K).symm ⟨xUnit .F4 K 1 c, xUnit_mem_adjointGroup 1 c⟩ : yGamma K) :
      ModGL .E6 K) = pinnedX .E6 K (Pi.single 3 1) c
    rw [hval, pinnedX_single]
    exact f4OrbitXUnit_one c

theorem map_yPsi_symm_rootSubgroup_neg_single_one :
    (((rootSubgroup .F4 K (-Pi.single 1 1)).subgroupOf (adjointGroup .F4 K)).map
      (yPsi K).symm.toMonoidHom).map (yGamma K).subtype =
        rootSubgroup .E6 K (-Pi.single 3 1) := by
  have hS : Set.range (pinnedX .F4 K (-Pi.single (1 : Fin Tag.F4.rank) 1)) ⊆
      adjointGroup .F4 K := by
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ c
  have hval : ∀ c : K, (yPsi K).symm ⟨yUnit .F4 K 1 c, yUnit_mem_adjointGroup 1 c⟩ =
      ⟨f4OrbitYUnit K 1 c, f4OrbitYUnit_mem 1 c⟩ := fun c => by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (coe_yPsi_f4OrbitYUnit 1 c).symm
  rw [rootSubgroup, closure_subgroupOf_eq hS, MonoidHom.map_closure, MonoidHom.map_closure,
    rootSubgroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨x, ⟨c, hc⟩, rfl⟩, rfl⟩
    have hx : x = ⟨yUnit .F4 K 1 c, yUnit_mem_adjointGroup 1 c⟩ :=
      Subtype.ext (hc.symm.trans (by rw [pinnedX_neg_single]))
    subst hx
    refine ⟨c, ?_⟩
    change pinnedX .E6 K (-Pi.single 3 1) c =
      (((yPsi K).symm ⟨yUnit .F4 K 1 c, yUnit_mem_adjointGroup 1 c⟩ : yGamma K) : ModGL .E6 K)
    rw [hval, pinnedX_neg_single]
    exact (f4OrbitYUnit_one c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨⟨yUnit .F4 K 1 c, yUnit_mem_adjointGroup 1 c⟩,
      ⟨c, by rw [pinnedX_neg_single]; rfl⟩, rfl⟩, ?_⟩
    change (((yPsi K).symm ⟨yUnit .F4 K 1 c, yUnit_mem_adjointGroup 1 c⟩ : yGamma K) :
      ModGL .E6 K) = pinnedX .E6 K (-Pi.single 3 1) c
    rw [hval, pinnedX_neg_single]
    exact f4OrbitYUnit_one c

theorem map_yLeviSpHom_spRootSL2 {v : Fin 3 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 3) ∅)
    (hvβ : F4Pilot.psiF4 (c3ToF4 v) = Pi.single 1 1) :
    (F4Pilot.spRootSL2 3 K v).map (yLeviSpHom K) =
      (rootSubgroup .E6 K (Pi.single 3 1) ⊔ rootSubgroup .E6 K (-Pi.single 3 1)).map
        (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).toMonoidHom := by
  have hβ : IsRoot .F4 (Pi.single (1 : Fin Tag.F4.rank) 1) := isRoot_single .F4 1
  have hγ : IsRoot .F4 (c3ToF4 v) := isRoot_c3ToF4 hv
  rw [yLeviSpHom, ← Subgroup.map_map, ← Subgroup.map_map, ← Subgroup.map_map,
    ← Subgroup.map_map]
  congr 1
  rw [F4Pilot.spRootSL2, Subgroup.map_sup, F4Pilot.map_c3LeviHom_rootGroup hv,
    F4Pilot.map_c3LeviHom_rootGroup (F4Pilot.neg_mem_roots_cartanC hv), map_neg,
    Subgroup.map_sup, F4Pilot.map_graphAutF4_rootGroup (K := K) hγ,
    F4Pilot.map_graphAutF4_rootGroup (K := K) (IsRoot.neg hγ), F4Pilot.psiF4_neg hγ, hvβ,
    F4Pilot.rootGroup_eq_subgroupOf hβ, F4Pilot.rootGroup_eq_subgroupOf (IsRoot.neg hβ),
    Subgroup.map_sup, Subgroup.map_sup, map_yPsi_symm_rootSubgroup_single_one,
    map_yPsi_symm_rootSubgroup_neg_single_one]

theorem wordProd_smul_single_three :
    (coxeterSystem .E6).wordProd ([3, 1, 2, 4] : List (Fin Tag.E6.rank)) •
      (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) = e6RepPreHigh 1 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  decide

variable (K) in
@[expose] noncomputable def yWeylN : ModGL .E6 K :=
  (([3, 1, 2, 4] : List (Fin Tag.E6.rank)).map fun i => weylElt .E6 K i 1).prod

theorem yWeylN_mem_yLeviF4 : yWeylN K ∈ yLeviF4 K := by
  have h3 := weylElt_mem_yLeviF4 (K := K) (j := 3) (Or.inr rfl)
  have h1 := weylElt_mem_yLeviF4 (K := K) (j := 1) (Or.inl rfl)
  have h24 := weylElt_two_mul_weylElt_four_mem_yLeviF4 (K := K)
  simp only [yWeylN, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact mul_mem h3 (mul_mem h1 h24)

theorem highRootSL2_eq_map_conj_yWeylN :
    EPilot.highRootSL2 .E6 K =
      (rootSubgroup .E6 K (Pi.single 3 1) ⊔ rootSubgroup .E6 K (-Pi.single 3 1)).map
        (MulAut.conj ((e6RepConj K 1 : ModGL .E6 K) * yWeylN K)).toMonoidHom := by
  have h3 : IsRoot .E6 (Pi.single (3 : Fin Tag.E6.rank) 1) := isRoot_single .E6 3
  have hρ : IsRoot .E6 (e6RepPreHigh 1) := by
    rw [← wordProd_smul_single_three]
    exact IsRoot.smul h3 _
  rw [← map_conj_map_conj_eq_conj_mul, Subgroup.map_sup, yWeylN,
    map_conj_prod_weylElt_rootSubgroup K _ h3,
    map_conj_prod_weylElt_rootSubgroup K _ (IsRoot.neg h3),
    smul_neg, wordProd_smul_single_three, Subgroup.map_sup,
    map_conj_e6RepConj_rootSubgroup 1 hρ, map_conj_e6RepConj_rootSubgroup 1 (IsRoot.neg hρ),
    smul_neg,
    e6RepWeyl_smul_e6RepPreHigh]
  rfl

theorem exists_psiF4_c3ToF4_eq_single_one :
    ∃ v ∈ roots (isFiniteType_cartanC 3) ∅,
      F4Pilot.psiF4 (c3ToF4 v) = Pi.single (1 : Fin Tag.F4.rank) 1 := by
  have hβ : IsRoot .F4 (Pi.single (1 : Fin Tag.F4.rank) 1) := isRoot_single .F4 1
  have h3 : (Pi.single (1 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ⟨3, by decide⟩ = 0 :=
    Pi.single_eq_of_ne (by decide) _
  have hc : F4Pilot.psiF4 (Pi.single (1 : Fin Tag.F4.rank) 1) ∈ F4Pilot.c3LeviRoots := by
    rw [← F4Pilot.psiF4_mem_b3LeviRoots_iff (F4Pilot.isRoot_psiF4 hβ), F4Pilot.psiF4_psiF4 hβ]
    exact ⟨hβ, h3⟩
  obtain ⟨v, hv, hve⟩ := F4Pilot.exists_c3ToF4_eq_of_mem_c3LeviRoots hc
  exact ⟨v, hv, by rw [hve, F4Pilot.psiF4_psiF4 hβ]⟩

theorem exists_yLevi_coe_eq : ∃ mY : yLevi K, ((mY : adjointGroup .E6 K) : ModGL .E6 K) =
    (e6RepConj K 1 : ModGL .E6 K) * yWeylN K * (e6RepConj K 1 : ModGL .E6 K)⁻¹ := by
  have hmGL : (e6RepConj K 1 : ModGL .E6 K) * yWeylN K * (e6RepConj K 1 : ModGL .E6 K)⁻¹ ∈
      yLeviGL K := by
    rw [yLeviGL_eq_map_yLeviF4]
    exact ⟨yWeylN K, yWeylN_mem_yLeviF4, rfl⟩
  exact ⟨⟨⟨_, yLeviGL_le_adjointGroup hmGL⟩, mem_subgroupOf.2 hmGL⟩, rfl⟩

theorem exists_map_spRootSL2_yLeviSpEquiv_eq :
    ∃ v ∈ roots (isFiniteType_cartanC 3) ∅, ∃ p : ↥(StatedSp 3 K),
      ((((F4Pilot.spRootSL2 3 K v).map (MulAut.conj p).toMonoidHom).map
          (yLeviSpEquiv K).toMonoidHom).map (yLevi K).subtype) =
        (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) := by
  obtain ⟨v, hv, hvβ⟩ := exists_psiF4_c3ToF4_eq_single_one
  obtain ⟨mY, hmY⟩ := exists_yLevi_coe_eq (K := K)
  refine ⟨v, hv, (yLeviSpEquiv K).symm mY, ?_⟩
  have hp : yLeviSpHom K ((yLeviSpEquiv K).symm mY) =
      (e6RepConj K 1 : ModGL .E6 K) * yWeylN K * (e6RepConj K 1 : ModGL .E6 K)⁻¹ := by
    rw [← subtype_comp_yLeviSpEquiv, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hmY
  have hmul : (e6RepConj K 1 : ModGL .E6 K) * yWeylN K * (e6RepConj K 1 : ModGL .E6 K)⁻¹ *
      (e6RepConj K 1 : ModGL .E6 K) = (e6RepConj K 1 : ModGL .E6 K) * yWeylN K := by
    rw [inv_mul_cancel_right]
  apply Subgroup.map_injective (adjointGroup .E6 K).subtype_injective
  rw [subgroupOf_map_subtype, inf_of_le_left EPilot.highRootSL2_le_adjointGroup, Subgroup.map_map,
    Subgroup.map_map, subtype_comp_yLeviSpEquiv, map_map_conj_eq_map_conj, hp,
    map_yLeviSpHom_spRootSL2 hv hvβ, map_conj_map_conj_eq_conj_mul, hmul,
    highRootSL2_eq_map_conj_yWeylN]

theorem isAutConjIn_yLevi_highRootSL2 :
    IsAutConjIn (yLevi K) ((EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)) := by
  obtain ⟨v, -, p, hp⟩ := exists_map_spRootSL2_yLeviSpEquiv_eq (K := K)
  rw [← hp]
  exact ((isAutConj_spRootSL2 le_rfl v).map_conj p).isAutConjIn_map (yLeviSpEquiv K)

end Model

end CFSG.SeitzReduction.E6Pilot

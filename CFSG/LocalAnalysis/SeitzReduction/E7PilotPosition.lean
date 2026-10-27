module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionCaseB
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionX

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)

local instance e7PositionNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section D

variable {K : Type} [Field K]

theorem center_perpLevi_eq_bot_E7 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    center (EPilot.perpLevi .E7 K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hRC : rootSpan .E7 K (EPilot.perpRoots .E7) ≤ adjointGroup .E7 K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hzD : ((z : adjointGroup .E7 K) : ModGL .E7 K) ∈ rootSpan .E7 K (EPilot.perpRoots .E7) :=
    mem_subgroupOf.1 z.2
  have hzC : ((z : adjointGroup .E7 K) : ModGL .E7 K) ∈ adjointGroup .E7 K ⊓
      centralizer (rootSpan .E7 K (EPilot.perpRoots .E7) : Set (ModGL .E7 K)) := by
    refine mem_inf.2 ⟨(z : adjointGroup .E7 K).2, mem_centralizer_iff.2 fun m hm => ?_⟩
    have h := mem_center_iff.1 hz ⟨⟨m, hRC hm⟩, mem_subgroupOf.2 hm⟩
    exact congrArg (fun x : EPilot.perpLevi .E7 K => ((x : adjointGroup .E7 K) : ModGL .E7 K)) h
  rw [EPilot.centralizer_perpLevi_eq (Or.inr (Or.inl rfl)) hq] at hzC
  have h1 := Subgroup.disjoint_def.1
    (E6Pilot.disjoint_highRootSL2_perpLevi (K := K) (Or.inr (Or.inl rfl))) hzC hzD
  exact mem_bot.2 (Subtype.ext (Subtype.ext h1))

theorem perpLevi_E7_eq_subgroupOf_subsystemGroup :
    EPilot.perpLevi .E7 K = (subsystemGroup .E7 K {i | i ≠ (0 : Fin 7)}).subgroupOf
      (adjointGroup .E7 K) := by
  have hroots : parabolicRoots .E7 {i | i ≠ (0 : Fin 7)} = EPilot.perpRoots .E7 := by
    ext γ
    constructor
    · rintro ⟨hγ, h0⟩
      exact ⟨hγ, h0 0 (fun h => h rfl)⟩
    · rintro ⟨hγ, h0⟩
      refine ⟨hγ, fun i hi => ?_⟩
      have hi0 : i = 0 := by
        by_contra h
        exact hi h
      subst hi0
      exact h0
  rw [subsystemGroup_eq_rootSpan, hroots]
  rfl

variable {G : Type*} [Group G] {L : Subgroup G}

noncomputable def perpLeviMapEquivE7 (e : L ≃* adjointGroup .E7 K) :
    EPilot.perpLevi .E7 K ≃*
      (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  ((EPilot.perpLevi .E7 K).equivMapOfInjective _ e.symm.injective).trans
    (((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).equivMapOfInjective _ L.subtype_injective)

theorem perpLevi_le_centralizer_posJE7 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    EPilot.perpLevi .E7 K ≤ centralizer (posJE7 K : Set (adjointGroup .E7 K)) :=
  (EPilot.centralizer_highRootSL2_subgroupOf (Or.inr (Or.inl rfl)) hq).symm.le

theorem map_perpLevi_le_centralizer_E7 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .E7 K) {X : Subgroup G}
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype) :
    ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype ≤ centralizer (X : Set G) :=
  (F4Pilot.map_le_centralizer_map L.subtype
    (F4Pilot.map_le_centralizer_map e.symm.toMonoidHom (perpLevi_le_centralizer_posJE7 hq))).trans
    (centralizer_le hXJ)

end D

theorem exists_le_centralizer_mulEquiv_E7 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype) :
    ∃ g₁ : G, ∃ y ∈ ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype, y ≠ 1 ∧
      (g₁⁻¹ * t * g₁ = y ∨ g₁⁻¹ * t * g₁ = t * y) ∧ ∃ P : Subgroup G,
        P ≤ centralizer (X : Set G) ⊓ centralizer ({g₁⁻¹ * t * g₁} : Set G) ∧
          Nonempty (P ≃* EPilot.perpLevi .E7 K) := by
  by_cases hcase : ∃ g : G, g⁻¹ * t * g ∈ L
  · obtain ⟨g, hw⟩ := hcase
    obtain ⟨g₁, y, hyD, hy1, hg₁, hP⟩ :=
      exists_le_centralizer_mulEquiv_of_conj_mem_E7 hset hf hK e ht hKt hw hXodd hXJ
    exact ⟨g₁, y, hyD, hy1, Or.inl hg₁, hP⟩
  · push Not at hcase
    obtain ⟨g₁, y, hyD, hy1, hg₁, hP⟩ :=
      exists_le_centralizer_mulEquiv_caseA_E7 hset hf hK e ht hKt hcase hXodd hXJ
    exact ⟨g₁, y, hyD, hy1, Or.inr hg₁, hP⟩

theorem not_normal_neighbour_E7 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E7 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hDq : CFSG.Open.IsQuasisimple (EPilot.perpLevi .E7 K))
    (hOutD : Group.IsSolvable (Outer (EPilot.perpLevi .E7 K)))
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((posJE7 K).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  obtain ⟨g₁, y, hyD, hy1, hg₁, P, hP, ⟨eP⟩⟩ :=
    exists_le_centralizer_mulEquiv_E7 hset hf hK e ht hKt hXodd hXJ
  subst hDe
  set eD := perpLeviMapEquivE7 (G := G) e with heD
  have hDL : ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype ≤ L :=
    map_subtype_le _
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht
    (map_perpLevi_le_centralizer_E7 hq e hXJ) (F4Pilot.isQuasisimple_open_of_mulEquiv eD hDq)
    (F4Pilot.center_eq_bot_congr eD (center_perpLevi_eq_bot_E7 hq))
    ((CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eD).2.1 hOutD)
    (hDL.trans hLt) hsyl hyD hy1 hg₁ hP ⟨eP.trans eD⟩

end CFSG.SeitzReduction.E7Pilot

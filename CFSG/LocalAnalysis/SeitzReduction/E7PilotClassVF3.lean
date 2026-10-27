module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVF3Wedge
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVAut
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZCore
public import CFSG.LocalAnalysis.SeitzReduction.EPilotWeakF3
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionRouteBAut
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  map_perfectCore)

section General

variable {G : Type*} [Group G]

theorem perfectCore_subgroupOf [Finite G] {C X : Subgroup G} (hX : X ≤ C) :
    perfectCore (X.subgroupOf C) = (perfectCore X).subgroupOf C := by
  apply map_injective C.subtype_injective
  rw [map_perfectCore, map_subgroupOf_eq_of_le hX,
    map_subgroupOf_eq_of_le ((perfectCore_le X).trans hX)]

theorem map_centralizer_singleton_mulAut (κ : MulAut G) (x : G) :
    (centralizer ({x} : Set G)).map κ.toMonoidHom = centralizer ({κ x} : Set G) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg κ h
    simpa using this
  · intro h
    have := congrArg κ.symm h
    simpa using this

theorem exists_mul_ne_mul_of_perfect {M : Subgroup G} [Nontrivial M] (hM : ⁅M, M⁆ = M) :
    ∃ a b : M, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hbot : ⁅M, M⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
  rw [hM] at hbot
  obtain ⟨a, ha⟩ := exists_ne (1 : M)
  apply ha
  apply Subtype.ext
  have h1 : (a : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact a.2
  exact mem_bot.1 h1

end General

variable {K : Type} [Field K]

theorem parabolicLevi_vNodes_le_rootSpan_sup_torusGroup :
    parabolicLevi .E7 K vNodes ≤
      rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊔ torusGroup .E7 K := by
  refine sup_le le_sup_right ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, ← pinnedX_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots .E7 vNodes) ⟨isRoot_single .E7 j, fun i hi => ?_⟩ c)
    exact Pi.single_eq_of_ne (by rintro rfl; exact hi hj) _
  · rw [SetLike.mem_coe, ← pinnedX_neg_single]
    refine mem_sup_left (pinnedX_mem_rootSpan (S := parabolicRoots .E7 vNodes)
      ⟨isRoot_neg_single .E7 j, fun i hi => ?_⟩ c)
    rw [Pi.neg_apply, Pi.single_eq_of_ne (by rintro rfl; exact hi hj), neg_zero]

theorem perfectCore_torusGroup_eq_bot : perfectCore (torusGroup .E7 K) = ⊥ := by
  refine eq_bot_iff.2 ((CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans (le_of_eq ?_))
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero,
    commutator_eq_bot_iff_le_centralizer]
  intro h hh
  rw [mem_centralizer_iff]
  intro k hk
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
    (torusGroup_le_diagonalGroup hh)

theorem commutator_range_spToAdjointE7 [Finite K] [CharP K 2] :
    ⁅(spToAdjointE7 K).range, (spToAdjointE7 K).range⁆ = (spToAdjointE7 K).range := by
  have hperf : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSp 3 K) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      F4Pilot.sp6_field_condition).1
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    hperf.commutator_eq_top]

theorem perfectCore_parabolicLevi_inf_centralizer_vAS [Finite K] [CharP K 2] :
    perfectCore (parabolicLevi .E7 K vNodes ⊓ centralizer ({vAS K} : Set (ModGL .E7 K))) =
      (spToAdjointE7 K).range.map (adjointGroup .E7 K).subtype := by
  have : Finite (ModGL .E7 K) := finite_modGL
  refine le_antisymm (le_trans (le_inf ?_ ((perfectCore_le _).trans inf_le_right))
    rootSpan_inf_centralizer_le_range_spToAdjointE7) (le_perfectCore_of_perfect (le_inf ?_ ?_) ?_)
  · calc perfectCore (parabolicLevi .E7 K vNodes ⊓ centralizer ({vAS K} : Set (ModGL .E7 K)))
        ≤ perfectCore (rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊔ torusGroup .E7 K) :=
          perfectCore_mono (inf_le_left.trans parabolicLevi_vNodes_le_rootSpan_sup_torusGroup)
      _ ≤ rootSpan .E7 K (parabolicRoots .E7 vNodes) ⊔ perfectCore (torusGroup .E7 K) :=
          E6Pilot.perfectCore_sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
      _ = rootSpan .E7 K (parabolicRoots .E7 vNodes) := by
          rw [perfectCore_torusGroup_eq_bot, sup_bot_eq]
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.1 (range_spToAdjointE7_le_parabolicLevi hx)
  · exact rootSpan_inf_centralizer_eq_range_spToAdjointE7.symm.le.trans inf_le_right
  · rw [← Subgroup.map_commutator, commutator_range_spToAdjointE7]

theorem centralizer_e7Rep_four_eq_map [CharP K 2] :
    centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) =
      ((centralizer ({vAS K} : Set (ModGL .E7 K))).subgroupOf (adjointGroup .E7 K)).map
        (MulAut.conj (e7RepConj K 4)).toMonoidHom := by
  rw [← e7RepConj_mul_e7ASRep_mul_inv (K := K) 4, ← MulAut.conj_apply,
    ← map_centralizer_singleton_mulAut, F4Pilot.centralizer_eq_subgroupOf, coe_e7ASRep_four,
    inf_subgroupOf_right]

theorem leviV_inf_centralizer_e7Rep_four_eq_map [CharP K 2] :
    leviV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) =
      ((parabolicLevi .E7 K vNodes ⊓ centralizer ({vAS K} : Set (ModGL .E7 K))).subgroupOf
        (adjointGroup .E7 K)).map (MulAut.conj (e7RepConj K 4)).toMonoidHom := by
  rw [centralizer_e7Rep_four_eq_map, leviV, ← map_inf_eq _ _ _ (MulAut.conj _).injective]
  congr 1

theorem perfectCore_leviV_inf_centralizer_e7Rep_four [Finite K] [CharP K 2] :
    perfectCore (leviV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) = vLevi K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  rw [leviV_inf_centralizer_e7Rep_four_eq_map, ← map_perfectCore,
    perfectCore_subgroupOf (inf_le_left.trans (parabolicLevi_le_adjointGroup .E7 K vNodes)),
    perfectCore_parabolicLevi_inf_centralizer_vAS, vLevi]
  congr 1
  exact comap_map_eq_self_of_injective (adjointGroup .E7 K).subtype_injective _

theorem leviV_le_normalizer_radicalV :
    leviV K ≤ normalizer (radicalV K : Set (adjointGroup .E7 K)) := by
  have hMN : parabolicLevi .E7 K vNodes ≤
      normalizer (parabolicRadical .E7 K vNodes : Set (ModGL .E7 K)) :=
    (parabolicLevi_le_parabolicSubgroup vNodes).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical vNodes)
  have h : (parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K) ≤
      normalizer ((parabolicRadical .E7 K vNodes).subgroupOf (adjointGroup .E7 K) :
        Set (adjointGroup .E7 K)) := by
    intro m hm
    rw [mem_normalizer_iff]
    intro y
    have hmN := mem_normalizer_iff.1 (hMN (mem_subgroupOf.1 hm)) (y : ModGL .E7 K)
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact hmN
  rw [leviV, radicalV, ← map_equiv_normalizer_eq]
  exact map_mono h

theorem radicalV_inf_leviV : radicalV K ⊓ leviV K = ⊥ := by
  rw [radicalV, leviV, ← map_inf_eq _ _ _ (MulAut.conj _).injective]
  have h : (parabolicRadical .E7 K vNodes).subgroupOf (adjointGroup .E7 K) ⊓
      (parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hq, hm⟩ := mem_inf.1 hx
    have h1 := mem_inf.2 ⟨mem_subgroupOf.1 hq, mem_subgroupOf.1 hm⟩
    rw [parabolicRadical_inf_parabolicLevi vNodes, mem_bot] at h1
    exact mem_bot.2 (Subtype.ext h1)
  rw [h, Subgroup.map_bot]

theorem isPGroup_radicalV [Finite K] [CharP K 2] : IsPGroup 2 (radicalV K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQC : parabolicRadical .E7 K vNodes ≤ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  obtain ⟨-, hQp, -⟩ :=
    (parabolic_root_radical_Levi_factors .E7 K vNodes).2.2.2.2.2.2.2.2.2.2.2.2 2
  exact (F4Pilot.isPGroup_subgroupOf_of_le hQC hQp).map _

theorem centralizer_e7Rep_four_eq_sup [CharP K 2] :
    centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) =
      (radicalV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) ⊔
        (leviV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) := by
  refine le_antisymm (fun g hg => ?_) (sup_le inf_le_right inf_le_right)
  obtain ⟨q, hq, m, hm, hqc, hmc, rfl⟩ := exists_mul_eq_of_mem_centralizer_e7Rep_four hg
  exact mul_mem (mem_sup_left (mem_inf.2 ⟨hq, hqc⟩)) (mem_sup_right (mem_inf.2 ⟨hm, hmc⟩))

section Finite

variable [Finite K] [CharP K 2]

theorem vLevi_le_leviV : vLevi K ≤ leviV K :=
  vLevi_le_conj_parabolicLevi

theorem vLevi_le_normalizer_radicalV :
    vLevi K ≤ normalizer (radicalV K : Set (adjointGroup .E7 K)) :=
  vLevi_le_leviV.trans leviV_le_normalizer_radicalV

theorem commutator_vLevi : ⁅vLevi K, vLevi K⁆ = vLevi K := by
  rw [vLevi, ← Subgroup.map_commutator, commutator_range_spToAdjointE7]

theorem vLevi_le_perfectCore_centralizer :
    vLevi K ≤ perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) :=
  le_perfectCore_of_perfect vLevi_le_centralizer commutator_vLevi

theorem perfectCore_centralizer_e7Rep_four_le :
    perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) ≤
      radicalV K ⊔ vLevi K := by
  have : Finite (ModGL .E7 K) := finite_modGL
  have hMN : leviV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) ≤
      normalizer ((radicalV K ⊓ centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K)) :
        Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) :=
    (inf_le_inf leviV_le_normalizer_radicalV le_normalizer).trans inf_normalizer_le_normalizer_inf
  rw [centralizer_e7Rep_four_eq_sup]
  refine (E6Pilot.perfectCore_sup_le hMN).trans ?_
  rw [perfectCore_leviV_inf_centralizer_e7Rep_four]
  exact sup_le_sup_right inf_le_left _

theorem perfectCore_centralizer_e7Rep_four :
    perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) =
      (perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) ⊓ radicalV K) ⊔
        vLevi K :=
  EPilot.perfectCore_eq_inf_sup_of_le_sup vLevi_le_normalizer_radicalV commutator_vLevi
    vLevi_le_centralizer perfectCore_centralizer_e7Rep_four_le

end Finite

variable (K) in
@[expose] noncomputable def vCoreRadical : Subgroup (adjointGroup .E7 K) :=
  perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) ⊓ radicalV K

section Finite

variable [Finite K] [CharP K 2]

theorem perfectCore_centralizer_e7Rep_four_eq_sup :
    perfectCore (centralizer ({e7Rep K 4} : Set (adjointGroup .E7 K))) =
      vCoreRadical K ⊔ vLevi K :=
  perfectCore_centralizer_e7Rep_four

theorem isPGroup_vCoreRadical : IsPGroup 2 (vCoreRadical K) :=
  isPGroup_radicalV.to_le inf_le_right

theorem vLevi_le_normalizer_vCoreRadical :
    vLevi K ≤ normalizer (vCoreRadical K : Set (adjointGroup .E7 K)) :=
  EPilot.le_normalizer_inf_of_le_of_le_normalizer vLevi_le_normalizer_radicalV
    vLevi_le_perfectCore_centralizer

theorem disjoint_vCoreRadical_vLevi : Disjoint (vCoreRadical K) (vLevi K) :=
  EPilot.disjoint_inf_of_disjoint (disjoint_iff.2 (eq_bot_iff.2
    ((inf_le_inf_left _ vLevi_le_leviV).trans radicalV_inf_leviV.le)))

theorem forall_normal_isPGroup_eq_bot_vLevi :
    ∀ N : Subgroup (vLevi K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .E7 K) := finite_modGL
  have := isSimpleGroup_vLevi (K := K)
  exact EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup
    (exists_mul_ne_mul_of_perfect commutator_vLevi) N hN hp

theorem f5aut_v
    (β : (vCoreRadical K ⊔ vLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (vCoreRadical K ⊔ vLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((vCoreRadical K).subgroupOf (vCoreRadical K ⊔ vLevi K)).map β.toMonoidHom =
      (vCoreRadical K).subgroupOf (vCoreRadical K ⊔ vLevi K)) :
    ∃ c ∈ vLevi K,
      ((((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).subgroupOf (vLevi K)).map
          (EPilot.leviAutOfAut (vCoreRadical K) (vLevi K) disjoint_vCoreRadical_vLevi
            vLevi_le_normalizer_vCoreRadical β hβ).toMonoidHom).map (vLevi K).subtype =
        ((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
          (MulAut.conj c).toMonoidHom :=
  isAutConjIn_vLevi_highRootSL2 _

theorem nonempty_centralizer_map_conj_highRootSL2_mulEquiv (hq : 4 ≤ Nat.card K)
    (c : adjointGroup .E7 K) :
    Nonempty (centralizer ((((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
      (MulAut.conj c).toMonoidHom : Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) ≃*
        EPilot.perpLevi .E7 K) := by
  have hcen : centralizer ((((EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)).map
      (MulAut.conj c).toMonoidHom : Subgroup (adjointGroup .E7 K)) : Set (adjointGroup .E7 K)) =
        (EPilot.perpLevi .E7 K).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c),
      EPilot.centralizer_highRootSL2_subgroupOf (Or.inr (Or.inl rfl)) hq]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((EPilot.perpLevi .E7 K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem nonempty_centralizer_leviAutOfAut_v (hq : 4 ≤ Nat.card K)
    (β : (vCoreRadical K ⊔ vLevi K : Subgroup (adjointGroup .E7 K)) ≃*
      (vCoreRadical K ⊔ vLevi K : Subgroup (adjointGroup .E7 K)))
    (hβ : ((vCoreRadical K).subgroupOf (vCoreRadical K ⊔ vLevi K)).map β.toMonoidHom =
      (vCoreRadical K).subgroupOf (vCoreRadical K ⊔ vLevi K)) :
    Nonempty (centralizer ((((((EPilot.highRootSL2 .E7 K).subgroupOf
        (adjointGroup .E7 K)).subgroupOf (vLevi K)).map (EPilot.leviAutOfAut (vCoreRadical K)
          (vLevi K) disjoint_vCoreRadical_vLevi vLevi_le_normalizer_vCoreRadical β
            hβ).toMonoidHom).map (vLevi K).subtype : Subgroup (adjointGroup .E7 K)) :
        Set (adjointGroup .E7 K)) ≃* EPilot.perpLevi .E7 K) := by
  obtain ⟨c, -, hc⟩ := f5aut_v β hβ
  rw [hc]
  exact nonempty_centralizer_map_conj_highRootSL2_mulEquiv hq c

end Finite

end CFSG.SeitzReduction.E7Pilot

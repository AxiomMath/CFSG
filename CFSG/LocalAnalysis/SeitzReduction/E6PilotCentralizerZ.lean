module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZBruhat
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e6CentralizerZNeZeroRank' : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]


variable (K) in
@[expose] noncomputable def zRadical : Subgroup (adjointGroup .E6 K) :=
  (parabolicRadical .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))).subgroupOf
    (adjointGroup .E6 K)

variable (K) in
@[expose] noncomputable def zLevi : Subgroup (adjointGroup .E6 K) :=
  (parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))).subgroupOf
    (adjointGroup .E6 K)

theorem levi_inf_le_normalizer_radical_inf :
    parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) ≤
      normalizer ((parabolicRadical .E6 K zNodes ⊓
        centralizer ({zAS K} : Set (ModGL .E6 K)) : Subgroup (ModGL .E6 K)) : Set (ModGL .E6 K)) :=
  le_trans (inf_le_inf ((parabolicLevi_le_parabolicSubgroup zNodes).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical zNodes)) le_normalizer)
    inf_normalizer_le_normalizer_inf

theorem radical_inf_inf_levi_inf :
    (parabolicRadical .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))) ⊓
        (parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K))) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf inf_le_left inf_le_left).trans
    (parabolicRadical_inf_parabolicLevi zNodes).le)

theorem isTwoRadicalDecomp_zAS [Finite K] [CharP K 2] :
    F4Pilot.IsTwoRadicalDecomp (e6ASRep K 2) (zRadical K) (zLevi K) := by
  have hQC : parabolicRadical .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) ≤
      adjointGroup .E6 K :=
    inf_le_left.trans ((parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup)
  have hMC : parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) ≤
      adjointGroup .E6 K :=
    inf_le_left.trans (parabolicLevi_le_adjointGroup .E6 K zNodes)
  obtain ⟨h1, h2, h3⟩ := F4Pilot.decomp_subgroupOf hQC hMC (e6ASRep K 2)
    (by rw [coe_e6ASRep_two]; exact centralizer_zAS_inf_eq) radical_inf_inf_levi_inf
    levi_inf_le_normalizer_radical_inf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQp, -⟩ :=
    (parabolic_root_radical_Levi_factors .E6 K zNodes).2.2.2.2.2.2.2.2.2.2.2.2 2
  exact ⟨F4Pilot.isPGroup_subgroupOf_of_le hQC (hQp.to_le inf_le_left), h1, h2, h3⟩

theorem alpha2_frame_check : ∀ β ∈ zFrame,
    isRootB .E6 (Pi.single (1 : Fin Tag.E6.rank) 1 + β) = false ∧
      isRootB .E6 (-Pi.single (1 : Fin Tag.E6.rank) 1 + β) = false ∧
      Pi.single (1 : Fin Tag.E6.rank) 1 ≠ -β ∧ -Pi.single (1 : Fin Tag.E6.rank) 1 ≠ -β := by
  decide +kernel

theorem commute_pinnedX_alpha2_zAS {α : Fin Tag.E6.rank → ℤ}
    (hα : α = Pi.single 1 1 ∨ α = -Pi.single 1 1) (c : K) :
    Commute (pinnedX .E6 K α c) (zAS K) := by
  refine Commute.list_prod_right _ _ fun x hx => ?_
  obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
  have hβr := isRoot_of_mem_zPsi (mem_zPsi_of_mem_zFrame hβ)
  obtain ⟨h1, h2, h3, h4⟩ := alpha2_frame_check β hβ
  rcases hα with rfl | rfl
  · refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_single .E6 1) hβr h3 ?_ c _
    rw [← isRootB_iff, h1]
    exact Bool.false_ne_true
  · refine CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv (isRoot_neg_single .E6 1) hβr h4 ?_ c _
    rw [← isRootB_iff, h2]
    exact Bool.false_ne_true

theorem rootPair_alpha2_le_levi_inf_centralizer :
    rootSubgroup .E6 K (Pi.single 1 1) ⊔ rootSubgroup .E6 K (-Pi.single 1 1) ≤
      parabolicLevi .E6 K zNodes ⊓ centralizer ({zAS K} : Set (ModGL .E6 K)) := by
  have h13 : (1 : Fin Tag.E6.rank) ∈ zNodes := by
    show (1 : Fin Tag.E6.rank) ≠ 3
    decide
  have hcen : ∀ α : Fin Tag.E6.rank → ℤ, (α = Pi.single 1 1 ∨ α = -Pi.single 1 1) →
      rootSubgroup .E6 K α ≤ centralizer ({zAS K} : Set (ModGL .E6 K)) := by
    intro α hα
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact mem_centralizer_singleton_iff.2 (commute_pinnedX_alpha2_zAS hα c).eq
  refine sup_le (le_inf ?_ (hcen _ (Or.inl rfl))) (le_inf ?_ (hcen _ (Or.inr rfl)))
  · exact F4Pilot.rootSubgroup_single_le_parabolicLevi' h13
  · exact F4Pilot.rootSubgroup_neg_single_le_parabolicLevi' h13

variable (K) in
@[expose] noncomputable def zDRadical : Subgroup (adjointGroup .E6 K) :=
  (zRadical K).map (MulAut.conj (e6RepConj K 2)).toMonoidHom

variable (K) in
@[expose] noncomputable def zDLevi : Subgroup (adjointGroup .E6 K) :=
  (zLevi K).map (MulAut.conj (e6RepConj K 2)).toMonoidHom

theorem isTwoRadicalDecomp_zD [Finite K] [CharP K 2] :
    F4Pilot.IsTwoRadicalDecomp (e6Rep K 2) (zDRadical K) (zDLevi K) := by
  have h := (isTwoRadicalDecomp_zAS (K := K)).map (MulAut.conj (e6RepConj K 2))
  rwa [MulAut.conj_apply, e6RepConj_mul_e6ASRep_mul_inv] at h

theorem e6RepWeyl_two_smul_alpha2 :
    e6RepWeyl 2 • (Pi.single (1 : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) = highRoot .E6 := by
  have h : e6RepPreHigh 2 = Pi.single (1 : Fin Tag.E6.rank) 1 := by decide
  rw [← h]
  exact e6RepWeyl_smul_e6RepPreHigh 2

theorem highRootSL2_le_zDLevi [CharP K 2] :
    (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ≤ zDLevi K := by
  intro x hx
  rw [mem_subgroupOf, ← EPilot.map_conj_rootPair_eq_highRootSL2 e6RepWeyl_two_smul_alpha2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyC : y ∈ adjointGroup .E6 K :=
    parabolicLevi_le_adjointGroup .E6 K zNodes (rootPair_alpha2_le_levi_inf_centralizer hy).1
  refine ⟨⟨y, hyC⟩, mem_subgroupOf.2 (rootPair_alpha2_le_levi_inf_centralizer hy), ?_⟩
  apply Subtype.ext
  rw [← hyx]
  rfl

end CFSG.SeitzReduction.E6Pilot

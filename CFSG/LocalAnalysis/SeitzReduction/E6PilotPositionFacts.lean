module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHighE6
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Exact
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZCore
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono perfectCore_eq_self_of_perfect
  le_perfectCore_of_perfect)

section General

variable {G : Type*} [Group G]

theorem perfectCore_eq_inf_sup_of_perfect [Finite G] {X Q M : Subgroup G} (hX : Q ⊔ M = X)
    (hMN : M ≤ normalizer (Q : Set G)) (hM : ⁅M, M⁆ = M) :
    perfectCore X = (perfectCore X ⊓ Q) ⊔ M := by
  conv_lhs => rw [perfectCore_eq_inf_sup_perfectCore hX hMN, perfectCore_eq_self_of_perfect hM]

theorem le_normalizer_perfectCore_inf [Finite G] {X Q M : Subgroup G} (hX : Q ⊔ M = X)
    (hMN : M ≤ normalizer (Q : Set G)) (hM : ⁅M, M⁆ = M) :
    M ≤ normalizer ((perfectCore X ⊓ Q : Subgroup G) : Set G) := by
  have hMX : M ≤ perfectCore X := le_perfectCore_of_perfect (le_sup_right.trans hX.le) hM
  exact le_trans (le_inf (hMX.trans le_normalizer) hMN) inf_normalizer_le_normalizer_inf

theorem disjoint_perfectCore_inf {X Q M : Subgroup G} (hQM : Q ⊓ M = ⊥) :
    Disjoint (perfectCore X ⊓ Q) M := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨⟨-, hxQ⟩, hxM⟩ := mem_inf.1 hx
  have : x ∈ Q ⊓ M := mem_inf.2 ⟨hxQ, hxM⟩
  rwa [hQM] at this

end General

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def posJ : Subgroup (adjointGroup .E6 K) :=
  (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K)

variable (K) in
@[expose] noncomputable def posLevi : Fin 3 → Subgroup (adjointGroup .E6 K) :=
  ![EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1), yLevi K, perfectCore (zDLevi K)]

variable (K) in
@[expose] noncomputable def posRadical : Fin 3 → Subgroup (adjointGroup .E6 K) :=
  ![perfectCore (centralizer ({e6Rep K 0} : Set (adjointGroup .E6 K))) ⊓
      EPilot.rootRadical .E6 K (Pi.single (0 : Fin 6) 1),
    yRadical K,
    perfectCore (centralizer ({e6Rep K 2} : Set (adjointGroup .E6 K))) ⊓ zDRadical K]

theorem isPerfect_SL2_of_four_le [Finite K] (hq : 4 ≤ Nat.card K) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ : Finset K).card by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩

theorem commutator_highRootSL2 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅EPilot.highRootSL2 .E6 K, EPilot.highRootSL2 .E6 K⁆ = EPilot.highRootSL2 .E6 K := by
  have := isPerfect_SL2_of_four_le hq
  rw [← range_rootSL2_highRoot (τ := .E6), ← Subgroup.isPerfect_iff]
  exact Group.IsPerfect.range _

theorem commutator_posJ [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) :
    ⁅posJ K, posJ K⁆ = posJ K :=
  CFSG.SeitzReduction.commutator_subgroupOf_eq_self EPilot.highRootSL2_le_adjointGroup
    (commutator_highRootSL2 hq)

theorem exists_rootPerpLevi_single_zero_eq_map :
    ∃ c : adjointGroup .E6 K, EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) =
      (a5Levi K).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (Or.inl rfl) (isRoot_single .E6 (0 : Fin 6))
  refine ⟨⟨canonicalRep (coxeterSystem .E6) K w, canonicalRep_mem_adjointGroup _ K w⟩, ?_⟩
  rw [EPilot.rootPerpLevi, ← hw, ← EPilot.map_conj_rootSpan_perpRoots (Or.inl rfl) w,
    a5Levi_eq_subgroupOf_perpRoots K, CFSG.LieType.Chevalley.map_conj_subgroupOf
      (EPilot.rootSpan_le_adjointGroup' (EPilot.perpRoots .E6))]

theorem nonempty_rootPerpLevi_single_zero_mulEquiv :
    Nonempty (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) ≃* a5Levi K) := by
  obtain ⟨c, hc⟩ := exists_rootPerpLevi_single_zero_eq_map (K := K)
  exact ⟨(MulEquiv.subgroupCongr hc).trans
    ((a5Levi K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem commutator_rootPerpLevi_single_zero [Finite K] [CharP K 2] :
    ⁅EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1),
        EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1)⁆ =
      EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1) := by
  obtain ⟨c, hc⟩ := exists_rootPerpLevi_single_zero_eq_map (K := K)
  have hD : ⁅a5Levi K, a5Levi K⁆ = a5Levi K :=
    Subgroup.isPerfect_iff.1 (isQuasisimple_a5Levi (K := K)).1
  rw [hc, ← Subgroup.map_commutator, hD]

theorem exists_mul_ne_mul_a5Levi [Finite K] [CharP K 2] :
    ∃ a b : a5Levi K, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hperf := (isQuasisimple_a5Levi (K := K)).1
  have hS := isSimpleGroup_a5Levi (K := K)
  have hcomm : commutator (a5Levi K) = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  rw [hperf.commutator_eq_top] at hcomm
  obtain ⟨a, b, hab⟩ := exists_pair_ne (a5Levi K)
  apply hab
  have ha : a ∈ (⊥ : Subgroup (a5Levi K)) := hcomm ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup (a5Levi K)) := hcomm ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

theorem forall_normal_isPGroup_eq_bot_a5Levi [Finite K] [CharP K 2] (N : Subgroup (a5Levi K))
    (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_a5Levi (K := K)
  exact EPilot.forall_normal_isPGroup_eq_bot_of_isSimpleGroup exists_mul_ne_mul_a5Levi N hN hN2

theorem forall_normal_isPGroup_eq_bot_rootPerpLevi_single_zero [Finite K] [CharP K 2]
    (N : Subgroup (EPilot.rootPerpLevi .E6 K (Pi.single (0 : Fin 6) 1))) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨φ⟩ := nonempty_rootPerpLevi_single_zero_mulEquiv (K := K)
  exact EPilot.forall_normal_isPGroup_eq_bot_of_mulEquiv φ.symm
    forall_normal_isPGroup_eq_bot_a5Levi N hN hN2

theorem perfectCore_centralizer_e6Rep_eq [Finite K] [CharP K 2] (κ : Fin 3) :
    perfectCore (centralizer ({e6Rep K κ} : Set (adjointGroup .E6 K))) =
      posRadical K κ ⊔ posLevi K κ := by
  fin_cases κ
  · obtain ⟨-, hQM, -, hMN⟩ := EPilot.isTwoRadicalDecomp_e6Rep_zero (K := K)
    exact perfectCore_eq_inf_sup_of_perfect hQM hMN commutator_rootPerpLevi_single_zero
  · exact (factF3y (K := K)).1
  · exact (perfectCore_centralizer_zD (K := K)).1

theorem isPGroup_posRadical [Finite K] [CharP K 2] (κ : Fin 3) : IsPGroup 2 (posRadical K κ) := by
  fin_cases κ
  · exact (EPilot.isTwoRadicalDecomp_e6Rep_zero (K := K)).1.to_le inf_le_right
  · exact (factF3y (K := K)).2.1
  · exact (perfectCore_centralizer_zD (K := K)).2.1

theorem posLevi_le_normalizer_posRadical [Finite K] [CharP K 2] (κ : Fin 3) :
    posLevi K κ ≤ normalizer (posRadical K κ : Set (adjointGroup .E6 K)) := by
  fin_cases κ
  · obtain ⟨-, hQM, -, hMN⟩ := EPilot.isTwoRadicalDecomp_e6Rep_zero (K := K)
    exact le_normalizer_perfectCore_inf hQM hMN commutator_rootPerpLevi_single_zero
  · exact (factF3y (K := K)).2.2.1
  · exact (perfectCore_centralizer_zD (K := K)).2.2.1

theorem disjoint_posRadical_posLevi [Finite K] [CharP K 2] (κ : Fin 3) :
    Disjoint (posRadical K κ) (posLevi K κ) := by
  fin_cases κ
  · exact disjoint_perfectCore_inf (EPilot.isTwoRadicalDecomp_e6Rep_zero (K := K)).2.2.1
  · exact (factF3y (K := K)).2.2.2.1
  · exact (perfectCore_centralizer_zD (K := K)).2.2.2

theorem posJ_le_posLevi [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (κ : Fin 3) :
    posJ K ≤ posLevi K κ := by
  fin_cases κ
  · exact EPilot.highRootSL2_subgroupOf_le_rootPerpLevi_e6Rep_zero
  · exact (factF3y (K := K)).2.2.2.2.2
  · exact le_perfectCore_of_perfect highRootSL2_le_zDLevi (commutator_posJ hq)

variable (K) in
@[expose] def ZLeviOTwo : Prop :=
  ∀ N : Subgroup (perfectCore (zDLevi K)), N.Normal → IsPGroup 2 N → N = ⊥

theorem forall_normal_isPGroup_posLevi [Finite K] [CharP K 2] (hz : ZLeviOTwo K) (κ : Fin 3) :
    ∀ N : Subgroup (posLevi K κ), N.Normal → IsPGroup 2 N → N = ⊥ := by
  fin_cases κ
  · exact forall_normal_isPGroup_eq_bot_rootPerpLevi_single_zero
  · exact (factF3y (K := K)).2.2.2.2.1
  · exact hz

variable (K) in
@[expose] def FactF5E6 : Prop :=
  ∀ (κ κ' : Fin 3) (ι : posLevi K κ ≃* posLevi K κ'), ∃ c : adjointGroup .E6 K,
    (((posJ K).subgroupOf (posLevi K κ)).map ι.toMonoidHom).map (posLevi K κ').subtype =
      (posJ K).map (MulAut.conj c).toMonoidHom

variable (K) in
@[expose] def FactF56E6 : Prop :=
  ∀ (κ κ' : Fin 3) (ι : posLevi K κ ≃* posLevi K κ'), Nonempty (centralizer
    (((((posJ K).subgroupOf (posLevi K κ)).map ι.toMonoidHom).map (posLevi K κ').subtype :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) ≃* a5Levi K)

theorem nonempty_centralizer_map_conj_posJ_mulEquiv [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (c : adjointGroup .E6 K) :
    Nonempty (centralizer (((posJ K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) ≃* a5Levi K) := by
  have hcen : centralizer (((posJ K).map (MulAut.conj c).toMonoidHom :
      Subgroup (adjointGroup .E6 K)) : Set (adjointGroup .E6 K)) =
        (a5Levi K).map (MulAut.conj c).toMonoidHom := by
    rw [← F4Pilot.map_centralizer_mulEquiv (MulAut.conj c) (posJ K), posJ,
      EPilot.centralizer_highRootSL2_subgroupOf (Or.inl rfl) hq]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hcen).trans
    ((a5Levi K).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

theorem factF56E6_of_factF5E6 [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) (h : FactF5E6 K) :
    FactF56E6 K := by
  intro κ κ' ι
  obtain ⟨c, hc⟩ := h κ κ' ι
  rw [hc]
  exact nonempty_centralizer_map_conj_posJ_mulEquiv hq c

end CFSG.SeitzReduction.E6Pilot

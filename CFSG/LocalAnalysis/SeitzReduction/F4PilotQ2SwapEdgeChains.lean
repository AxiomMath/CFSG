module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapEdge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapCTMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn TwistOn)

local instance f4PilotQ2SwapEdgeChainsNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩


@[expose] def TwoSwapChainInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∀ P : SwapParam t (subgroupToG e (C3Levi K)), Function.Injective P.Ψ →
      P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀) →
    ∀ P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)),
      Function.Injective P'.Ψ →
      P'.Ψ.range = centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀) →
      (∃ s₂ : ℤˣ, TwistOn s₂ P P'
        (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1}))) ∧
      (∃ s₃ : ℤˣ, TwistOn s₃ P P'
        (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}))) ∧
      ∃ (DR : Subgroup G) (R : SwapParam t DR) (σ σ' : ℤˣ),
        subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}) ≤ DR ∧
        subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}) ≤ DR ∧
        TwistOn σ R P'
          (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0})) ∧
        TwistOn σ' R P
          (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}))

theorem reflect_F4_one_single_two :
    reflect .F4 (1 : Fin (Tag.rank .F4)) (Pi.single 2 1) = Pi.single 1 1 + Pi.single 2 1 := by
  decide

theorem reflect_F4_two_single_one_add_single_two :
    reflect .F4 (2 : Fin (Tag.rank .F4)) (Pi.single 1 1 + Pi.single 2 1) =
      Pi.single 1 1 + Pi.single 2 1 := by
  decide

theorem ht_single_one_add_single_two_pos :
    0 < ht (Pi.single 1 1 + Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) := by
  decide

theorem ht_neg_single_two_neg : ht (-Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) < 0 := by
  decide

theorem not_forall_commute_levi_one_two (K : Type) [Field K] :
    ¬ ∀ a ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1},
      ∀ b ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}, a * b = b * a := by
  intro hcomm
  have hct := Adjoint.f4_isCTGroupDatum K
  have hext := Adjoint.f4_steinbergExtras K
  have hroot : ∀ v, v ∈ (Adjoint.f4Datum K).roots ↔ IsRoot .F4 v := fun v =>
    Adjoint.mem_adjDatum_roots
  have hα : (Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) ∈ (Adjoint.f4Datum K).roots :=
    (hroot _).2 (isRoot_single _ 2)
  have hα' : (-Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) ∈ (Adjoint.f4Datum K).roots :=
    (hroot _).2 (isRoot_neg_single _ 2)
  have hδ : (Pi.single 1 1 + Pi.single 2 1 : Fin (Tag.rank .F4) → ℤ) ∈
      (Adjoint.f4Datum K).roots := (hroot _).2 (by rw [← mem_rootFinset]; decide)
  have hs1 : CFSG.LieType.RootSystem.weylAction (Adjoint.f4Datum K).isFiniteType
      ((CFSG.LieType.RootSystem.coxeterMatrix
        (Adjoint.f4Datum K).isFiniteType).toCoxeterSystem.simple 1)
      (Pi.single 2 1) = Pi.single 1 1 + Pi.single 2 1 := by
    rw [Adjoint.weylAction_simple_eq_reflect]
    exact reflect_F4_one_single_two
  have hs2 : CFSG.LieType.RootSystem.weylAction (Adjoint.f4Datum K).isFiniteType
      ((CFSG.LieType.RootSystem.coxeterMatrix
        (Adjoint.f4Datum K).isFiniteType).toCoxeterSystem.simple 2)
      (Pi.single 1 1 + Pi.single 2 1) = Pi.single 1 1 + Pi.single 2 1 := by
    rw [Adjoint.weylAction_simple_eq_reflect]
    exact reflect_F4_two_single_one_add_single_two
  have hs2' := CFSG.LieType.RootSystem.weylAction_simple_single
    (Adjoint.f4Datum K).isFiniteType (2 : Fin (Tag.rank .F4))
  apply hext.ne_bot _ hα
  rw [eq_bot_iff]
  intro x hx
  have hn1 : CFSG.LieType.Chevalley.weylElement .F4 K 1 ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} := by
    rw [CFSG.LieType.CurtisTits.levi_singleton]
    exact hct.n_mem 1
  have hx2 : x ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} := by
    rw [CFSG.LieType.CurtisTits.levi_singleton]
    exact mem_sup_left hx
  have hxδ : x ∈ (Adjoint.f4Datum K).rootGroup (Pi.single 1 1 + Pi.single 2 1) := by
    have h1 := hct.conj_mem 1 _ hα x hx
    rw [hs1] at h1
    have h2 : CFSG.LieType.Chevalley.weylElement .F4 K 1 * x *
        (CFSG.LieType.Chevalley.weylElement .F4 K 1)⁻¹ = x := by
      rw [hcomm _ hn1 _ hx2, mul_inv_cancel_right]
    rwa [h2] at h1
  have hy1 := hct.conj_mem 2 _ hα x hx
  have hy2 := hct.conj_mem 2 _ hδ x hxδ
  rw [hs2'] at hy1
  rw [hs2] at hy2
  set y := CFSG.LieType.Chevalley.weylElement .F4 K 2 * x *
    (CFSG.LieType.Chevalley.weylElement .F4 K 2)⁻¹ with hydef
  have hy : y = 1 := by
    have hmem : y ∈ (⨆ γ ∈ {γ | γ ∈ (Adjoint.f4Datum K).roots ∧ 0 < ht γ},
        (Adjoint.f4Datum K).rootGroup γ) ⊓
        (⨆ γ ∈ {γ | γ ∈ (Adjoint.f4Datum K).roots ∧ ht γ < 0},
          (Adjoint.f4Datum K).rootGroup γ) :=
      mem_inf.2 ⟨le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ (Adjoint.f4Datum K).roots ∧
          0 < ht γ}) => (Adjoint.f4Datum K).rootGroup γ) (Pi.single 1 1 + Pi.single 2 1)
          ⟨hδ, ht_single_one_add_single_two_pos⟩ le_rfl hy2,
        le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ (Adjoint.f4Datum K).roots ∧
          ht γ < 0}) => (Adjoint.f4Datum K).rootGroup γ) (-Pi.single 2 1)
          ⟨hα', ht_neg_single_two_neg⟩ le_rfl hy1⟩
    rw [hext.posPart_inf_negPart, mem_bot] at hmem
    exact hmem
  rw [mem_bot]
  have e1 : x = (CFSG.LieType.Chevalley.weylElement .F4 K 2)⁻¹ * y *
      CFSG.LieType.Chevalley.weylElement .F4 K 2 := by
    rw [hydef]
    group
  rw [e1, hy, mul_one, inv_mul_cancel]

theorem f4LeviOneTwoNotCommuteInput_holds :
    ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
      ∃ a ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1},
        ∃ b ∈ CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}, a * b ≠ b * a := by
  intro K _ _ _ _
  by_contra h
  exact not_forall_commute_levi_one_two K fun a ha b hb => by
    by_contra hab
    exact h ⟨a, ha, b, hb, hab⟩

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem subgroupToG_levi_pair (e : L ≃* adjointGroup .F4 K) (i j : Fin (Tag.rank .F4)) :
    subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i, j}) =
      subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i}) ⊔
        subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {j}) := by
  rw [levi_pair, subgroupToG, subgroupToG, subgroupToG, Subgroup.map_sup, Subgroup.map_sup]

theorem commute_coe_symm (e : L ≃* adjointGroup .F4 K) {x y : adjointGroup .F4 K}
    (h : x * y = y * x) :
    ((e.symm x : L) : G) * ((e.symm y : L) : G) = ((e.symm y : L) : G) * ((e.symm x : L) : G) := by
  rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h]

theorem twoSwapCoherenceInput_of_chainInput (h : TwoSwapChainInput) : TwoSwapCoherenceInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
  obtain ⟨⟨s₂, h₂⟩, ⟨s₃, h₃⟩, DR, R, σ, σ', h0R, h3R, h₀, h₃'⟩ :=
    h G L K e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  obtain ⟨a, ha, b, hb, hab⟩ := f4LeviOneTwoNotCommuteInput_holds K hK2
  have h10 : (0 : Fin (Tag.rank .F4)) ∉ ({1} : Finset (Fin (Tag.rank .F4))) := by decide
  have h20 : (0 : Fin (Tag.rank .F4)) ∉ ({2} : Finset (Fin (Tag.rank .F4))) := by decide
  have h13 : (3 : Fin (Tag.rank .F4)) ∉ ({1} : Finset (Fin (Tag.rank .F4))) := by decide
  have h23 : (3 : Fin (Tag.rank .F4)) ∉ ({2} : Finset (Fin (Tag.rank .F4))) := by decide
  have hab' : ((e.symm a : L) : G) * ((e.symm b : L) : G) ≠
      ((e.symm b : L) : G) * ((e.symm a : L) : G) := by
    intro h1
    apply hab
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul] at h1
    exact e.symm.injective (Subtype.ext h1)
  have hagree := agreeOn_twist_sup_of_not_commute htt hinj' h₂ h₃
    (subgroupToG_levi_le_C3Levi e h10) (subgroupToG_levi_le_C3Levi e h20)
    (subgroupToG_levi_le_B3Levi e h13) (subgroupToG_levi_le_B3Levi e h23)
    (coe_symm_mem_subgroupToG e ha) (coe_symm_mem_subgroupToG e hb) hab'
  refine ⟨s₂, (subgroupToG_levi_pair e 1 2).symm ▸ hagree, ?_⟩
  refine commute_twist_lft_of_twistOn htt s₂ R h₀ h₃' h0R h3R fun x hx y hy => ?_
  obtain ⟨x', hx', rfl⟩ := exists_eq_of_mem_subgroupToG e hx
  obtain ⟨y', hy', rfl⟩ := exists_eq_of_mem_subgroupToG e hy
  exact commute_coe_symm e (commute_levi_zero_three x' hx' y' hy').eq

theorem twoSwapPairParamInput_of_chainInput (h : TwoSwapChainInput)
    (hP : TwoF4SwapPairExclusionInput) : TwoSwapPairParamInput :=
  twoSwapPairParamInput_of_inputs (twoSwapCoherenceInput_of_chainInput h) hP

theorem twoSwapPairInput_of_chainInput (h : TwoSwapChainInput)
    (hP : TwoF4SwapPairExclusionInput) : TwoSwapPairInput :=
  twoSwapPairInput_of_paramInput (twoSwapPairParamInput_of_chainInput h hP)

end CFSG.SeitzReduction.F4Pilot

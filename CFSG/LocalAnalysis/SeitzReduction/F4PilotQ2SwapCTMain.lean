module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapCT
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Setup
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn)

local instance f4PilotQ2SwapCTMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem not_evenStandardException_of_card_eq_ordF4_two {Q : Type} [Group Q]
    (hQ : Nat.card Q = ordF4 2) : ¬ Recognition.Exact.EvenStandardException Q := by
  classical
  have hQ' : Nat.card Q = 3311126603366400 := by rw [hQ]; decide
  rintro (h1 | h1 | h1 | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | h1 | h1 | h1)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · have hle : Nat.card Q ≤ Fintype.card K ^ 16 := by
      rw [Nat.card_congr e.toEquiv]
      calc Nat.card (commutator (Matrix.symplecticGroup (Fin 2) K))
          ≤ Nat.card (Matrix.symplecticGroup (Fin 2) K) := Subgroup.card_le_card_group _
        _ ≤ Nat.card (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :=
            Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = Fintype.card K ^ 16 := by
            rw [Matrix, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
            simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
            ring
    rw [hQ', hK] at hle
    exact absurd hle (by norm_num)
  · have hK2 : Nat.card K = 2 := by rw [Nat.card_eq_fintype_card, hK]
    have hH : Nat.card (adjointGroup .G2 K) = 12096 := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK2]
      rfl
    have : Finite (adjointGroup .G2 K) := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
    have hle : Nat.card Q ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← hH]
      refine Subgroup.card_le_of_le (Subgroup.commutator_le.2 fun a ha c hc => ?_)
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    rw [hQ'] at hle
    exact absurd hle (by norm_num)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · rw [EvenSmallLie.Child3.card_of_lieModel_classical (by norm_num) h1] at hQ'
    exact absurd hQ' (by decide)
  · obtain ⟨e⟩ := h1
    rw [Nat.card_congr e.toEquiv] at hQ'
    change Nat.card CFSG.Blueprint.NativeSporadic.He = _ at hQ'
    rw [CFSG.Sporadic.He.card_He] at hQ'
    exact absurd hQ' (by norm_num)

theorem lieModel_of_mulEquiv_F4 {G : Type} [Group G] {L : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .F4 K) :
    LieModel L .F4 0 2 f := by
  have := finite_of_natCard_eq_two_pow hK
  refine Or.inr (Or.inl ⟨by decide, by decide, ⟨Nat.prime_two, hf, rfl⟩, K, inferInstance,
    inferInstance, hK, ⟨e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .F4 K).symm⟩⟩)

theorem seitzSetting_of_f4Work_F4_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) :
    SeitzSetting G L := by
  have hZ := hw.center_eq_bot
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have : IsSimpleGroup G := hw.standard.simple
  have hLM : LieModel L .F4 0 2 1 := lieModel_of_mulEquiv_F4 le_rfl hw.card_eq e
  have hLMq : LieModel (L ⧸ center L) .F4 0 2 1 :=
    lieModel_of_mulEquiv (quotientCenterMulEquiv hZ).symm hLM
  have hcard : Nat.card (L ⧸ center L) = ordF4 2 := by
    rw [Nat.card_congr (quotientCenterMulEquiv hZ).toEquiv, Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hw.card_eq, pow_one]
  obtain ⟨S, hS⟩ := hw.standard.cyclic
  exact seitzSetting_of hw.standard.nonab hw.standard.kProper hw.standard.standard
    hw.standard.core S hS (Or.inl ⟨.F4, 0, 1, ⟨Nat.prime_two, le_rfl, rfl⟩, hLMq⟩)
    (not_evenStandardException_of_card_eq_ordF4_two hcard) hZ

theorem false_of_coherent_swapParams_F4_two {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) (hP : SeitzQ2.SwapPairExclusion (adjointGroup .F4 K))
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (P : SwapParam t (subgroupToG e (C3Levi K)))
    (hinj : Function.Injective P.Ψ)
    (hrange : P.Ψ.range = centralizerPerfectCore (subgroupToG e X₀))
    (P' : SwapParam t (subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K)))
    (hagree : AgreeOn P P'
      (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2})))
    (hcomm : ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}),
      ∀ b ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}),
      Commute (P'.lft a) (P.lft b) ∧ Commute (P'.lft a) (t * P.lft b * t⁻¹)) : False := by
  obtain ⟨G₁, hq, h₁₂, hδ, hsurj, hE⟩ :=
    exists_swapFactors_of_coherent_F4_two hw e hXJ hcyc hX₀ P hinj hrange P' hagree hcomm
  have hset := seitzSetting_of_f4Work_F4_two hw e
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have ht := hw.orderOf_eq
  have hKt := hw.inf_eq
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have : Finite (adjointGroup .F4 K) := by
    have : Finite (ModGL Tag.F4 K) := finite_modGL
    infer_instance
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨-, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hDX : subgroupToG e (C3Levi K) ≤ centralizer (subgroupToG e X₀ : Set G) :=
    map_map_symm_le_centralizer e hX₀D
  have hDq : CFSG.IsQuasisimple (subgroupToG e (C3Levi K)) := isQuasisimple_map_C3Levi e
  have hDperf : ⁅subgroupToG e (C3Levi K), subgroupToG e (C3Levi K)⁆ = subgroupToG e (C3Levi K) :=
    isPerfect_iff.mp hDq.1
  have hD : subgroupToG e (C3Levi K) ≠ ⊥ :=
    (nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial hDq)
  have hnorm := SeitzQ2.nonSwap_of_factorNormal hset ht hKt
    (SeitzQ2.factorNormal_of_swapPairExclusion hset hOut e hP ht hKt) hq h₁₂ hδ hsurj
  have huniq := SeitzQ2.unique_of_swapFactors_of_neighbour hset hOut hw.mem_centralizer ht hq h₁₂
    hδ hsurj (subgroupToG_le e X₀) (subgroupToG_le e (C3Levi K)) hDX hDperf hD hE hnorm
  have : IsSimpleGroup G := hset.1
  exact false_of_simple_of_swap_of_isQuasisimple ht hq h₁₂ rfl huniq

@[expose] def TwoSwapCoherenceInput : Prop :=
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
      ∃ s : ℤˣ, AgreeOn P (P'.twist s)
          (subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1, 2})) ∧
        ∀ a ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}),
        ∀ b ∈ subgroupToG e (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3}),
          Commute ((P'.twist s).lft a) (P.lft b) ∧
            Commute ((P'.twist s).lft a) (t * P.lft b * t⁻¹)

@[expose] def TwoF4SwapPairExclusionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    SeitzQ2.SwapPairExclusion (adjointGroup .F4 K)

theorem twoSwapPairParamInput_of_inputs (hC : TwoSwapCoherenceInput)
    (hP : TwoF4SwapPairExclusionInput) : TwoSwapPairParamInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
  obtain ⟨s, hagree, hcomm⟩ := hC G L K e t hw X₀ hXJ hcyc hX₀ P hinj hrange P' hinj' hrange'
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  exact false_of_coherent_swapParams_F4_two hw e (hP K hK2) hXJ hcyc hX₀ P hinj hrange
    (P'.twist s) hagree hcomm

end CFSG.SeitzReduction.F4Pilot

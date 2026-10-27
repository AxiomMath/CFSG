module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldRowEnd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowField

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2FieldRowMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem one_subset_nodes_X_fieldRow :
    ({1} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

theorem one_subset_nodes_Y : ({1} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.Y.nodes := by
  decide

theorem two_subset_nodes_X : ({2} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.X.nodes := by
  decide

theorem two_subset_nodes_Y : ({2} : Finset (Fin (Tag.rank .F4))) ⊆ AmalgamNeighbour.Y.nodes := by
  decide


section Facts

theorem Q2FieldParam.range_restrict_one_two {K : Type} [Field K] {σ : K ≃+* K} {G : Type}
    [Group G] {L : Subgroup G} {e : L ≃* adjointGroup .F4 (fixSubfield σ)} {N : AmalgamNeighbour}
    {E : Subgroup G} (h : Q2FieldParam σ e N E)
    (h12 : ({1, 2} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes)
    (h1 : ({1} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes)
    (h2 : ({2} : Finset (Fin (Tag.rank .F4))) ⊆ N.nodes) :
    (h.restrict h12).range = (h.restrict h1).range ⊔ (h.restrict h2).range := by
  rw [h.range_restrict_eq_map, h.range_restrict_eq_map, h.range_restrict_eq_map,
    ← Subgroup.map_sup, levi_pair, subgroupOf_sup (levi_le_neighbourLevi h1)
      (levi_le_neighbourLevi h2)]

theorem baseChangeGL_mem_highestRootRankOne {k K : Type} [Field k] [Field K] (ι : k →+* K)
    {x : ModGL .F4 k} (hx : x ∈ highestRootRankOne k) :
    baseChangeGL ι x ∈ highestRootRankOne K := by
  have hU : ∀ α : Fin (Tag.rank .F4) → ℤ,
      (rootSubgroup .F4 k α).map (baseChangeGL ι) ≤ rootSubgroup .F4 K α := by
    intro α
    rw [rootSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    rw [baseChangeGL_pinnedX]
    exact subset_closure ⟨ι c, rfl⟩
  have h : (highestRootRankOne k).map (baseChangeGL ι) ≤ highestRootRankOne K := by
    rw [highestRootRankOne, Subgroup.map_sup]
    exact sup_le_sup (hU _) (hU _)
  exact h ⟨x, hx, rfl⟩

theorem subgroupToG_levi_eq_modelToG {G : Type} [Group G] {L : Subgroup G} {K K' : Type}
    [Field K] [Field K'] (e : L ≃* adjointGroup .F4 K) (ε : K ≃+* K') (N : AmalgamNeighbour) :
    subgroupToG e (N.levi K) = modelToG (e.trans (adjointGroupF4RingEquiv ε))
      ((N.levi K').map (adjointGroup .F4 K').subtype) := by
  ext g
  rw [mem_modelToG]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨adjointGroupF4RingEquiv ε y, baseChangeGL_mem_map_levi _ N ⟨y, hy, rfl⟩, ?_⟩
    rw [MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply]
    rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨_, ⟨(adjointGroupF4RingEquiv ε).symm x,
      mem_levi_of_coe_mem (baseChangeGL_mem_map_levi _ N hx), rfl⟩, ?_⟩
    rw [MulEquiv.symm_trans_apply]
    rfl

end Facts

@[expose] def F4TwoFieldPieceInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
    ∀ (K₂ : Type) [Field K₂] [Finite K₂] [CharP K₂ 2] (σ : K₂ ≃+* K₂), Nat.card K₂ = 4 →
      orderOf σ = 2 → ∀ ε : K ≃+* fixSubfield σ,
    ∀ (hX : Q2FieldParam σ (e.trans (adjointGroupF4RingEquiv ε)) .X
          (centralizerPerfectCore (subgroupToG e X₀)))
      (hY : Q2FieldParam σ (e.trans (adjointGroupF4RingEquiv ε)) .Y
          (centralizerPerfectCore (subgroupToG (e.trans (graphAutF4 K).symm) X₀))),
      (hX.restrict one_subset_nodes_X_fieldRow).range = (hY.restrict one_subset_nodes_Y).range ∧
      (hX.restrict two_subset_nodes_X).range = (hY.restrict two_subset_nodes_Y).range ∧
      (hY.restrict zero_subset_Y).range = (hX.toX'.restrict zero_subset_X').range ∧
      (hX.restrict three_subset_X).range = (hX.toX'.restrict three_subset_X').range

theorem twoFieldPairParamInput_of_pieceInput (hP : F4TwoFieldPieceInput) :
    TwoFieldPairParamInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ F _ _ _ hF hisoX F' _ _ _ hF' hisoY hfixX hfixY
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, hσapp, hk⟩ := exists_quadraticFrobenius_F4 (f := 1) le_rfl
  have hq : QuadraticFrobenius K₂ σ 1 := ⟨hK₂, hσ, hσapp⟩
  have hK₂4 : Nat.card K₂ = 4 := by rw [hK₂]; norm_num
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  let := Fintype.ofFinite K₂
  let := Fintype.ofFinite F
  let := Fintype.ofFinite F'
  have hc : Fintype.card K = Fintype.card (fixSubfield σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hw.card_eq]
  set ε : K ≃+* fixSubfield σ := FiniteField.ringEquivOfCardEq hc with hε
  set e' : L ≃* adjointGroup .F4 (fixSubfield σ) := e.trans (adjointGroupF4RingEquiv ε) with he'
  have hw' : F4Work L (fixSubfield σ) t 1 :=
    ⟨hw.standard, hw.center_eq_bot, hw.one_le, hk, hw.orderOf_eq, hw.inf_eq⟩
  have hcF : Fintype.card K₂ = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₂4, hF]
  have hcF' : Fintype.card K₂ = Fintype.card F' := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₂4, hF']
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set Y : Subgroup G := subgroupToG (e.trans (graphAutF4 K).symm) X₀ with hYdef
  have hXL : X ≤ L := map_subtype_le _
  have hYL : Y ≤ L := map_subtype_le _
  have htC := hw.mem_centralizer
  have htNX : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore X
      (centralizer_le_normalizer X (centralizer_le hXL htC))
  have htNY : t ∈ normalizer (centralizerPerfectCore Y : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore Y
      (centralizer_le_normalizer Y (centralizer_le hYL htC))
  have hDX : subgroupToG e (C3Levi K) = modelToG e'
      ((AmalgamNeighbour.X.levi (fixSubfield σ)).map
        (adjointGroup .F4 (fixSubfield σ)).subtype) :=
    subgroupToG_levi_eq_modelToG e ε .X
  have hDY : subgroupToG (e.trans (graphAutF4 K).symm) (C3Levi K) = modelToG e'
      ((AmalgamNeighbour.Y.levi (fixSubfield σ)).map
        (adjointGroup .F4 (fixSubfield σ)).subtype) := by
    rw [← subgroupToG_levi_eq_modelToG e ε .Y]
    have hcomp : (e.trans (graphAutF4 K).symm).symm.toMonoidHom =
        e.symm.toMonoidHom.comp (graphAutF4 K).toMonoidHom := by
      ext x
      rfl
    change ((C3Levi K).map (e.trans (graphAutF4 K).symm).symm.toMonoidHom).map L.subtype =
      ((B3Levi K).map e.symm.toMonoidHom).map L.subtype
    have hB : (C3Levi K).map (graphAutF4 K).toMonoidHom = B3Levi K := map_graphAutF4_C3Levi
    rw [← hB, Subgroup.map_map, hcomp, Subgroup.map_map, Subgroup.map_map]
    rfl
  obtain ⟨ψX⟩ := hisoX
  obtain ⟨ψY⟩ := hisoY
  have hψX : Nonempty (AmalgamNeighbour.X.levi K₂ ≃* centralizerPerfectCore X) :=
    ⟨(neighbourLeviEquiv K₂ .X).symm.trans
      ((statedSpCongr (FiniteField.ringEquivOfCardEq hcF) 3).trans ψX)⟩
  have hψY : Nonempty (AmalgamNeighbour.Y.levi K₂ ≃* centralizerPerfectCore Y) :=
    ⟨(neighbourLeviEquiv K₂ .Y).symm.trans
      ((statedSpCongr (FiniteField.ringEquivOfCardEq hcF') 3).trans ψY)⟩
  obtain ⟨hX⟩ := nonempty_q2FieldParam (e := e') .X hψX htNX hw.orderOf_eq hσ (hfixX.trans hDX)
  obtain ⟨hY⟩ := nonempty_q2FieldParam (e := e') .Y hψY htNY hw.orderOf_eq hσ (hfixY.trans hDY)
  obtain ⟨h1, h2, -, -⟩ := hP G L K e t hw X₀ hXJ hcyc hX₀ K₂ σ hK₂4 hσ ε hX hY
  have hr12 : (hX.restrict one_two_subset_X).range = (hY.restrict one_two_subset_Y).range := by
    rw [hX.range_restrict_one_two one_two_subset_X one_subset_nodes_X_fieldRow two_subset_nodes_X,
      hY.range_restrict_one_two one_two_subset_Y one_subset_nodes_Y two_subset_nodes_Y, h1, h2]
  obtain ⟨ρ, hρ, hagree⟩ := exists_twist_restrict_eq_q2 hX hY hr12
  set hY' := hY.twist ρ hρ with hY'def
  set hX' := hX.toX' with hX'def
  obtain ⟨-, -, hM0, hM3⟩ := hP G L K e t hw X₀ hXJ hcyc hX₀ K₂ σ hK₂4 hσ ε hX hY'
  have hcomm : ∀ a b, Commute (hY'.restrict zero_subset_Y a) (hX.restrict three_subset_X b) := by
    intro a b
    obtain ⟨a', ha'⟩ : hY'.restrict zero_subset_Y a ∈ (hX'.restrict zero_subset_X').range :=
      hM0 ▸ ⟨a, rfl⟩
    obtain ⟨b', hb'⟩ : hX.restrict three_subset_X b ∈ (hX'.restrict three_subset_X').range :=
      hM3 ▸ ⟨b, rfl⟩
    rw [← ha', ← hb']
    exact hX'.commute_restrict _ _ a' b' (commute_levi_zero_three _ a'.2 _ b'.2)
  obtain ⟨ψ, hinj, hfixψ, hDψ⟩ := exists_injective_q2FieldRow hX hY' hagree hcomm
  have hXD : ∀ a : adjointGroup .F4 (fixSubfield σ), ((e'.symm a : L) : G) ∈ X →
      C3Levi K₂ ≤ centralizer ({fixedFieldInclusion σ a} : Set (adjointGroup .F4 K₂)) := by
    intro a ha d hd
    obtain ⟨_, ⟨x, hx, rfl⟩, hxa⟩ := ha
    have hxa' : x = (adjointGroupF4RingEquiv ε).symm a := by
      apply e.symm.injective
      exact Subtype.ext hxa
    have hxa'' : a = adjointGroupF4RingEquiv ε x := by
      rw [hxa', MulEquiv.apply_symm_apply]
    have hJ : ((fixedFieldInclusion σ a : adjointGroup .F4 K₂) : ModGL .F4 K₂) ∈
        highestRootRankOne K₂ := by
      rw [coe_fixedFieldInclusion, hxa'']
      change baseChangeGL (fixSubfield σ).subtype
        (baseChangeGL (ε : K →+* fixSubfield σ) (x : ModGL .F4 K)) ∈ _
      rw [baseChangeGL_baseChangeGL]
      exact baseChangeGL_mem_highestRootRankOne _ (mem_subgroupOf.1 (hXJ hx))
    exact mem_centralizer_singleton_iff.2
      (commute_of_mem_highestRootRankOne_of_mem_C3Levi (mem_subgroupOf.2 hJ) hd).symm
  exact false_of_q2FieldRow_of_injective hw' hq e' hXL hXD hinj hfixψ hDψ

theorem twoFieldPairInput_of_pieceInput (hP : F4TwoFieldPieceInput) : TwoFieldPairInput :=
  twoFieldPairInput_of_paramInput (twoFieldPairParamInput_of_pieceInput hP)

end CFSG.SeitzReduction.F4Pilot

module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpin

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.SeitzReduction.F4Pilot (three_le_rank_D4)
open scoped commutatorElement
open E7Neighbour

local instance e7PilotQ2OverlapSpinNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Levi

variable (K : Type) [Field K]

@[expose] noncomputable def d4LeviPar (γ : Fin 4 → ℤ) (c : K) : ↥(adjointGroup .E7 K) :=
  ⟨pinnedX .E7 K (d4EmbedE7 γ) c, pinnedX_mem_adjointGroup _ c⟩

variable {K}

theorem coe_d4LeviPar (γ : Fin 4 → ℤ) (c : K) :
    ((d4LeviPar K γ c : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K (d4EmbedE7 γ) c :=
  rfl

theorem d4LeviPar_add (γ : Fin 4 → ℤ) (c d : K) :
    d4LeviPar K γ (c + d) = d4LeviPar K γ c * d4LeviPar K γ d :=
  Subtype.ext (pinnedX_add .E7 K _ c d)

theorem d4LeviPar_zero (γ : Fin 4 → ℤ) : d4LeviPar K γ 0 = 1 :=
  Subtype.ext (pinnedX_zero .E7 K _)

theorem d4LeviPar_injective (γ : Fin 4 → ℤ) : Function.Injective (d4LeviPar K γ) :=
  fun _ _ h => pinnedX_injective .E7 K _ (congrArg Subtype.val h :)

theorem rootSpan_overlapRootsD4_high_seven_eq_closure :
    rootSpan .E7 K (overlapRootsD4 .high .seven) =
      closure {g | ∃ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∃ c : K,
        pinnedX .E7 K (d4EmbedE7 γ) c = g} := by
  rw [overlapRootsD4_high_seven_eq_image]
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · obtain ⟨v, hv, rfl⟩ := hγ
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact subset_closure ⟨v, hv, c, rfl⟩
  · rintro _ ⟨γ, hγ, c, rfl⟩
    exact le_iSup₂ (f := fun γ (_ : γ ∈ d4EmbedE7 '' roots (isFiniteType_cartanD 4) ∅) =>
      rootSubgroup .E7 K γ) (d4EmbedE7 γ) ⟨γ, hγ, rfl⟩ (subset_closure ⟨c, rfl⟩)

theorem overlapSpanD4_high_seven_eq_closure :
    overlapSpanD4 K .high .seven =
      closure {g | ∃ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∃ c : K, d4LeviPar K γ c = g} := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  rw [overlapSpanD4, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _),
    rootSpan_overlapRootsD4_high_seven_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨d4LeviPar K γ c, ⟨γ, hγ, c, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, rfl⟩

end Levi

section Commutators

variable {K : Type} [Field K]

theorem commutator_d4LeviPar_of_mem [CharP K 2] {α β : Fin 4 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 4) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 4) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∈ roots (isFiniteType_cartanD 4) ∅) (c d : K) :
    ⁅d4LeviPar K α c, d4LeviPar K β d⁆ = d4LeviPar K (α + β) (c * d) := by
  have hαβ : α ≠ β := fun h => add_self_not_mem_rootsD4_E7 (h ▸ hr)
  have hne₁ : d4EmbedE7 α ≠ d4EmbedE7 β := fun h => hαβ (d4EmbedE7_injective h)
  have hne₂ : d4EmbedE7 α ≠ -d4EmbedE7 β := fun h => hne (d4EmbedE7_injective (by
    rw [d4EmbedE7_add, h, d4EmbedE7_zero, neg_add_cancel]))
  have hr7 : IsRoot .E7 (d4EmbedE7 α + d4EmbedE7 β) := by
    rw [← d4EmbedE7_add]
    exact isRoot_d4EmbedE7 hr
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
    (isRoot_d4EmbedE7 hα) (isRoot_d4EmbedE7 hβ) hne₁ hne₂).1 hr7
  apply Subtype.ext
  rw [show ((⁅d4LeviPar K α c, d4LeviPar K β d⁆ : adjointGroup .E7 K) : ModGL .E7 K) =
      ⁅((d4LeviPar K α c : adjointGroup .E7 K) : ModGL .E7 K),
        ((d4LeviPar K β d : adjointGroup .E7 K) : ModGL .E7 K)⁆ from
      map_commutatorElement (adjointGroup .E7 K).subtype _ _,
    coe_d4LeviPar, coe_d4LeviPar, coe_d4LeviPar, hF K c d,
    intCast_eq_one_of_charTwo_D6 hC, one_mul, d4EmbedE7_add]

theorem commutator_d4LeviPar_of_not_mem {α β : Fin 4 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 4) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 4) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∉ roots (isFiniteType_cartanD 4) ∅) (c d : K) :
    ⁅d4LeviPar K α c, d4LeviPar K β d⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  by_cases hαβ : α = β
  · subst hαβ
    rw [Commute, SemiconjBy, ← d4LeviPar_add, ← d4LeviPar_add, add_comm]
  · have hne₁ : d4EmbedE7 α ≠ d4EmbedE7 β := fun h => hαβ (d4EmbedE7_injective h)
    have hne₂ : d4EmbedE7 α ≠ -d4EmbedE7 β := fun h => hne (d4EmbedE7_injective (by
      rw [d4EmbedE7_add, h, d4EmbedE7_zero, neg_add_cancel]))
    have hr7 : ¬ IsRoot .E7 (d4EmbedE7 α + d4EmbedE7 β) := by
      rw [← d4EmbedE7_add, isRoot_d4EmbedE7_iff]
      exact hr
    have h := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
      (isRoot_d4EmbedE7 hα) (isRoot_d4EmbedE7 hβ) hne₁ hne₂).2 hr7 K
      (pinnedX .E7 K (d4EmbedE7 α) c) (subset_closure ⟨c, rfl⟩)
      (pinnedX .E7 K (d4EmbedE7 β) d) (subset_closure ⟨d, rfl⟩)
    exact Subtype.ext h

theorem commutatorFormula_d4LeviPar [CharP K 2] (O : CommOrder (SpinPlus.Φ 4 K three_le_rank_D4)) :
    CommutatorFormula (d4LeviPar K) O SpinPlus.commC := by
  intro α hα β hβ hαβ c d
  by_cases hr : α + β ∈ (SpinPlus.Φ 4 K three_le_rank_D4).roots
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).1 hr, List.map_singleton,
      List.prod_singleton, one_smul, one_smul, pow_one, pow_one,
      commutator_d4LeviPar_of_mem hα hβ hαβ hr, F4Pilot.commC_cast_eq_one_D4, one_mul]
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).2 hr, List.map_nil,
      List.prod_nil]
    exact commutator_d4LeviPar_of_not_mem hα hβ hαβ hr c d

end Commutators

section Hom

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def spinToE7D4 : spinGroup (quadPlus 4 K) →* ↥(adjointGroup .E7 K) :=
  liftOfPresentationB (SpinPlus.presentationB three_le_rank_D4) (F4Pilot.d4Order K)
    (SpinPlus.commutatorFormula three_le_rank_D4 (F4Pilot.d4Order K))
    (fun γ _ c d => d4LeviPar_add γ c d) (commutatorFormula_d4LeviPar (F4Pilot.d4Order K))

variable {K}

theorem spinToE7D4_x {γ : Fin 4 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c : K) :
    spinToE7D4 K (SpinPlus.x 4 K three_le_rank_D4 γ c) = d4LeviPar K γ c :=
  liftOfPresentationB_apply _ _ _ _ _ hγ c

theorem range_spinToE7D4 : (spinToE7D4 K).range = overlapSpanD4 K .high .seven := by
  rw [MonoidHom.range_eq_map, ← F4Pilot.closure_spinX_four_eq_top, MonoidHom.map_closure,
    overlapSpanD4_high_seven_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, (spinToE7D4_x hγ c).symm⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨_, ⟨γ, hγ, c, rfl⟩, spinToE7D4_x hγ c⟩

theorem exists_spinToE7D4_ne_one : ∃ g, spinToE7D4 K g ≠ 1 := by
  have hr : (Pi.single 0 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    (SpinPlus.Φ 4 K three_le_rank_D4).single_mem 0
  refine ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single 0 1) 1, fun h => ?_⟩
  rw [spinToE7D4_x hr, ← d4LeviPar_zero (Pi.single 0 1)] at h
  exact one_ne_zero (d4LeviPar_injective _ h)

theorem spinToE7D4_injective : Function.Injective (spinToE7D4 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← F4Pilot.center_spinGroup_quadPlus_four_eq_bot]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D4)
    exists_spinToE7D4_ne_one

variable (K) in
@[expose] noncomputable def spinEquivOverlapD4 :
    spinGroup (quadPlus 4 K) ≃* ↥(overlapSpanD4 K .high .seven) :=
  (MonoidHom.ofInjective spinToE7D4_injective).trans (MulEquiv.subgroupCongr range_spinToE7D4)

theorem isQuasisimple_overlapSpanD4_high_seven :
    CFSG.IsQuasisimple (overlapSpanD4 K .high .seven) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (spinEquivOverlapD4 K)
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D4)

theorem center_overlapSpanD4_high_seven_eq_bot : center (overlapSpanD4 K .high .seven) = ⊥ := by
  rw [← Subgroup.map_center_eq (spinEquivOverlapD4 K),
    F4Pilot.center_spinGroup_quadPlus_four_eq_bot, Subgroup.map_bot]

end Hom

section Transport

variable (K : Type) [Field K]

@[expose] noncomputable def wordRepE7 (ω : List (Fin (Tag.rank .E7))) : adjointGroup .E7 K :=
  (ω.map (CFSG.LieType.Chevalley.weylElement .E7 K)).prod

variable {K}

theorem coe_wordRepE7 (ω : List (Fin (Tag.rank .E7))) :
    (wordRepE7 K ω : ModGL .E7 K) = (ω.map fun i => weylElt .E7 K i 1).prod := by
  rw [wordRepE7, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

theorem map_conj_wordRepE7_rootSpan (ω : List (Fin (Tag.rank .E7)))
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E7 γ) :
    (rootSpan .E7 K S).map (MulAut.conj (wordRepE7 K ω : ModGL .E7 K)).toMonoidHom =
      rootSpan .E7 K ((fun α => (coxeterSystem .E7).wordProd ω • α) '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  refine iSup_congr fun γ => iSup_congr fun hγ => ?_
  rw [coe_wordRepE7]
  exact map_conj_prod_weylElt_rootSubgroup K ω (hS γ hγ)

theorem map_conj_wordRepE7_subgroupOf_rootSpan (ω : List (Fin (Tag.rank .E7)))
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .E7 γ) :
    ((rootSpan .E7 K S).subgroupOf (adjointGroup .E7 K)).map
        (MulAut.conj (wordRepE7 K ω)).toMonoidHom =
      (rootSpan .E7 K ((fun α => (coxeterSystem .E7).wordProd ω • α) '' S)).subgroupOf
        (adjointGroup .E7 K) := by
  apply Subgroup.map_injective (adjointGroup .E7 K).subtype_injective
  rw [map_conj_map_subtype_E7, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' S),
    inf_of_le_left (EPilot.rootSpan_le_adjointGroup' _), map_conj_wordRepE7_rootSpan ω hS]

theorem image_overlapWeyl_overlapRootsD4 {N N' : E7Neighbour} (h : N ≠ N') :
    (fun α => overlapWeyl N N' • α) '' overlapRootsD4 .high .seven = overlapRootsD4 N N' := by
  obtain ⟨h1, h2, h3⟩ := overlapWeyl_smul h
  rw [overlapRootsD4, overlapRootsD4, Set.image_inter (MulAction.injective _),
    Set.image_inter (MulAction.injective _), image_smul_orthRoots, image_smul_orthRoots,
    image_smul_orthRoots, thirdRoot_high_seven]
  change orthRoots (overlapWeyl N N' • highRoot .E7) ∩
      orthRoots (overlapWeyl N N' • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ)) ∩
      orthRoots (overlapWeyl N N' • d6HighRoot) = _
  rw [h1, h2, h3, Set.inter_right_comm]

theorem overlapSpanD4_eq_map_conj {N N' : E7Neighbour} (h : N ≠ N') :
    overlapSpanD4 K N N' = (overlapSpanD4 K .high .seven).map
      (MulAut.conj (wordRepE7 K (overlapWord N N'))).toMonoidHom := by
  rw [overlapSpanD4, overlapSpanD4,
    map_conj_wordRepE7_subgroupOf_rootSpan _ (fun γ hγ => hγ.2.1)]
  congr 2
  exact (image_overlapWeyl_overlapRootsD4 h).symm

end Transport

section Simple

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isQuasisimple_overlapSpanD4 {N N' : E7Neighbour} (h : N ≠ N') :
    CFSG.IsQuasisimple (overlapSpanD4 K N N') := by
  rw [overlapSpanD4_eq_map_conj h]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((overlapSpanD4 K .high .seven).equivMapOfInjective _ (MulAut.conj _).injective)
    isQuasisimple_overlapSpanD4_high_seven

theorem commutator_overlapSpanD4 {N N' : E7Neighbour} (h : N ≠ N') :
    ⁅overlapSpanD4 K N N', overlapSpanD4 K N N'⁆ = overlapSpanD4 K N N' :=
  Subgroup.isPerfect_iff.mp (isQuasisimple_overlapSpanD4 h).1

theorem center_overlapSpanD4_eq_bot {N N' : E7Neighbour} (h : N ≠ N') :
    center (overlapSpanD4 K N N') = ⊥ := by
  rw [overlapSpanD4_eq_map_conj h]
  exact F4Pilot.center_eq_bot_congr
    ((overlapSpanD4 K .high .seven).equivMapOfInjective _ (MulAut.conj _).injective)
    center_overlapSpanD4_high_seven_eq_bot

theorem isSimpleGroup_overlapSpanD4 {N N' : E7Neighbour} (h : N ≠ N') :
    IsSimpleGroup (overlapSpanD4 K N N') := by
  have hq := isQuasisimple_overlapSpanD4 (K := K) h
  have hZ := center_overlapSpanD4_eq_bot (K := K) h
  have e : overlapSpanD4 K N N' ⧸ center (overlapSpanD4 K N N') ≃* overlapSpanD4 K N N' :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact @MulEquiv.isSimpleGroup _ _ _ _ hq.2.1 e.symm

end Simple

end CFSG.SeitzReduction.E7Pilot

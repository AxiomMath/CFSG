module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourRoots
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Commutator

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.EPilot
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open scoped commutatorElement

theorem three_le_rank_D6 : 3 ≤ 6 := by norm_num

section Levi


variable (K : Type) [Field K]

@[expose] noncomputable def d6LeviPar (γ : Fin 6 → ℤ) (c : K) : ↥(adjointGroup .E7 K) :=
  ⟨pinnedX .E7 K (d6Embed γ) c, pinnedX_mem_adjointGroup _ c⟩

variable {K}

theorem coe_d6LeviPar (γ : Fin 6 → ℤ) (c : K) :
    ((d6LeviPar K γ c : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K (d6Embed γ) c :=
  rfl

theorem d6LeviPar_add (γ : Fin 6 → ℤ) (c d : K) :
    d6LeviPar K γ (c + d) = d6LeviPar K γ c * d6LeviPar K γ d :=
  Subtype.ext (pinnedX_add .E7 K _ c d)

theorem d6LeviPar_zero (γ : Fin 6 → ℤ) : d6LeviPar K γ 0 = 1 :=
  Subtype.ext (pinnedX_zero .E7 K _)

theorem d6LeviPar_injective (γ : Fin 6 → ℤ) : Function.Injective (d6LeviPar K γ) :=
  fun _ _ h => pinnedX_injective .E7 K _ (congrArg Subtype.val h :)

theorem map_subtype_perpLevi_E7 :
    (perpLevi .E7 K).map (adjointGroup .E7 K).subtype = rootSpan .E7 K (perpRoots .E7) := by
  rw [perpLevi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup' _)]

theorem rootSpan_perpRoots_E7_eq_closure :
    rootSpan .E7 K (perpRoots .E7) =
      closure {g | ∃ γ ∈ roots (isFiniteType_cartanD 6) ∅, ∃ c : K,
        pinnedX .E7 K (d6Embed γ) c = g} := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · obtain ⟨v, hv, rfl⟩ := exists_d6Embed_eq_of_mem_perpRoots hγ
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact subset_closure ⟨v, hv, c, rfl⟩
  · rintro _ ⟨γ, hγ, c, rfl⟩
    exact le_iSup₂ (f := fun γ (_ : γ ∈ perpRoots .E7) => rootSubgroup .E7 K γ) (d6Embed γ)
      (d6Embed_mem_perpRoots hγ) (subset_closure ⟨c, rfl⟩)

theorem d6LeviPar_mem_perpLevi {γ : Fin 6 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅)
    (c : K) : d6LeviPar K γ c ∈ perpLevi .E7 K := by
  rw [perpLevi, mem_subgroupOf, rootSpan_perpRoots_E7_eq_closure]
  exact subset_closure ⟨γ, hγ, c, rfl⟩

theorem perpLevi_E7_eq_closure :
    perpLevi .E7 K =
      closure {g | ∃ γ ∈ roots (isFiniteType_cartanD 6) ∅, ∃ c : K, d6LeviPar K γ c = g} := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  rw [map_subtype_perpLevi_E7, rootSpan_perpRoots_E7_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨d6LeviPar K γ c, ⟨γ, hγ, c, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, rfl⟩

end Levi

section Commutators

variable {K : Type} [Field K] [CharP K 2]

theorem intCast_eq_one_of_charTwo_D6 {C : ℤ} (h : C = 1 ∨ C = -1) : (C : K) = 1 := by
  rcases h with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

theorem commC_cast_eq_one (α β : Fin 6 → ℤ) (p : ℕ × ℕ) :
    ((SpinPlus.commC α β p : ℤ) : K) = 1 := by
  have h := SpinPlus.commC_natAbs α β p
  exact intCast_eq_one_of_charTwo_D6 (Int.natAbs_eq_iff.1 h |>.imp (by simp) (by simp))


theorem commutator_d6LeviPar_of_mem {α β : Fin 6 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 6) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 6) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∈ roots (isFiniteType_cartanD 6) ∅) (c d : K) :
    ⁅d6LeviPar K α c, d6LeviPar K β d⁆ = d6LeviPar K (α + β) (c * d) := by
  have hαβ : α ≠ β := fun h => add_self_not_mem_rootsD (h ▸ hr)
  have hne₁ : d6Embed α ≠ d6Embed β := fun h => hαβ (d6Embed_injective h)
  have hne₂ : d6Embed α ≠ -d6Embed β := fun h => hne (d6Embed_injective (by
    rw [d6Embed_add, h, d6Embed_zero, neg_add_cancel]))
  have hr7 : IsRoot .E7 (d6Embed α + d6Embed β) := by
    rw [← d6Embed_add]
    exact isRoot_d6Embed hr
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
    (isRoot_d6Embed hα) (isRoot_d6Embed hβ) hne₁ hne₂).1 hr7
  apply Subtype.ext
  rw [show ((⁅d6LeviPar K α c, d6LeviPar K β d⁆ : adjointGroup .E7 K) : ModGL .E7 K) =
      ⁅((d6LeviPar K α c : adjointGroup .E7 K) : ModGL .E7 K),
        ((d6LeviPar K β d : adjointGroup .E7 K) : ModGL .E7 K)⁆ from
      map_commutatorElement (adjointGroup .E7 K).subtype _ _,
    coe_d6LeviPar, coe_d6LeviPar, coe_d6LeviPar, hF K c d,
    intCast_eq_one_of_charTwo_D6 hC, one_mul, d6Embed_add]

omit [CharP K 2] in
theorem commutator_d6LeviPar_of_not_mem {α β : Fin 6 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 6) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 6) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∉ roots (isFiniteType_cartanD 6) ∅) (c d : K) :
    ⁅d6LeviPar K α c, d6LeviPar K β d⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  by_cases hαβ : α = β
  · subst hαβ
    rw [Commute, SemiconjBy, ← d6LeviPar_add, ← d6LeviPar_add, add_comm]
  · have hne₁ : d6Embed α ≠ d6Embed β := fun h => hαβ (d6Embed_injective h)
    have hne₂ : d6Embed α ≠ -d6Embed β := fun h => hne (d6Embed_injective (by
      rw [d6Embed_add, h, d6Embed_zero, neg_add_cancel]))
    have hr7 : ¬ IsRoot .E7 (d6Embed α + d6Embed β) := by
      rw [← d6Embed_add, isRoot_d6Embed_iff]
      exact hr
    have h := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
      (isRoot_d6Embed hα) (isRoot_d6Embed hβ) hne₁ hne₂).2 hr7 K
      (pinnedX .E7 K (d6Embed α) c) (subset_closure ⟨c, rfl⟩)
      (pinnedX .E7 K (d6Embed β) d) (subset_closure ⟨d, rfl⟩)
    exact Subtype.ext h

theorem commutatorFormula_d6LeviPar (O : CommOrder (SpinPlus.Φ 6 K three_le_rank_D6)) :
    CommutatorFormula (d6LeviPar K) O SpinPlus.commC := by
  intro α hα β hβ hαβ c d
  by_cases hr : α + β ∈ (SpinPlus.Φ 6 K three_le_rank_D6).roots
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D6 O hα hβ hαβ).1 hr, List.map_singleton,
      List.prod_singleton, one_smul, one_smul, pow_one, pow_one,
      commutator_d6LeviPar_of_mem hα hβ hαβ hr, commC_cast_eq_one, one_mul]
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D6 O hα hβ hαβ).2 hr, List.map_nil, List.prod_nil]
    exact commutator_d6LeviPar_of_not_mem hα hβ hαβ hr c d

end Commutators

end CFSG.SeitzReduction.E7Pilot

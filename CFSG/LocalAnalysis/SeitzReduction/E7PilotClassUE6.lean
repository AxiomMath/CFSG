module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUE6Roots
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Steinberg.Isogeny.Lift

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Levi

variable (K : Type) [Field K]

@[expose] def e6LeviRoots : Set (Fin (Tag.rank .E7) → ℤ) := {γ | IsRoot .E7 γ ∧ γ e7LastNode = 0}

@[expose] noncomputable def e6Levi : Subgroup ↥(adjointGroup .E7 K) :=
  (rootSpan .E7 K e6LeviRoots).subgroupOf (adjointGroup .E7 K)

@[expose] noncomputable def e6LeviPar (γ : Fin (Tag.rank .E6) → ℤ) (c : K) :
    ↥(adjointGroup .E7 K) :=
  ⟨pinnedX .E7 K (e6Embed γ) c, pinnedX_mem_adjointGroup _ c⟩

variable {K}

theorem coe_e6LeviPar (γ : Fin (Tag.rank .E6) → ℤ) (c : K) :
    ((e6LeviPar K γ c : adjointGroup .E7 K) : ModGL .E7 K) = pinnedX .E7 K (e6Embed γ) c :=
  rfl

theorem e6LeviPar_add (γ : Fin (Tag.rank .E6) → ℤ) (c d : K) :
    e6LeviPar K γ (c + d) = e6LeviPar K γ c * e6LeviPar K γ d :=
  Subtype.ext (pinnedX_add .E7 K _ c d)

theorem e6LeviPar_zero (γ : Fin (Tag.rank .E6) → ℤ) : e6LeviPar K γ 0 = 1 :=
  Subtype.ext (pinnedX_zero .E7 K _)

theorem e6LeviPar_injective (γ : Fin (Tag.rank .E6) → ℤ) : Function.Injective (e6LeviPar K γ) :=
  fun _ _ h => pinnedX_injective .E7 K _ (congrArg Subtype.val h :)

theorem rootSpan_le_adjointGroup_E7 (S : Set (Fin (Tag.rank .E7) → ℤ)) :
    rootSpan .E7 K S ≤ adjointGroup .E7 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem map_subtype_e6Levi :
    (e6Levi K).map (adjointGroup .E7 K).subtype = rootSpan .E7 K e6LeviRoots := by
  rw [e6Levi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_E7 _)]

theorem rootSpan_e6LeviRoots_eq_closure :
    rootSpan .E7 K e6LeviRoots =
      closure {g | ∃ γ, IsRoot .E6 γ ∧ ∃ c : K, pinnedX .E7 K (e6Embed γ) c = g} := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · obtain ⟨v, hv, rfl⟩ := exists_e6Embed_eq hγ.1 hγ.2
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact subset_closure ⟨v, hv, c, rfl⟩
  · rintro _ ⟨γ, hγ, c, rfl⟩
    exact le_iSup₂ (f := fun γ (_ : γ ∈ e6LeviRoots) => rootSubgroup .E7 K γ) (e6Embed γ)
      ⟨isRoot_e6Embed hγ, e6Embed_last γ⟩ (subset_closure ⟨c, rfl⟩)

theorem e6Levi_eq_closure :
    e6Levi K = closure {g | ∃ γ, IsRoot .E6 γ ∧ ∃ c : K, e6LeviPar K γ c = g} := by
  apply map_injective (adjointGroup .E7 K).subtype_injective
  rw [map_subtype_e6Levi, rootSpan_e6LeviRoots_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨e6LeviPar K γ c, ⟨γ, hγ, c, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, rfl⟩

end Levi

section Commutators

variable {K : Type} [Field K] [CharP K 2]

theorem intCast_eq_one_of_charTwo' {C : ℤ} (h : C = 1 ∨ C = -1) : (C : K) = 1 := by
  rcases h with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

theorem eq_one_of_isSign_of_charTwo' {σ : K} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

set_option maxRecDepth 100000 in
theorem add_self_not_mem_rootFinset_E6 :
    ∀ γ ∈ rootFinset .E6, γ + γ ∉ rootFinset .E6 := by
  decide +kernel

theorem not_isRoot_add_self_E6
    {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) : ¬ IsRoot .E6 (α + α) := fun h =>
  add_self_not_mem_rootFinset_E6 α (mem_rootFinset.2 hα) (mem_rootFinset.2 h)

theorem commutator_e6LeviPar_of_isRoot {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (hne : α + β ≠ 0) (hr : IsRoot .E6 (α + β)) (c d : K) :
    ⁅e6LeviPar K α c, e6LeviPar K β d⁆ = e6LeviPar K (α + β) (c * d) := by
  have hαβ : α ≠ β := fun h => not_isRoot_add_self_E6 hα (h ▸ hr)
  have hne₁ : e6Embed α ≠ e6Embed β := fun h => hαβ (e6Embed_injective h)
  have hne₂ : e6Embed α ≠ -e6Embed β := fun h => hne (e6Embed_injective (by
    rw [e6Embed_add, h, e6Embed_zero, neg_add_cancel]))
  have hr7 : IsRoot .E7 (e6Embed α + e6Embed β) := by
    rw [← e6Embed_add]
    exact isRoot_e6Embed hr
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
    (isRoot_e6Embed hα) (isRoot_e6Embed hβ) hne₁ hne₂).1 hr7
  apply Subtype.ext
  rw [show ((⁅e6LeviPar K α c, e6LeviPar K β d⁆ : adjointGroup .E7 K) : ModGL .E7 K) =
      ⁅((e6LeviPar K α c : adjointGroup .E7 K) : ModGL .E7 K),
        ((e6LeviPar K β d : adjointGroup .E7 K) : ModGL .E7 K)⁆ from
      map_commutatorElement (adjointGroup .E7 K).subtype _ _,
    coe_e6LeviPar, coe_e6LeviPar, coe_e6LeviPar, hF K c d,
    intCast_eq_one_of_charTwo' hC, one_mul, e6Embed_add]

omit [CharP K 2] in
theorem commutator_e6LeviPar_of_not_isRoot {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hβ : IsRoot .E6 β) (hne : α + β ≠ 0) (hr : ¬ IsRoot .E6 (α + β)) (c d : K) :
    ⁅e6LeviPar K α c, e6LeviPar K β d⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  by_cases hαβ : α = β
  · subst hαβ
    rw [Commute, SemiconjBy, ← e6LeviPar_add, ← e6LeviPar_add, add_comm]
  · have hne₁ : e6Embed α ≠ e6Embed β := fun h => hαβ (e6Embed_injective h)
    have hne₂ : e6Embed α ≠ -e6Embed β := fun h => hne (e6Embed_injective (by
      rw [e6Embed_add, h, e6Embed_zero, neg_add_cancel]))
    have hr7 : ¬ IsRoot .E7 (e6Embed α + e6Embed β) := by
      rw [← e6Embed_add, isRoot_e6Embed_iff]
      exact hr
    have h := (simply_laced_root_commutator_unit .E7 (Or.inr (Or.inr (Or.inl rfl)))
      (isRoot_e6Embed hα) (isRoot_e6Embed hβ) hne₁ hne₂).2 hr7 K
      (pinnedX .E7 K (e6Embed α) c) (subset_closure ⟨c, rfl⟩)
      (pinnedX .E7 K (e6Embed β) d) (subset_closure ⟨d, rfl⟩)
    exact Subtype.ext h

theorem commutator_xm_of_isRoot_of_charTwo_E6
    {α β : Fin (Tag.rank .E6) → ℤ}
    (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α + β ≠ 0) (hr : IsRoot .E6 (α + β))
    (c d : K) :
    ⁅e6Data_valid.xm K α c, e6Data_valid.xm K β d⁆ = e6Data_valid.xm K (α + β) (c * d) := by
  obtain ⟨σ, hσ, h⟩ := (e6Data_valid.commutator_xm K hα hβ hne).1 hr
  rw [h, eq_one_of_isSign_of_charTwo' hσ, one_mul]

theorem sameCommutators_xm_e6LeviPar
    {α β : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hne : α + β ≠ 0) :
    CFSG.LieType.Steinberg.SameCommutators (e6Data_valid.xm K) (e6LeviPar K) α β := by
  refine ⟨fun hr => ⟨1, fun c d => ?_, fun c d => ?_⟩, fun hr =>
    ⟨fun c d => (e6Data_valid.commutator_xm K hα hβ hne).2 hr c d,
      fun c d => commutator_e6LeviPar_of_not_isRoot hα hβ hne hr c d⟩⟩
  · rw [one_mul, commutator_xm_of_isRoot_of_charTwo_E6 hα hβ hne hr]
  · rw [one_mul, commutator_e6LeviPar_of_isRoot hα hβ hne hr]

end Commutators

section Hom

noncomputable abbrev e6Sys :
    CFSG.LieType.Steinberg.RootSystem (Fin (Tag.rank .E6)) :=
  CFSG.LieType.Steinberg.RootSystem.ofCartan isFiniteType_cartan_E6 ∅

theorem e6Sys_roots :
    e6Sys.roots = {γ | IsRoot .E6 γ} :=
  roots_eq isFiniteType_cartan_E6

variable (K : Type) [Field K] [CharP K 2]

theorem commutatorFormula_e6LeviPar {O : CommOrder e6Sys}
    {C : (Fin (Tag.rank .E6) → ℤ) → (Fin (Tag.rank .E6) → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (e6Data_valid.xm K) O C) : CommutatorFormula (e6LeviPar K) O C :=
  CFSG.LieType.Steinberg.commutatorFormula_of_sameCommutators e6Sys_roots
    (fun _ hα _ hβ hne hr => list_eq_singleton_of_isRoot posDef_cartan_E6 e6Sys_roots O hα hβ hne hr)
    (fun _ hα _ hβ hne hr => list_eq_nil_of_not_isRoot posDef_cartan_E6 e6Sys_roots O hα hβ hne hr)
    (fun _ hγ => e6Data_valid.xm_injective K hγ)
    (fun _ _ hα hβ hne => sameCommutators_xm_e6LeviPar hα hβ hne) hC

variable [Finite K]

@[expose] noncomputable def e6ToE7 : ↥(e6Data_valid.minGroup K) →* ↥(adjointGroup .E7 K) :=
  CFSG.LieType.Steinberg.liftOfPresentationB (e6_presentationB K)
    (commOrder posDef_cartan_E6 e6Sys e6Sys_roots)
    (e6Data_valid.commutatorFormula_commC K posDef_cartan_E6 e6Sys e6Sys_roots _)
    (fun γ _ c d => e6LeviPar_add γ c d)
    (commutatorFormula_e6LeviPar K
      (e6Data_valid.commutatorFormula_commC K posDef_cartan_E6 e6Sys e6Sys_roots _))

variable {K}

theorem e6ToE7_xm {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : K) :
    e6ToE7 K (e6Data_valid.xm K γ c) = e6LeviPar K γ c :=
  CFSG.LieType.Steinberg.liftOfPresentationB_apply _ _ _ _ _
    (by rw [e6Sys_roots]; exact hγ) c

omit [CharP K 2] [Finite K]
  in
theorem closure_xm_eq_top_E6 :
    closure {g : e6Data_valid.minGroup K | ∃ γ, IsRoot .E6 γ ∧ ∃ c : K,
      e6Data_valid.xm K γ c = g} = ⊤ := by
  have h := closure_closure_coe_preimage (k := {g | ∃ γ, IsRoot .E6 γ ∧ ∃ c : K,
    g = e6Data_valid.xu K γ c})
  refine Eq.trans ?_ h
  congr 1
  ext g
  exact ⟨fun ⟨γ, hγ, c, hc⟩ => ⟨γ, hγ, c, by rw [← hc]; rfl⟩,
    fun ⟨γ, hγ, c, hc⟩ => ⟨γ, hγ, c, Subtype.ext hc.symm⟩⟩

theorem range_e6ToE7 : (e6ToE7 K).range = e6Levi K := by
  rw [MonoidHom.range_eq_map, ← closure_xm_eq_top_E6, MonoidHom.map_closure, e6Levi_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, (e6ToE7_xm hγ c).symm⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨_, ⟨γ, hγ, c, rfl⟩, e6ToE7_xm hγ c⟩

theorem exists_e6ToE7_ne_one : ∃ g, e6ToE7 K g ≠ 1 := by
  have h0 : (0 : ℕ) < Tag.rank .E6 := by decide
  refine ⟨e6Data_valid.xm K (Pi.single ⟨0, h0⟩ 1) 1, fun h => ?_⟩
  rw [e6ToE7_xm (isRoot_single .E6 _), ← e6LeviPar_zero (Pi.single ⟨0, h0⟩ 1)] at h
  exact one_ne_zero (e6LeviPar_injective _ h)

theorem ker_e6ToE7_le_center : (e6ToE7 K).ker ≤ center ↥(e6Data_valid.minGroup K) :=
  CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 K) exists_e6ToE7_ne_one

end Hom

end CFSG.SeitzReduction.E7Pilot

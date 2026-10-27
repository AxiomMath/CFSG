module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviRoots
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction.EPilot
open scoped commutatorElement

section Levi


variable (K : Type) [Field K]

@[expose] noncomputable def e7Levi : Subgroup ↥(adjointGroup .E8 K) :=
  (rootSpan .E8 K (perpRoots .E8)).subgroupOf (adjointGroup .E8 K)

@[expose] noncomputable def e7LeviPar (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    ↥(adjointGroup .E8 K) :=
  ⟨pinnedX .E8 K (e7Embed γ) c, pinnedX_mem_adjointGroup _ c⟩

variable {K}

theorem coe_e7LeviPar (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    ((e7LeviPar K γ c : adjointGroup .E8 K) : ModGL .E8 K) = pinnedX .E8 K (e7Embed γ) c :=
  rfl

theorem e7LeviPar_add (γ : Fin (Tag.rank .E7) → ℤ) (c d : K) :
    e7LeviPar K γ (c + d) = e7LeviPar K γ c * e7LeviPar K γ d :=
  Subtype.ext (pinnedX_add .E8 K _ c d)

theorem e7LeviPar_zero (γ : Fin (Tag.rank .E7) → ℤ) : e7LeviPar K γ 0 = 1 :=
  Subtype.ext (pinnedX_zero .E8 K _)

theorem e7LeviPar_injective (γ : Fin (Tag.rank .E7) → ℤ) : Function.Injective (e7LeviPar K γ) :=
  fun _ _ h => pinnedX_injective .E8 K _ (congrArg Subtype.val h :)

theorem mem_e7Levi_iff {g : adjointGroup .E8 K} :
    g ∈ e7Levi K ↔ (g : ModGL .E8 K) ∈ rootSpan .E8 K (perpRoots .E8) :=
  mem_subgroupOf

theorem rootSpan_le_adjointGroup_E8 (S : Set (Fin (Tag.rank .E8) → ℤ)) :
    rootSpan .E8 K S ≤ adjointGroup .E8 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem map_subtype_e7Levi :
    (e7Levi K).map (adjointGroup .E8 K).subtype = rootSpan .E8 K (perpRoots .E8) := by
  rw [e7Levi, subgroupOf_map_subtype, inf_of_le_left (rootSpan_le_adjointGroup_E8 _)]

theorem rootSpan_perpRoots_eq_closure :
    rootSpan .E8 K (perpRoots .E8) =
      closure {g | ∃ γ, IsRoot .E7 γ ∧ ∃ c : K, pinnedX .E8 K (e7Embed γ) c = g} := by
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) ((closure_le _).2 ?_)
  · obtain ⟨v, hv, rfl⟩ := exists_e7Embed_eq_of_mem_perpRoots hγ
    refine (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact subset_closure ⟨v, hv, c, rfl⟩
  · rintro _ ⟨γ, hγ, c, rfl⟩
    exact le_iSup₂ (f := fun γ (_ : γ ∈ perpRoots .E8) => rootSubgroup .E8 K γ) (e7Embed γ)
      (e7Embed_mem_perpRoots hγ) (subset_closure ⟨c, rfl⟩)

theorem e7LeviPar_mem_e7Levi {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    e7LeviPar K γ c ∈ e7Levi K := by
  rw [mem_e7Levi_iff, rootSpan_perpRoots_eq_closure]
  exact subset_closure ⟨γ, hγ, c, rfl⟩

theorem e7Levi_eq_closure :
    e7Levi K = closure {g | ∃ γ, IsRoot .E7 γ ∧ ∃ c : K, e7LeviPar K γ c = g} := by
  apply map_injective (adjointGroup .E8 K).subtype_injective
  rw [map_subtype_e7Levi, rootSpan_perpRoots_eq_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨e7LeviPar K γ c, ⟨γ, hγ, c, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, rfl⟩

end Levi

section Commutators

variable {K : Type} [Field K] [CharP K 2]

theorem intCast_eq_one_of_charTwo {C : ℤ} (h : C = 1 ∨ C = -1) : (C : K) = 1 := by
  rcases h with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

theorem eq_one_of_isSign_of_charTwo {σ : K} (h : IsSign σ) : σ = 1 := by
  rcases h with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem not_isRoot_add_self_E7 {α : Fin (Tag.rank .E7) → ℤ} :
    ¬ IsRoot .E7 (α + α) := by
  intro h
  have h2 := iform_self_eq_two (τ := .E7) (Or.inr (Or.inl rfl)) h
  have h1 : iform (α + α) (α + α) = 4 * iform α α := by
    simp only [iform_add_left, iform_add_right]
    ring
  have h3 : (2 : ℤ) = 4 * iform α α := h2 ▸ h1
  omega


theorem commutator_e7LeviPar_of_isRoot {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α)
    (hβ : IsRoot .E7 β) (hne : α + β ≠ 0) (hr : IsRoot .E7 (α + β)) (c d : K) :
    ⁅e7LeviPar K α c, e7LeviPar K β d⁆ = e7LeviPar K (α + β) (c * d) := by
  have hαβ : α ≠ β := fun h => not_isRoot_add_self_E7 (h ▸ hr)
  have hne₁ : e7Embed α ≠ e7Embed β := fun h => hαβ (e7Embed_injective h)
  have hne₂ : e7Embed α ≠ -e7Embed β := fun h => hne (e7Embed_injective (by
    rw [e7Embed_add, h, e7Embed_zero, neg_add_cancel]))
  have hr8 : IsRoot .E8 (e7Embed α + e7Embed β) := by
    rw [← e7Embed_add]
    exact isRoot_e7Embed hr
  obtain ⟨hC, hF⟩ := (simply_laced_root_commutator_unit .E8 (Or.inr (Or.inr (Or.inr rfl)))
    (isRoot_e7Embed hα) (isRoot_e7Embed hβ) hne₁ hne₂).1 hr8
  apply Subtype.ext
  rw [show ((⁅e7LeviPar K α c, e7LeviPar K β d⁆ : adjointGroup .E8 K) : ModGL .E8 K) =
      ⁅((e7LeviPar K α c : adjointGroup .E8 K) : ModGL .E8 K),
        ((e7LeviPar K β d : adjointGroup .E8 K) : ModGL .E8 K)⁆ from
      map_commutatorElement (adjointGroup .E8 K).subtype _ _,
    coe_e7LeviPar, coe_e7LeviPar, coe_e7LeviPar, hF K c d,
    intCast_eq_one_of_charTwo hC, one_mul, e7Embed_add]

omit [CharP K 2] in
theorem commutator_e7LeviPar_of_not_isRoot {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α)
    (hβ : IsRoot .E7 β) (hne : α + β ≠ 0) (hr : ¬ IsRoot .E7 (α + β)) (c d : K) :
    ⁅e7LeviPar K α c, e7LeviPar K β d⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  by_cases hαβ : α = β
  · subst hαβ
    rw [Commute, SemiconjBy, ← e7LeviPar_add, ← e7LeviPar_add, add_comm]
  · have hne₁ : e7Embed α ≠ e7Embed β := fun h => hαβ (e7Embed_injective h)
    have hne₂ : e7Embed α ≠ -e7Embed β := fun h => hne (e7Embed_injective (by
      rw [e7Embed_add, h, e7Embed_zero, neg_add_cancel]))
    have hr8 : ¬ IsRoot .E8 (e7Embed α + e7Embed β) := by
      rw [← e7Embed_add, isRoot_e7Embed_iff]
      exact hr
    have h := (simply_laced_root_commutator_unit .E8 (Or.inr (Or.inr (Or.inr rfl)))
      (isRoot_e7Embed hα) (isRoot_e7Embed hβ) hne₁ hne₂).2 hr8 K
      (pinnedX .E8 K (e7Embed α) c) (subset_closure ⟨c, rfl⟩)
      (pinnedX .E8 K (e7Embed β) d) (subset_closure ⟨d, rfl⟩)
    exact Subtype.ext h

theorem commutator_xm_of_isRoot_of_charTwo
    {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α + β ≠ 0) (hr : IsRoot .E7 (α + β))
    (c d : K) :
    ⁅e7Data_valid.xm K α c, e7Data_valid.xm K β d⁆ = e7Data_valid.xm K (α + β) (c * d) := by
  obtain ⟨σ, hσ, h⟩ := (e7Data_valid.commutator_xm K hα hβ hne).1 hr
  rw [h, eq_one_of_isSign_of_charTwo hσ, one_mul]

theorem sameCommutators_xm_e7LeviPar
    {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β) (hne : α + β ≠ 0) :
    SameCommutators (e7Data_valid.xm K) (e7LeviPar K) α β := by
  refine ⟨fun hr => ⟨1, fun c d => ?_, fun c d => ?_⟩, fun hr =>
    ⟨fun c d => (e7Data_valid.commutator_xm K hα hβ hne).2 hr c d,
      fun c d => commutator_e7LeviPar_of_not_isRoot hα hβ hne hr c d⟩⟩
  · rw [one_mul, commutator_xm_of_isRoot_of_charTwo hα hβ hne hr]
  · rw [one_mul, commutator_e7LeviPar_of_isRoot hα hβ hne hr]

end Commutators

section Hom

noncomputable abbrev e7Sys :
    CFSG.LieType.Steinberg.RootSystem (Fin (Tag.rank .E7)) :=
  CFSG.LieType.Steinberg.RootSystem.ofCartan isFiniteType_cartan_E7 ∅

theorem e7Sys_roots :
    e7Sys.roots = {γ | IsRoot .E7 γ} :=
  roots_eq isFiniteType_cartan_E7


variable (K : Type) [Field K] [CharP K 2]

theorem commutatorFormula_e7LeviPar {O : CommOrder e7Sys}
    {C : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula (e7Data_valid.xm K) O C) : CommutatorFormula (e7LeviPar K) O C :=
  commutatorFormula_of_sameCommutators e7Sys_roots
    (fun _ hα _ hβ hne hr => list_eq_singleton_of_isRoot posDef_cartan_E7 e7Sys_roots O hα hβ hne hr)
    (fun _ hα _ hβ hne hr => list_eq_nil_of_not_isRoot posDef_cartan_E7 e7Sys_roots O hα hβ hne hr)
    (fun _ hγ => e7Data_valid.xm_injective K hγ)
    (fun _ _ hα hβ hne => sameCommutators_xm_e7LeviPar hα hβ hne) hC

variable [Finite K]

@[expose] noncomputable def e7ToE8 : ↥(e7Data_valid.minGroup K) →* ↥(adjointGroup .E8 K) :=
  liftOfPresentationB (e7_presentationB K) (commOrder posDef_cartan_E7 e7Sys e7Sys_roots)
    (e7Data_valid.commutatorFormula_commC K posDef_cartan_E7 e7Sys e7Sys_roots _)
    (fun γ _ c d => e7LeviPar_add γ c d)
    (commutatorFormula_e7LeviPar K
      (e7Data_valid.commutatorFormula_commC K posDef_cartan_E7 e7Sys e7Sys_roots _))

variable {K}

theorem e7ToE8_xm {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    e7ToE8 K (e7Data_valid.xm K γ c) = e7LeviPar K γ c :=
  liftOfPresentationB_apply _ _ _ _ _ (by rw [e7Sys_roots]; exact hγ) c

theorem coe_e7ToE8_xm {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    ((e7ToE8 K (e7Data_valid.xm K γ c) : adjointGroup .E8 K) : ModGL .E8 K) =
      pinnedX .E8 K (e7Embed γ) c := by
  rw [e7ToE8_xm hγ]
  rfl

omit [CharP K 2] [Finite K]
  in
theorem closure_xm_eq_top :
    closure {g : e7Data_valid.minGroup K | ∃ γ, IsRoot .E7 γ ∧ ∃ c : K,
      e7Data_valid.xm K γ c = g} = ⊤ := by
  have h := closure_closure_coe_preimage (k := {g | ∃ γ, IsRoot .E7 γ ∧ ∃ c : K,
    g = e7Data_valid.xu K γ c})
  refine Eq.trans ?_ h
  congr 1
  ext g
  exact ⟨fun ⟨γ, hγ, c, hc⟩ => ⟨γ, hγ, c, by rw [← hc]; rfl⟩,
    fun ⟨γ, hγ, c, hc⟩ => ⟨γ, hγ, c, Subtype.ext hc.symm⟩⟩

theorem range_e7ToE8 : (e7ToE8 K).range = e7Levi K := by
  rw [MonoidHom.range_eq_map, ← closure_xm_eq_top, MonoidHom.map_closure, e7Levi_eq_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    exact ⟨γ, hγ, c, (e7ToE8_xm hγ c).symm⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    exact ⟨_, ⟨γ, hγ, c, rfl⟩, e7ToE8_xm hγ c⟩

theorem e7ToE8_mem_e7Levi (g : e7Data_valid.minGroup K) : e7ToE8 K g ∈ e7Levi K := by
  rw [← range_e7ToE8]
  exact ⟨g, rfl⟩

theorem exists_e7ToE8_ne_one : ∃ g, e7ToE8 K g ≠ 1 := by
  have h0 : (0 : ℕ) < Tag.rank .E7 := by decide
  refine ⟨e7Data_valid.xm K (Pi.single ⟨0, h0⟩ 1) 1, fun h => ?_⟩
  rw [e7ToE8_xm (isRoot_single .E7 _), ← e7LeviPar_zero (Pi.single ⟨0, h0⟩ 1)] at h
  exact one_ne_zero (e7LeviPar_injective _ h)

end Hom

section Centre


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem center_minGroup_e7_eq_bot : center ↥(e7Data_valid.minGroup K) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h2 : z ^ 2 = 1 := CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_two_e7 K hz
  have hq : z ^ (Nat.card K - 1) = 1 :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.center_pow_eq_one (e7Datum_isCTGroupDatum K)
      (e7Datum_steinbergExtras K) (e7Datum_bruhatExtras K)
      (fun i _ hh => CFSG.ClassicalInvolution.ModelFacts.ChevAut.torus_pow_card_sub_one
        e7Data_valid K i hh) z hz
  have hodd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    obtain ⟨m, hm⟩ := F4Pilot.two_dvd_natCard_of_charP_two (K := K)
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hm' : Nat.card K - 1 = 2 * (m - 1) + 1 := by omega
    rw [hm', Nat.gcd_comm, Nat.gcd_mul_left_add_left, Nat.gcd_one_left]
  have h1 := (pow_gcd_eq_one (a := z) (m := 2) (n := Nat.card K - 1)).2 ⟨h2, hq⟩
  rw [hodd, pow_one] at h1
  exact (mem_bot).2 h1

end Centre

section Equiv


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e7ToE8_injective : Function.Injective (e7ToE8 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_minGroup_e7_eq_bot (K := K)]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 K) exists_e7ToE8_ne_one

variable (K) in
@[expose] noncomputable def e7MinEquivLevi : ↥(e7Data_valid.minGroup K) ≃* ↥(e7Levi K) :=
  (MonoidHom.ofInjective e7ToE8_injective).trans (MulEquiv.subgroupCongr range_e7ToE8)

theorem coe_e7MinEquivLevi (g : e7Data_valid.minGroup K) :
    ((e7MinEquivLevi K g : e7Levi K) : adjointGroup .E8 K) = e7ToE8 K g :=
  rfl

theorem e7MinEquivLevi_xm {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) :
    e7MinEquivLevi K (e7Data_valid.xm K γ c) = ⟨e7LeviPar K γ c, e7LeviPar_mem_e7Levi hγ c⟩ :=
  Subtype.ext (e7ToE8_xm hγ c)

end Equiv

end CFSG.SeitzReduction.E8Pilot

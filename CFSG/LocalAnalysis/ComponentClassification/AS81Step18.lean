module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fix

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isActionHom_subtype_comp {Ω : Type} [Group Ω] {M T : Subgroup Ω} (hMT : M ≤ T)
    {L : Subgroup G} {ψ : normalizer (L : Set G) →* ↥T} (hψ : IsActionHom L (M.subgroupOf T) ψ) :
    IsActionHom L M (T.subtype.comp ψ) where
  map_mem a ha := hψ.map_mem a ha
  exists_eq x hx := by
    obtain ⟨a, ha, hae⟩ := hψ.exists_eq ⟨x, hMT hx⟩ hx
    exact ⟨a, ha, by rw [MonoidHom.comp_apply, hae]; rfl⟩
  eq_one_iff n := by
    rw [MonoidHom.comp_apply, ← hψ.eq_one_iff n]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

omit [Finite G] in
theorem range_subtype_comp_le {Ω : Type} [Group Ω] {T : Subgroup Ω} {L : Subgroup G}
    (ψ : normalizer (L : Set G) →* ↥T) : (T.subtype.comp ψ).range ≤ T := by
  rintro _ ⟨n, rfl⟩
  exact (ψ n).2

omit [Finite G] in
theorem closureIn_le_normalClosure (A N : Subgroup G) :
    closureIn A N ≤ normalClosure (A : Set G) := by
  have h : rankTwoX (A.subgroupOf N) ≤ (normalClosure (A : Set G)).subgroupOf N :=
    normalClosure_le_normal fun a ha => subset_normalClosure ha
  exact (map_mono h).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

omit [Finite G] in
theorem closureIn_le_centralizer {A W : Subgroup G} (hAW : A ≤ centralizer (W : Set G)) :
    closureIn A (normalizer (W : Set G)) ≤ centralizer (W : Set G) := by
  have hn : ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      have := (mem_normalizer_iff.mp (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer W g.2) n).mp hn
      simpa using this⟩
  have h : rankTwoX (A.subgroupOf (normalizer (W : Set G))) ≤
      (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G)) :=
    normalClosure_le_normal fun a ha => hAW ha
  exact (map_mono h).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)

omit [Finite G] in
theorem center_eq_bot_of_autModel {X₀ W : Type*} [Group X₀] [Group W] {X : Subgroup W}
    (hW : RankTwoSporadic.AutModel X₀ W X) : center X₀ = ⊥ := by
  obtain ⟨e⟩ := hW.nonempty_mulEquiv
  have hX : center ↥X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : W) ∈ centralizer (X : Set W) := mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
    rw [hW.centralizer_eq_bot, mem_bot] at this
    exact (mem_bot).mpr (Subtype.ext this)
  rw [← map_center_eq e, hX, Subgroup.map_bot]

omit [Finite G] in
theorem commutator_eq_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : commutator X = ⊤) : commutator Y = ⊤ := by
  have : Group.IsPerfect X := (Group.isPerfect_def).2 h
  exact (Group.isPerfect_def).1 (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

end CFSG.ComponentClassification.AS81

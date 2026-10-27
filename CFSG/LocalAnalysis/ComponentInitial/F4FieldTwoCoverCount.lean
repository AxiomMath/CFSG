module

public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCoverRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigherRoots

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open Subgroup
open scoped commutatorElement

theorem card_closure_le_of_posRoots_list {τ : Tag} {G : Type*} [Group G] [Finite G]
    (y : (Fin τ.rank → ℤ) → G) (hy2 : ∀ α, IsRoot τ α → 0 < height α → y α * y α = 1)
    (L : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → List (Fin τ.rank → ℤ))
    (hL : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → α ≠ β →
      ∀ γ ∈ L α β, IsRoot τ γ ∧ height α < height γ ∧ height β < height γ)
    (hrel : ∀ α β, IsRoot τ α → 0 < height α → IsRoot τ β → 0 < height β → α ≠ β →
      ⁅y α, y β⁆ = ((L α β).map y).prod) :
    Nat.card (closure {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ y α = g}) ≤
      2 ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  classical
  have key : ∀ T : Finset (Fin τ.rank → ℤ), (∀ α ∈ T, IsRoot τ α ∧ 0 < height α) →
      (∀ α ∈ T, ∀ β ∈ T, α ≠ β → ∀ γ ∈ L α β, γ ∈ T) →
      Nat.card (closure (y '' (T : Set (Fin τ.rank → ℤ)))) ≤ 2 ^ T.card := by
    intro T
    induction T using Finset.induction_on_min_value height with
    | empty =>
      intro _ _
      simp
    | insert a s has hmin ih =>
      intro hpos hcl
      have ha := hpos a (Finset.mem_insert_self _ _)
      have hpos_s : ∀ α ∈ s, IsRoot τ α ∧ 0 < height α := fun α hα =>
        hpos α (Finset.mem_insert_of_mem hα)
      have hcl_s : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → ∀ γ ∈ L α β, γ ∈ s := by
        intro α hα β hβ hne γ hγ
        rcases Finset.mem_insert.mp (hcl α (Finset.mem_insert_of_mem hα) β
          (Finset.mem_insert_of_mem hβ) hne γ hγ) with h' | h'
        · exfalso
          have h1 := hmin α hα
          have h2 := (hL α β (hpos_s α hα).1 (hpos_s α hα).2 (hpos_s β hβ).1 (hpos_s β hβ).2 hne
            γ hγ).2.1
          rw [h'] at h2
          omega
        · exact h'
      have ih' := ih hpos_s hcl_s
      rw [Finset.coe_insert, Set.image_insert_eq, Finset.card_insert_of_notMem has, pow_succ']
      refine (LinearCover.card_closure_insert_le (hy2 a ha.1 ha.2) ?_).trans
        (Nat.mul_le_mul_left 2 ih')
      rintro _ ⟨β, hβ, rfl⟩
      have hβ' := hpos_s β hβ
      have hne : a ≠ β := fun h => has (h ▸ hβ)
      rw [show y a * y β * (y a)⁻¹ = ⁅y a, y β⁆ * y β by simp only [commutatorElement_def]; group,
        hrel a β ha.1 ha.2 hβ'.1 hβ'.2 hne]
      refine mul_mem (list_prod_mem fun g hg => ?_) (subset_closure ⟨β, hβ, rfl⟩)
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hg
      rcases Finset.mem_insert.mp (hcl a (Finset.mem_insert_self _ _) β
        (Finset.mem_insert_of_mem hβ) hne γ hγ) with h' | h'
      · exfalso
        have h2 := (hL a β ha.1 ha.2 hβ'.1 hβ'.2 hne γ hγ).2.1
        rw [h'] at h2
        omega
      · exact subset_closure ⟨γ, h', rfl⟩
  have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.Finite :=
    (finite_setOf_isRoot τ).subset fun _ h => h.1
  set T := hfin.toFinset with hTdef
  have hT := key T (fun α hα => (Set.Finite.mem_toFinset hfin).1 hα) (fun α hα β hβ hne γ hγ => by
    have hα' := (Set.Finite.mem_toFinset hfin).1 hα
    have hβ' := (Set.Finite.mem_toFinset hfin).1 hβ
    obtain ⟨hγr, hγh, -⟩ := hL α β hα'.1 hα'.2 hβ'.1 hβ'.2 hne γ hγ
    exact (Set.Finite.mem_toFinset hfin).2 ⟨hγr, by linarith [hα'.2]⟩)
  have hset : y '' (T : Set (Fin τ.rank → ℤ)) =
      {g | ∃ α, IsRoot τ α ∧ 0 < height α ∧ y α = g} := by
    ext g
    simp only [hTdef, Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq, and_assoc]
  rw [hset, ← Set.ncard_coe_finset, hTdef, Set.Finite.coe_toFinset] at hT
  exact hT

variable {K : Type} [Field K]

theorem posUnipotent_le_closure_xr [Finite K] (hK : Nat.card K = 2) :
    (posUnipotent .F4 K).subgroupOf (adjointGroup .F4 K) ≤
      closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ xr (K := K) α = g} := by
  have : Fintype K := Fintype.ofFinite K
  have hc : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases h0 : c = 0
    · exact Or.inl h0
    · right
      have h := FiniteField.pow_card_sub_one_eq_one c h0
      rwa [← Nat.card_eq_fintype_card, hK, show 2 - 1 = 1 from rfl, pow_one] at h
  set L := closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ xr (K := K) α = g}
  have hU : posUnipotent .F4 K ≤ L.map (adjointGroup .F4 K).subtype := by
    rw [posUnipotent, rootSpan_eq_closure, closure_le]
    rintro _ ⟨α, ⟨hα, hαp⟩, c, rfl⟩
    rcases hc c with rfl | rfl
    · rw [pinnedX_zero]
      exact one_mem _
    · exact ⟨xr α, subset_closure ⟨α, hα, hαp, rfl⟩, rfl⟩
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hU (mem_subgroupOf.1 hu)
  have : v = u := Subtype.ext hvu
  rwa [← this]

end CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover

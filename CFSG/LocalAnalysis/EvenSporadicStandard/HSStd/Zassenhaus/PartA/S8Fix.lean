module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

section Fix

variable {Γ : Type*} [Group Γ]

theorem centralizes_of_fixed {K K' : Subgroup Γ} (hKp : commutator ↥K = ⊤)
    (hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) (g : Γ)
    (hgK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hgK' : ∀ y ∈ K', g * y * g⁻¹ ∈ K')
    (hfix : ∀ k ∈ K, ∃ y ∈ K', g * (k * y) * g⁻¹ = k * y) : ∀ k ∈ K, g * k * g⁻¹ = k := by
  have hδ : ∀ k ∈ K, k⁻¹ * (g * k * g⁻¹) ∈ K ∧ (∀ x ∈ K, x * (k⁻¹ * (g * k * g⁻¹)) =
      (k⁻¹ * (g * k * g⁻¹)) * x) := by
    intro k hk
    obtain ⟨y, hy, hgy⟩ := hfix k hk
    have e1 : k⁻¹ * (g * k * g⁻¹) = y * (g * y * g⁻¹)⁻¹ := by
      have : g * (k * y) * g⁻¹ = (g * k * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this] at hgy
      calc k⁻¹ * (g * k * g⁻¹) = k⁻¹ * ((g * k * g⁻¹) * (g * y * g⁻¹)) * (g * y * g⁻¹)⁻¹ := by group
        _ = y * (g * y * g⁻¹)⁻¹ := by rw [hgy]; group
    have hK' : y * (g * y * g⁻¹)⁻¹ ∈ K' := K'.mul_mem hy (K'.inv_mem (hgK' y hy))
    refine ⟨K.mul_mem (K.inv_mem hk) (hgK k hk), fun x hx => ?_⟩
    rw [e1]
    exact hcomm x hx _ hK'
  let δ : ↥K →* ↥(center ↥K) :=
    { toFun := fun k => ⟨⟨k⁻¹ * (g * k * g⁻¹), (hδ k k.2).1⟩, by
        rw [Subgroup.mem_center_iff]
        intro x
        exact Subtype.ext ((hδ k k.2).2 x x.2)⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := by
        intro k k'
        apply Subtype.ext; apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        have hc' := (hδ k k.2).2 (k' : Γ)⁻¹ (K.inv_mem k'.2)
        calc (k' : Γ)⁻¹ * (k : Γ)⁻¹ * (g * ((k : Γ) * k') * g⁻¹)
            = (k' : Γ)⁻¹ * ((k : Γ)⁻¹ * (g * k * g⁻¹)) * (g * k' * g⁻¹) := by group
          _ = ((k : Γ)⁻¹ * (g * k * g⁻¹)) * (k' : Γ)⁻¹ * (g * k' * g⁻¹) := by
            rw [hc']
          _ = _ := by group }
  have hker : commutator ↥K ≤ δ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subtype.ext (by
      have := Subgroup.mem_center_iff.1 (δ a).2 (δ b).1
      exact (congrArg Subtype.val this).symm))
  intro k hk
  have h1 : δ ⟨k, hk⟩ = 1 := by
    have : (⟨k, hk⟩ : ↥K) ∈ δ.ker := hker (hKp ▸ mem_top _)
    exact this
  have h2 : k⁻¹ * (g * k * g⁻¹) = 1 := congrArg (fun x : ↥(center ↥K) => ((x : ↥K) : Γ)) h1
  exact (inv_mul_eq_one.1 h2).symm

theorem list_length_le_card {G : Type*} [Group G] (F : Subgroup G) [Finite F] (l : List G)
    (hl : l.Nodup) (hF : ∀ x ∈ l, x ∈ F) : l.length ≤ Nat.card F := by
  let f : Fin l.length → F := fun i => ⟨l.get i, hF _ (List.get_mem l i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact (List.nodup_iff_injective_get.1 hl) (congrArg Subtype.val hij)
  simpa using Nat.card_le_card_of_injective f hf

theorem four_elements {G : Type*} [Group G] (F : Subgroup G) [Finite F] (hF4 : Nat.card F ≤ 4)
    {ub g : G} (hub : ub ∈ F) (hg : g ∈ F) (hub1 : ub ≠ 1) (hubsq : ub * ub = 1) (hg1 : g ≠ 1)
    (hgub : g ≠ ub) {x : G} (hx : x ∈ F) : x = 1 ∨ x = ub ∨ x = g ∨ x = g * ub := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hubi : ub⁻¹ = ub := inv_eq_of_mul_eq_one_right hubsq
  have hl : [1, ub, g, g * ub, x].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨⟨hub1.symm, hg1.symm, ?_, h1.symm⟩, ⟨hgub.symm, ?_, h2.symm⟩, ⟨?_, h3.symm⟩,
      h4.symm, by simp⟩
    · intro e
      apply hgub
      have : g = ub⁻¹ := eq_inv_of_mul_eq_one_left (e.symm)
      rw [this, hubi]
    · intro e
      apply hg1
      have : g = 1 := by
        have := congrArg (fun y => y * ub⁻¹) e
        simpa using this.symm
      exact this
    · intro e
      apply hub1
      have h' : (1 : G) = ub := by
        have := congrArg (fun y => g⁻¹ * y) e
        simpa using this
      exact h'.symm
  have := list_length_le_card F [1, ub, g, g * ub, x] hl (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact F.one_mem
    · exact hub
    · exact hg
    · exact F.mul_mem hg hub
    · exact hx)
  simp at this
  omega

end Fix

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

module

public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.LocalCores

open Subgroup

variable {G : Type*} [Group G]

theorem fitting_normal_intersection [Finite G] (N : Subgroup G) [hN : N.Normal] :
    (fittingSubgroup N).map N.subtype = N ⊓ fittingSubgroup G := by
  apply le_antisymm
  · refine le_inf (map_subtype_le _) ?_
    have : (fittingSubgroup N).Characteristic := (fitting_characteristic (G := N)).1
    have hnil : Group.IsNilpotent ((fittingSubgroup N).map N.subtype) :=
      have := (fitting_nilpotent (G := N)).1
      Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ N.subtype_injective)
    exact (fitting_characteristic (G := G)).2.2 _ inferInstance hnil
  · intro x hx
    obtain ⟨hxN, hxF⟩ := mem_inf.1 hx
    have hF : Group.IsNilpotent (fittingSubgroup G) := (fitting_nilpotent (G := G)).1
    have h1 : Group.IsNilpotent ↥(fittingSubgroup G ⊓ N) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        fittingSubgroup G ⊓ N ≤ fittingSubgroup G))
    have h2 : Group.IsNilpotent ((fittingSubgroup G ⊓ N).subgroupOf N) :=
      have := h1
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        fittingSubgroup G ⊓ N ≤ N)).symm
    have h3 : ((fittingSubgroup G ⊓ N).subgroupOf N).Normal :=
      have : (fittingSubgroup G ⊓ N).Normal := Subgroup.normal_inf_normal _ _
      Subgroup.normal_subgroupOf
    have hle := (fitting_characteristic (G := N)).2.2 _ h3 h2
    exact ⟨⟨x, hxN⟩, hle (mem_subgroupOf.2 ⟨hxF, hxN⟩), rfl⟩

theorem le_generalizedFitting_of_minimal [Finite G] {N : Subgroup G} (hN : N.Normal)
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    N ≤ generalizedFitting G := by
  obtain ⟨r, S, hr, hSN, hSsimple, hconj, hSnormal, e, -⟩ :=
    minimal_normal_simple_factors hN hN1 hmin
  set i₀ : Fin r := ⟨0, hr⟩
  by_cases hab : ∀ a ∈ S i₀, ∀ b ∈ S i₀, a * b = b * a
  ·
    have hS : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a * b = b * a := by
      intro i a ha b hb
      obtain ⟨g, hg⟩ := hconj i₀ i
      rw [hg, conjugate] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [show g⁻¹ * a' * g * (g⁻¹ * b' * g) = g⁻¹ * (a' * b') * g by group, hab a' ha' b' hb',
        show g⁻¹ * (b' * a') * g = g⁻¹ * b' * g * (g⁻¹ * a' * g) by group]
    have hcomm : IsMulCommutative N := ⟨⟨fun x y => by
      apply e.symm.injective
      rw [map_mul, map_mul]
      funext i
      exact Subtype.ext (hS i _ (e.symm x i).2 _ (e.symm y i).2)⟩⟩
    have hnil : Group.IsNilpotent N := inferInstance
    exact le_trans ((fitting_characteristic (G := G)).2.2 N hN hnil) le_sup_left
  ·
    push Not at hab
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    have hS0 : IsQuasisimple (S i₀) := by
      have : IsSimpleGroup (S i₀) := hSsimple i₀
      refine (isQuasisimple_of_isSimpleGroup ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab ?_⟩).1
      exact congrArg Subtype.val h
    have hcomp : IsComponent (S i₀) :=
      ⟨hS0, IsSubnormal.step _ N (hSN i₀) hN.isSubnormal (hSnormal i₀)⟩
    have : (layer G).Characteristic := layer_characteristic
    have hLN : layer G ⊓ N = N := by
      rcases hmin (layer G ⊓ N) (Subgroup.normal_inf_normal _ _) inf_le_right with h | h
      · exfalso
        have hsub : S i₀ ≤ layer G ⊓ N := le_inf (component_le_layer hcomp) (hSN i₀)
        rw [h, le_bot_iff] at hsub
        have : IsSimpleGroup (S i₀) := hSsimple i₀
        have hnt : Nontrivial (S i₀) := IsSimpleGroup.toNontrivial
        exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hsub
      · exact h
    rw [← hLN]
    exact le_trans inf_le_left le_sup_right

theorem generalized_fitting_minimal_normal [Finite G] :
    (∀ N : Subgroup G, N.Normal → N ≠ ⊥ →
      (∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) → N ≤ generalizedFitting G) ∧
    (Nontrivial G → generalizedFitting G ≠ ⊥) := by
  refine ⟨fun N hN hN1 hmin => le_generalizedFitting_of_minimal hN hN1 hmin, fun hG => ?_⟩
  obtain ⟨N, ⟨hNn, hNne⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, top_ne_bot⟩
  have hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hNmin ⟨hM, hM1⟩ hle)
  intro h
  exact hNne (le_bot_iff.1 (h ▸ le_generalizedFitting_of_minimal hNn hNne hmin))

end CFSG.LocalCores

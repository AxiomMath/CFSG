module

public import CFSG.ClassicalInvolution.AschTight.Hall196Syl

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem IsWreathed.conjSub {P : Subgroup G} (h : IsWreathed P) (g : G) :
    IsWreathed (conjSub g P) := by
  obtain ⟨a, c, b, ha4, hca, hac, hcard, hb2, hbac, hbca, hcl⟩ := h
  have hord : ∀ x : G, orderOf (g * x * g⁻¹) = orderOf x := fun x => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hconj : ∀ x y : G, (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := fun x y => by
    group
  have hinv : ∀ x : G, (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ := fun x => by group
  refine ⟨g * a * g⁻¹, g * c * g⁻¹, g * b * g⁻¹, by rw [hord]; exact ha4, by rw [hord, hord, hca],
    by rw [hconj, hconj, hac], ?_, by rw [hconj, hb2]; group, ?_, ?_, ?_⟩
  · rw [hord, ← hcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  · rw [hinv, hconj, hconj, hbac]
  · rw [hinv, hconj, hconj, hbca]
  · rw [← hcl]
    change _ = Subgroup.map (MulAut.conj g).toMonoidHom _
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply]

variable [Finite G]

theorem exists_conjSub_eq_of_isSylow2In {H V₁ V₂ : Subgroup G} (h₁ : IsSylow2In V₁ H)
    (h₂ : IsSylow2In V₂ H) : ∃ x ∈ H, conjSub x V₁ = V₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H (sylowOfIsSylow2In h₁) (sylowOfIsSylow2In h₂)
  refine ⟨(g : G), g.2, ?_⟩
  have hle : conjSub (g : G) V₁ ≤ V₂ := by
    rintro _ ⟨w, hw, rfl⟩
    have hwP : (⟨w, h₁.1 hw⟩ : H) ∈ ((sylowOfIsSylow2In h₁ : Sylow 2 ↥H) : Subgroup ↥H) :=
      Subgroup.mem_subgroupOf.mpr hw
    have hmem : MulAut.conj g (⟨w, h₁.1 hw⟩ : H) ∈
        ((g • sylowOfIsSylow2In h₁ : Sylow 2 ↥H) : Subgroup ↥H) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hwP
    rw [hg] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hcard : Nat.card V₂ ≤ Nat.card ↥(conjSub (g : G) V₁) := by
    rw [show Nat.card ↥(conjSub (g : G) V₁) = Nat.card V₁ from
      Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
      IsSylow2In.natCard_eq h₁ h₂]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem IsWreathed.of_isSylow2In {H P₀ P : Subgroup G} (h₀ : IsSylow2In P₀ H)
    (hw : IsWreathed P₀) (hP : IsSylow2In P H) : IsWreathed P := by
  obtain ⟨x, -, hx⟩ := exists_conjSub_eq_of_isSylow2In h₀ hP
  rw [← hx]
  exact IsWreathed.conjSub hw x

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.E6GraphLeviTheta

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRootPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem isPGroup_sup_of_commutator {A B C : Subgroup G} (hA : ∀ a ∈ A, a * a = 1)
    (hB : ∀ b ∈ B, b * b = 1) (hC : ∀ c ∈ C, c * c = 1)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ C) : IsPGroup 2 ↥(A ⊔ B) := by
  have hswap : ∀ a ∈ A, ∀ b ∈ B, ∃ d ∈ C, b * a = a * b * d := by
    intro a ha b hb
    refine ⟨(a * b * a⁻¹ * b⁻¹)⁻¹, inv_mem (hAB a ha b hb), ?_⟩
    have h1 := hAC a ha _ (inv_mem (hAB a ha b hb))
    have h2 := hBC b hb _ (inv_mem (hAB a ha b hb))
    calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      _ = a * b * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
          rw [← mul_assoc, ← h1, mul_assoc, ← h2, ← mul_assoc]
  let T : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, g = a * b * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, c, hc, rfl⟩ ⟨a', ha', b', hb', c', hc', rfl⟩
        obtain ⟨d, hd, hba⟩ := hswap a' ha' b hb
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', d * c * c',
          mul_mem (mul_mem hd hc) hc', ?_⟩
        calc a * b * c * (a' * b' * c') = a * b * (c * a') * b' * c' := by group
          _ = a * b * (a' * c) * b' * c' := by rw [← hAC a' ha' c hc]
          _ = a * (b * a') * (c * b') * c' := by group
          _ = a * (a' * b * d) * (b' * c) * c' := by rw [hba, ← hBC b' hb' c hc]
          _ = a * a' * b * (d * b') * c * c' := by group
          _ = a * a' * b * (b' * d) * c * c' := by rw [← hBC b' hb' d hd]
          _ = a * a' * (b * b') * (d * c * c') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by group⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
        obtain ⟨d, hd, hba⟩ := hswap a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, c⁻¹ * d, mul_mem (inv_mem hc) hd, ?_⟩
        calc (a * b * c)⁻¹ = c⁻¹ * (b⁻¹ * a⁻¹) := by group
          _ = c⁻¹ * (a⁻¹ * b⁻¹ * d) := by rw [hba]
          _ = c⁻¹ * a⁻¹ * b⁻¹ * d := by group
          _ = a⁻¹ * c⁻¹ * b⁻¹ * d := by rw [← hAC _ (inv_mem ha) _ (inv_mem hc)]
          _ = a⁻¹ * (c⁻¹ * b⁻¹) * d := by group
          _ = a⁻¹ * (b⁻¹ * c⁻¹) * d := by rw [← hBC _ (inv_mem hb) _ (inv_mem hc)]
          _ = a⁻¹ * b⁻¹ * (c⁻¹ * d) := by group }
  have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, 1, one_mem _, by group⟩)
    fun b hb => ⟨1, one_mem _, b, hb, 1, one_mem _, by group⟩
  have h4 : ∀ g ∈ T, g ^ 2 ^ 2 = 1 := by
    rintro _ ⟨a, ha, b, hb, c, hc, rfl⟩
    obtain ⟨d, hd, hba⟩ := hswap a ha b hb
    have hsq : (a * b * c) ^ 2 = d := by
      calc (a * b * c) ^ 2 = a * b * (c * a) * b * c := by rw [sq]; group
        _ = a * b * (a * c) * b * c := by rw [← hAC a ha c hc]
        _ = a * (b * a) * (c * b) * c := by group
        _ = a * (a * b * d) * (b * c) * c := by rw [hba, ← hBC b hb c hc]
        _ = a * a * b * (d * b) * (c * c) := by group
        _ = a * a * b * (b * d) * (c * c) := by rw [← hBC b hb d hd]
        _ = a * a * (b * b) * d * (c * c) := by group
        _ = d := by rw [hA a ha, hB b hb, hC c hc]; group
    rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, hsq, sq, hC d hd]
  intro g
  exact ⟨2, Subtype.ext (by simpa using h4 g (hle g.2))⟩

end Abstract

section Roots

variable {E : Type} [Field E]

theorem theta_add_facts : ∀ β ∈ rootFinset TwistTag.E6.tag, β ≠ e6HighestRoot →
    β ≠ -e6HighestRoot → e6HighestRoot + β ∈ rootFinset TwistTag.E6.tag →
      e6HighestRoot + (e6HighestRoot + β) ∉ rootFinset TwistTag.E6.tag ∧
      β + (e6HighestRoot + β) ∉ rootFinset TwistTag.E6.tag ∧
      e6HighestRoot ≠ e6HighestRoot + β ∧ e6HighestRoot ≠ -(e6HighestRoot + β) ∧
      β ≠ e6HighestRoot + β ∧ β ≠ -(e6HighestRoot + β) := by
  decide +kernel

theorem rootSubgroup_mul_self
    (h2 : (2 : E) = 0) {α : Fin TwistTag.E6.tag.rank → ℤ}
    {x : ModGL TwistTag.E6.tag E} (hx : x ∈ rootSubgroup TwistTag.E6.tag E α) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  rw [← pinnedX_add, ← two_mul, h2, zero_mul, pinnedX_zero]

theorem rootSubgroup_commute
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ¬IsRoot TwistTag.E6.tag (α + β)) {x y : ModGL TwistTag.E6.tag E}
    (hx : x ∈ rootSubgroup TwistTag.E6.tag E α) (hy : y ∈ rootSubgroup TwistTag.E6.tag E β) :
    x * y = y * x := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  exact (commute_pinnedX_of_not_isRoot hα hβ hne hne' h c d).eq

theorem isPGroup_rootSubgroup_sup
    (h2 : (2 : E) = 0) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) (h1 : β ≠ e6HighestRoot) (h1' : β ≠ -e6HighestRoot) :
    IsPGroup 2 ↥(rootSubgroup TwistTag.E6.tag E e6HighestRoot ⊔
      rootSubgroup TwistTag.E6.tag E β) := by
  have hθ := isRoot_e6HighestRoot
  have hne : e6HighestRoot ≠ β := fun h => h1 h.symm
  have hne' : e6HighestRoot ≠ -β := fun h => h1' (by rw [h, neg_neg])
  by_cases hs : IsRoot TwistTag.E6.tag (e6HighestRoot + β)
  · obtain ⟨hγθ, hγβ, hn1, hn2, hn3, hn4⟩ :=
      theta_add_facts β (mem_rootFinset.2 hβ) h1 h1' (mem_rootFinset.2 hs)
    refine isPGroup_sup_of_commutator (C := rootSubgroup TwistTag.E6.tag E (e6HighestRoot + β))
      (fun a ha => rootSubgroup_mul_self h2 ha) (fun b hb => rootSubgroup_mul_self h2 hb)
      (fun c hc => rootSubgroup_mul_self h2 hc)
      (fun a ha c hc => rootSubgroup_commute hθ hs hn1 hn2 (fun h => hγθ (mem_rootFinset.2 h))
        ha hc)
      (fun b hb c hc => rootSubgroup_commute hβ hs hn3 hn4 (fun h => hγβ (mem_rootFinset.2 h))
        hb hc) fun a ha b hb => ?_
    obtain ⟨s, rfl⟩ := mem_rootSubgroup.1 ha
    obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hb
    rw [← commutatorElement_def, commutator_pinnedX_of_two h2 hθ hβ hne hne' hs]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · refine isPGroup_sup_of_commutator (C := ⊥)
      (fun a ha => rootSubgroup_mul_self h2 ha) (fun b hb => rootSubgroup_mul_self h2 hb)
      (fun c hc => by rw [Subgroup.mem_bot.1 hc, one_mul])
      (fun a _ c hc => by rw [Subgroup.mem_bot.1 hc, one_mul, mul_one])
      (fun b _ c hc => by rw [Subgroup.mem_bot.1 hc, one_mul, mul_one]) fun a ha b hb => ?_
    rw [rootSubgroup_commute hθ hβ hne hne' hs ha hb, Subgroup.mem_bot]
    group

end Roots

end CFSG.LieType.Chevalley.E6GraphRootPair

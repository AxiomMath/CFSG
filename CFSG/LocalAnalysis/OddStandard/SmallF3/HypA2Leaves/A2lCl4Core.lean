module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Orbit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Lev
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Move

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem cl24_core [Finite K] [FiniteDimensional K V] (hK : ∀ c : K, c = 0 ∨ c = 1 ∨ c = -1)
    (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {X : Type*} [MulAction (elementaryGroup Q) X]
    [MulAction.IsPretransitive (elementaryGroup Q) X] [Finite X] (hX : 2 ≤ Nat.card X) (m : ℕ)
    (hshell : ∀ a : K, m ≤ ({v : V | v ∈ P₁.perp ∧ v ≠ 0 ∧ Q v = a} : Set V).ncard) :
    m + 1 ≤ Nat.card X := by
  haveI : Finite V := Module.finite_of_finite K
  obtain ⟨x₀, w₀, hmove⟩ := cl24_exists_move hQ h₁₂ hX
  have hDtop : cl24_D hK P₁ x₀ ≠ ⊤ := fun h =>
    hmove ((cl24_mem_D hK P₁ x₀ w₀).1 (h ▸ Submodule.mem_top))
  obtain ⟨w₁, hw₁0, hw₁Y⟩ := cl24_exists_ne_zero_mem_perpIn hQ P₁ (cl24_D hK P₁ x₀) hDtop
  set a : K := Q (w₁ : V) with ha
  let c : X → Set P₁.perp := fun y => cl24_perpIn P₁ (cl24_D hK P₁ y)
  let S₀ : Set X := {y | ∃ g : elementaryGroup Q, Cl24Lev P₁ g ∧ y = g • x₀}
  let m₀ : ℕ := Nat.card (c x₀)
  have hm₀ : 1 ≤ m₀ := Nat.card_pos_iff.2 ⟨⟨⟨0, cl24_zero_mem_perpIn P₁ _⟩⟩, inferInstance⟩
  have hDpos : 0 < Nat.card (cl24_D hK P₁ x₀) := Nat.card_pos
  have hW : Nat.card (cl24_D hK P₁ x₀) * m₀ = Nat.card P₁.perp :=
    cl24_card_mul_card_perpIn hQ P₁ _
  have hc : ∀ x, ∀ z ∈ cl24_Rorb P₁ x, c z = c x := fun x z hz => by
    simp only [c]
    rw [cl24_D_of_mem_Rorb hK P₁ hz]
  have hm : ∀ y ∈ S₀, m₀ ≤ Nat.card (cl24_Rorb P₁ y) := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 := cl24_card_Rorb_mul_card_D hK P₁ (g • x₀)
    rw [cl24_card_D_smul hK hg] at h1
    have h2 : Nat.card (cl24_Rorb P₁ (g • x₀)) = m₀ := by
      apply Nat.eq_of_mul_eq_mul_left hDpos
      rw [mul_comm, h1, hW]
    exact h2.ge
  have h1 := cl24_card_ge_of_invariant c (cl24_Rorb P₁) hc S₀ m₀ hm
  set 𝒴 : Set (Set P₁.perp) := c '' S₀ with h𝒴
  have hY : ∀ Y ∈ 𝒴, (0 : P₁.perp) ∈ Y ∧ Y.ncard = m₀ := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨cl24_zero_mem_perpIn P₁ _, ?_⟩
    rw [← Nat.card_coe_set_eq]
    exact cl24_card_perpIn_smul hK hg x₀
  have hcov : ∀ v ∈ ({v : P₁.perp | v ≠ 0 ∧ Q (v : V) = a} : Set P₁.perp),
      ∃ Y ∈ 𝒴, v ∈ Y := by
    rintro v ⟨hv0, hva⟩
    obtain ⟨g, hg, hgw⟩ := cl24_lev_exists hQ h₁₂ h₁₃ h₂₃ w₁.2 v.2
      (fun h => hw₁0 (Subtype.ext h)) (fun h => hv0 (Subtype.ext h)) (by rw [← ha, hva])
    refine ⟨c (g • x₀), ⟨g • x₀, ⟨g, hg, rfl⟩, rfl⟩, ?_⟩
    show v ∈ cl24_perpIn P₁ (cl24_D hK P₁ (g • x₀))
    rw [cl24_mem_perpIn_smul hK hg]
    have : (cl24_levEquiv hg).symm v = w₁ := by
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext hgw.symm
    rw [this]
    exact hw₁Y
  have hz : (0 : P₁.perp) ∉ ({v : P₁.perp | v ≠ 0 ∧ Q (v : V) = a} : Set P₁.perp) :=
    fun h => h.1 rfl
  have h2 := cl24_card_cover_le 𝒴 m₀ 0 hY _ hz hcov
  have hset : ({v : V | v ∈ P₁.perp ∧ v ≠ 0 ∧ Q v = a} : Set V) =
      Subtype.val '' ({v : P₁.perp | v ≠ 0 ∧ Q (v : V) = a} : Set P₁.perp) := by
    ext v
    constructor
    · rintro ⟨hv, hv0, hva⟩
      exact ⟨⟨v, hv⟩, ⟨fun h => hv0 (congrArg Subtype.val h), hva⟩, rfl⟩
    · rintro ⟨u, ⟨hu0, hua⟩, rfl⟩
      exact ⟨u.2, fun h => hu0 (Subtype.ext h), hua⟩
  have h3 := hshell a
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective] at h3
  obtain ⟨g₁, hg₁, -⟩ := cl24_lev_exists hQ h₁₂ h₁₃ h₂₃ w₁.2 w₁.2
    (fun h => hw₁0 (Subtype.ext h)) (fun h => hw₁0 (Subtype.ext h)) rfl
  have h𝒴pos : 0 < 𝒴.ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨c (g₁ • x₀), ⟨g₁ • x₀, ⟨g₁, hg₁, rfl⟩, rfl⟩⟩
  obtain ⟨k, hk⟩ : ∃ k, m₀ = k + 1 := ⟨m₀ - 1, by omega⟩
  rw [hk] at h2 h1
  simp only [Nat.add_sub_cancel] at h2
  nlinarith

end CFSG.OddStandard.SmallF3.HypA2Leaves

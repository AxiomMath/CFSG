module

public import CFSG.GH74.Uniqueness.SU.SU2Struct

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Trans

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

namespace GOPair

variable {Y : Subgroup X}

theorem exists_mem_omega_of_ne_one [Finite X] [Finite V] (hGO : GOPair V Y)
    {W₁ W₂ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) {v : V} (hv : v ≠ 1) :
    ∃ A ∈ omega V Y, v ∈ A := by
  by_cases h0 : v ∈ fixSub V Y
  · exact ⟨_, fixSub_mem_omega Y, h0⟩
  by_cases h1 : v ∈ commSub V Y
  · obtain ⟨y, _, hvy⟩ := hGO.typeA_cover hW₁.1 hW₁.2.2 h1 hv
    exact ⟨y • W₁, smul_mem_omega hW₁.1 y, hvy⟩
  · obtain ⟨y, _, hvy⟩ := hGO.typeB_cover hW₂.1 hW₂.2.1 hW₂.2.2 h0 h1
    exact ⟨y • W₂, smul_mem_omega hW₂.1 y, hvy⟩

theorem local_trans (hGO : GOPair V Y) {W₁ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y)
    {A : Subgroup V} (hA : A ∈ omega V Y) {a b : V} (ha : a ∈ A) (hb : b ∈ A) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : ∃ x : X, x • A = A ∧ x • a = b := by
  obtain ⟨g₁, hg₁⟩ := mem_omega_iff.1 hW₁.1
  obtain ⟨g₂, hg₂⟩ := mem_omega_iff.1 hA
  have hgA : (g₂ * g₁⁻¹) • W₁ = A := by rw [mul_smul, ← hg₁, inv_smul_smul, hg₂]
  have hinv : (g₂ * g₁⁻¹)⁻¹ • A = W₁ := by rw [inv_smul_eq_iff]; exact hgA.symm
  have ha' : (g₂ * g₁⁻¹)⁻¹ • a ∈ W₁ := by
    have := Subgroup.smul_mem_pointwise_smul a (g₂ * g₁⁻¹)⁻¹ A ha
    rwa [hinv] at this
  have hb' : (g₂ * g₁⁻¹)⁻¹ • b ∈ W₁ := by
    have := Subgroup.smul_mem_pointwise_smul b (g₂ * g₁⁻¹)⁻¹ A hb
    rwa [hinv] at this
  have ha1' : (g₂ * g₁⁻¹)⁻¹ • a ≠ 1 := fun h => ha1 (by
    have : (g₂ * g₁⁻¹)⁻¹ • a = (g₂ * g₁⁻¹)⁻¹ • (1 : V) := by rw [smul_one]; exact h
    exact MulAction.injective _ this)
  have hb1' : (g₂ * g₁⁻¹)⁻¹ • b ≠ 1 := fun h => hb1 (by
    have : (g₂ * g₁⁻¹)⁻¹ • b = (g₂ * g₁⁻¹)⁻¹ • (1 : V) := by rw [smul_one]; exact h
    exact MulAction.injective _ this)
  obtain ⟨y, _, hyW, hya⟩ := hGO.typeA_trans hW₁.1 hW₁.2.2 ha' hb' ha1' hb1'
  refine ⟨(g₂ * g₁⁻¹) * y * (g₂ * g₁⁻¹)⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hinv, hyW, hgA]
  · rw [mul_smul, mul_smul, hya, smul_inv_smul]

theorem transitive_on_V [Finite X] [Finite V] (hGO : GOPair V Y) {W₁ W₂ : Subgroup V}
    (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) {v w : V} (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ x : X, x • v = w := by
  obtain ⟨A, hA, hvA⟩ := hGO.exists_mem_omega_of_ne_one hW₁ hW₂ hv
  obtain ⟨B, hB, hwB⟩ := hGO.exists_mem_omega_of_ne_one hW₁ hW₂ hw
  obtain ⟨g₁, hg₁⟩ := mem_omega_iff.1 hA
  obtain ⟨g₂, hg₂⟩ := mem_omega_iff.1 hB
  have hAB : (g₂ * g₁⁻¹) • A = B := by rw [mul_smul, ← hg₁, inv_smul_smul, hg₂]
  have hvB : (g₂ * g₁⁻¹) • v ∈ B := by
    have := Subgroup.smul_mem_pointwise_smul v (g₂ * g₁⁻¹) A hvA
    rwa [hAB] at this
  have hv1 : (g₂ * g₁⁻¹) • v ≠ 1 := fun h => hv (by
    have : (g₂ * g₁⁻¹) • v = (g₂ * g₁⁻¹) • (1 : V) := by rw [smul_one]; exact h
    exact MulAction.injective _ this)
  obtain ⟨x₂, -, hx₂⟩ := hGO.local_trans hW₁ hB hvB hwB hv1 hw
  exact ⟨x₂ * (g₂ * g₁⁻¹), by rw [mul_smul, hx₂]⟩

theorem odd_ncard_omega [Finite X] [Finite V] (hGO : GOPair V Y) {W₁ W₂ : Subgroup V}
    (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) : Odd (omega V Y).ncard := by
  rw [ncard_omega]
  exact ((hGO.odd_ncard_omegaA hW₁).add_odd (hGO.odd_ncard_omegaB hW₂)).add_one

theorem even_ncard_omega_of_commSub_mem [Finite X] [Finite V] (hGO : GOPair V Y)
    (hV₁ : commSub V Y ∈ omegaA V Y) :
    Even (omega V Y).ncard := by
  set X₀ := MulAction.stabilizer X (fixSub V Y) with hX₀
  set X₁ := MulAction.stabilizer X (commSub V Y) with hX₁
  have hle : X₀ ≤ X₁ := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff] at hx ⊢
    exact hGO.smul_commSub_eq hx
  obtain ⟨h, hh⟩ := mem_omega_iff.1 hV₁.1
  have hcard : Nat.card X₁ = Nat.card X₀ := by
    rw [hX₁, ← hh, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hX₀,
      Subgroup.card_map_of_injective (MulAut.conj h).injective]
  have hX01 : X₀ = X₁ := Subgroup.eq_of_le_of_card_ge hle hcard.le
  have hne : fixSub V Y ≠ commSub V Y := fun h0 => hV₁.2.1 h0.symm
  have hhinv : h⁻¹ • commSub V Y = fixSub V Y := by rw [inv_smul_eq_iff]; exact hh.symm
  have hhN : h ∈ Subgroup.normalizer (X₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx0 : x • fixSub V Y = fixSub V Y := MulAction.mem_stabilizer_iff.1 hx
      rw [hX01, hX₁, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hhinv, hx0, hh]
    · intro hx
      rw [hX01, hX₁, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hhinv] at hx
      rw [MulAction.mem_stabilizer_iff]
      have : h • (x • fixSub V Y) = h • fixSub V Y := by rw [hx, hh]
      exact MulAction.injective h this
  set N := Subgroup.normalizer (X₀ : Set X) with hNdef
  have hX₀N : X₀ ≤ N := Subgroup.le_normalizer
  have hstab : MulAction.stabilizer ↥N (fixSub V Y) = X₀.subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hX₀, MulAction.mem_stabilizer_iff]
    rfl
  have horb : MulAction.orbit ↥N (fixSub V Y) = {fixSub V Y, commSub V Y} := by
    ext B
    simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩
      have hBΩ : (n : X) • fixSub V Y ∈ omega V Y := smul_mem_omega (fixSub_mem_omega Y) (n : X)
      rw [omega_eq] at hBΩ
      rcases hBΩ with hB | hB | hB
      · exact Or.inl hB
      · obtain ⟨y, hy, hyB⟩ := hGO.typeA_conj hV₁.1 hV₁.2.2 hB.1 hB.2.2
        right
        show (n : X) • fixSub V Y = commSub V Y
        rw [hyB]
        exact hGO.smul_commSub_eq (smul_fixSub_of_mem hy)
      · exfalso
        have hfix : ∀ y ∈ Y, y • ((n : X) • fixSub V Y) = (n : X) • fixSub V Y := by
          intro y hy
          have hyX₀ : y ∈ X₀ := MulAction.mem_stabilizer_iff.2 (smul_fixSub_of_mem hy)
          have hn' := ((Subgroup.mem_normalizer_iff.1 (N.inv_mem n.2)) y).1 hyX₀
          rw [inv_inv] at hn'
          have h2 := MulAction.mem_stabilizer_iff.1 hn'
          calc y • ((n : X) • fixSub V Y)
              = (n : X) • (((n : X)⁻¹ * y * (n : X)) • fixSub V Y) := by
                rw [← mul_smul, ← mul_smul, mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
            _ = (n : X) • fixSub V Y := by rw [h2]
        obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
          by_contra hcon
          exact hGO.ne_bot ((Subgroup.eq_bot_iff_forall _).2 fun y hy =>
            by_contra fun h' => hcon ⟨y, hy, h'⟩)
        exact hy1 (hGO.typeB_stab_trivial hB.1 hB.2.1 hB.2.2 hy (hfix y hy))
    · rintro (rfl | rfl)
      · exact ⟨1, one_smul _ _⟩
      · exact ⟨⟨h, hhN⟩, hh⟩
  have hrel : X₀.relIndex N = 2 := by
    have := MulAction.index_stabilizer ↥N (fixSub V Y)
    rw [hstab, horb, Set.ncard_pair hne] at this
    exact this
  have hΩcard : (omega V Y).ncard = X₀.index := (MulAction.index_stabilizer X (fixSub V Y)).symm
  rw [hΩcard, ← Subgroup.relIndex_mul_index hX₀N, hrel]
  exact even_two_mul _

theorem card_fixSub_lt_card_commSub [Finite X] [Finite V] (hGO : GOPair V Y) {W₁ W₂ : Subgroup V}
    (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) :
    Nat.card (fixSub V Y) < Nat.card (commSub V Y) := by
  have hle : Nat.card (fixSub V Y) ≤ Nat.card (commSub V Y) := by
    rw [← card_eq_of_mem_omega hW₁.1]
    exact Subgroup.card_le_of_le hW₁.2.2
  refine lt_of_le_of_ne hle fun heq => ?_
  have hW₁V : W₁ = commSub V Y :=
    Subgroup.eq_of_le_of_card_ge hW₁.2.2 (by rw [card_eq_of_mem_omega hW₁.1, heq])
  have hev := hGO.even_ncard_omega_of_commSub_mem (hW₁V ▸ hW₁)
  exact (Nat.not_even_iff_odd.2 (hGO.odd_ncard_omega hW₁ hW₂)) hev

theorem sq_le [Finite X] [Finite V] (hGO : GOPair V Y) {W₁ W₂ : Subgroup V}
    (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) :
    Nat.card (fixSub V Y) ^ 2 ≤ Nat.card (commSub V Y) := by
  have hlt := hGO.card_fixSub_lt_card_commSub hW₁ hW₂
  have hex : ∃ y ∈ Y, y • W₁ ≠ W₁ := by
    by_contra hcon
    have hall : ∀ y ∈ Y, y • W₁ = W₁ := fun y hy => by_contra fun h' => hcon ⟨y, hy, h'⟩
    have hV₁ : commSub V Y ≤ W₁ := by
      intro v hv
      by_cases hv1 : v = 1
      · rw [hv1]; exact one_mem _
      · obtain ⟨y, hy, hvy⟩ := hGO.typeA_cover hW₁.1 hW₁.2.2 hv hv1
        rwa [hall y hy] at hvy
    have heq : W₁ = commSub V Y := le_antisymm hW₁.2.2 hV₁
    have := card_eq_of_mem_omega hW₁.1
    rw [heq] at this
    omega
  obtain ⟨y, hy, hne⟩ := hex
  have hW₁' : y • W₁ ∈ omegaA V Y := hGO.smul_mem_omegaA (smul_fixSub_of_mem hy) hW₁
  have hinf : W₁ ⊓ y • W₁ = ⊥ :=
    hGO.inf_eq_bot_of_ne hW₁.1 hW₁'.1 hne.symm
  let f : W₁ × (y • W₁ : Subgroup V) → commSub V Y := fun p =>
    ⟨(p.1 : V) * (p.2 : V), (commSub V Y).mul_mem (hW₁.2.2 p.1.2) (hW₁'.2.2 p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have h1 : a * b = a' * b' := congrArg Subtype.val hab
    have h2 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : a'⁻¹ * a ∈ W₁ ⊓ y • W₁ :=
      ⟨W₁.mul_mem (W₁.inv_mem ha') ha, h2 ▸ (y • W₁).mul_mem hb' ((y • W₁).inv_mem hb)⟩
    rw [hinf] at h3
    have h4 : a'⁻¹ * a = 1 := h3
    have h5 : a = a' := (inv_mul_eq_one.1 h4).symm
    have h6 : b' * b⁻¹ = 1 := h2 ▸ h4
    have h7 : b = b' := (mul_inv_eq_one.1 h6).symm
    subst h5; subst h7
    rfl
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, card_eq_of_mem_omega hW₁.1, card_eq_of_mem_omega hW₁'.1] at this
  rw [sq]
  exact this

end GOPair

end Trans

end CFSG.GH74.Uniqueness.SU.SU2

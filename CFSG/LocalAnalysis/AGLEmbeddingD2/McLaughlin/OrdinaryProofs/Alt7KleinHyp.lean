module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7Klein
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7KleinHypK

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

set_option maxRecDepth 100000 in
theorem perm7_five_cycle_witness :
    ((Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) * (Equiv.swap 1 2 * Equiv.swap 3 4)) ^ 5 = 1 ∧
      (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) * (Equiv.swap 1 2 * Equiv.swap 3 4) ≠ 1 := by
  decide +kernel

theorem alt7_exists_order_five_product : ∃ a b : alternatingGroup (Fin 7),
    a ≠ 1 ∧ a ^ 2 = 1 ∧ b ≠ 1 ∧ b ^ 2 = 1 ∧ orderOf (a * b) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨h5, h1⟩ := perm7_five_cycle_witness
  have hA : ∀ σ : Equiv.Perm (Fin 7), σ = Equiv.swap 0 1 * Equiv.swap 2 3 ∨
      σ = Equiv.swap 1 2 * Equiv.swap 3 4 → σ ∈ alternatingGroup (Fin 7) := by
    intro σ hσ
    rcases hσ with rfl | rfl <;> exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  let a : alternatingGroup (Fin 7) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, hA _ (Or.inl rfl)⟩
  let b : alternatingGroup (Fin 7) := ⟨Equiv.swap 1 2 * Equiv.swap 3 4, hA _ (Or.inr rfl)⟩
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply (show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) ≠ 1 by decide +kernel)
    exact congrArg Subtype.val h
  · apply Subtype.ext
    show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) ^ 2 = 1
    decide +kernel
  · intro h
    apply (show (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4) ≠ 1 by decide +kernel)
    exact congrArg Subtype.val h
  · apply Subtype.ext
    show (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 3 4) ^ 2 = 1
    decide +kernel
  · apply orderOf_eq_prime
    · apply Subtype.ext
      exact h5
    · intro h
      apply h1
      exact congrArg Subtype.val h

set_option maxRecDepth 100000 in
theorem perm7_even_involution_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 7) =>
      σ * σ = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1)).card = 105 :=
  Alt7KleinHypK.card_even_invol_K (by decide +kernel)

theorem alt7_card_involutions :
    Nat.card {t : alternatingGroup (Fin 7) // t ^ 2 = 1 ∧ t ≠ 1} = 105 := by
  classical
  let e : {t : alternatingGroup (Fin 7) // t ^ 2 = 1 ∧ t ≠ 1} ≃
      {σ : Equiv.Perm (Fin 7) // σ * σ = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1} :=
    { toFun := fun t => ⟨(t.1 : Equiv.Perm (Fin 7)), by
        obtain ⟨t, h2, h1⟩ := t
        refine ⟨?_, fun h => h1 (Subtype.ext (by rw [Subgroup.coe_one]; exact h)),
          Equiv.Perm.mem_alternatingGroup.mp t.2⟩
        rw [← Subgroup.coe_mul, ← pow_two, h2, Subgroup.coe_one]⟩
      invFun := fun σ => ⟨⟨σ.1, Equiv.Perm.mem_alternatingGroup.mpr σ.2.2.2⟩,
        by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
          exact σ.2.1,
        fun h => σ.2.2.1 (by
          have := congrArg Subtype.val h
          rw [Subgroup.coe_one] at this
          exact this)⟩
      left_inv := fun t => by
        obtain ⟨⟨t, ht⟩, h2, h1⟩ := t
        rfl
      right_inv := fun σ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, perm7_even_involution_count]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem perm7_involution_conj_a0_search :
    ∀ x ∈ (Finset.univ.filter (fun x : Equiv.Perm (Fin 7) =>
        x * x = 1 ∧ x ≠ 1 ∧ Equiv.Perm.sign x = 1)),
      ∃ g ∈ (Finset.univ.filter (fun g : Equiv.Perm (Fin 7) => Equiv.Perm.sign g = 1)),
        g * (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) * g⁻¹ = x := by
  intro x hx
  obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hx
  obtain ⟨g, hg, hgx⟩ := Alt7KleinHypK.even_invol_conj_K
    (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) (by decide +kernel)
    (by decide +kernel) x h1 h2 h3
  exact ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩, hgx⟩

theorem perm7_involution_conj_a0 (x : Equiv.Perm (Fin 7)) (h1 : x * x = 1) (h2 : x ≠ 1)
    (h3 : Equiv.Perm.sign x = 1) :
    ∃ g : Equiv.Perm (Fin 7), Equiv.Perm.sign g = 1 ∧
      g * (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) * g⁻¹ = x := by
  obtain ⟨g, hg, hgx⟩ := perm7_involution_conj_a0_search x
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩)
  exact ⟨g, (Finset.mem_filter.mp hg).2, hgx⟩

theorem alt7_involutions_conj {a b : alternatingGroup (Fin 7)} (ha1 : a ≠ 1) (ha : a ^ 2 = 1)
    (hb1 : b ≠ 1) (hb : b ^ 2 = 1) : IsConj a b := by
  have hsq : ∀ x : alternatingGroup (Fin 7), x ^ 2 = 1 →
      (x : Equiv.Perm (Fin 7)) * (x : Equiv.Perm (Fin 7)) = 1 := by
    intro x hx
    have := congrArg Subtype.val hx
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two] at this
    exact this
  have hne : ∀ x : alternatingGroup (Fin 7), x ≠ 1 → (x : Equiv.Perm (Fin 7)) ≠ 1 :=
    fun x hx h => hx (Subtype.ext (by rw [Subgroup.coe_one]; exact h))
  obtain ⟨g, hg, hga⟩ := perm7_involution_conj_a0 _ (hsq a ha) (hne a ha1)
    (Equiv.Perm.mem_alternatingGroup.mp a.2)
  obtain ⟨h, hh, hhb⟩ := perm7_involution_conj_a0 _ (hsq b hb) (hne b hb1)
    (Equiv.Perm.mem_alternatingGroup.mp b.2)
  have hc : Equiv.Perm.sign (h * g⁻¹) = 1 := by
    simp [map_mul, map_inv, hh, hg]
  refine isConj_iff.mpr ⟨⟨h * g⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hc⟩, ?_⟩
  apply Subtype.ext
  show (h * g⁻¹) * (a : Equiv.Perm (Fin 7)) * (h * g⁻¹)⁻¹ = (b : Equiv.Perm (Fin 7))
  rw [← hga, ← hhb]
  group

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

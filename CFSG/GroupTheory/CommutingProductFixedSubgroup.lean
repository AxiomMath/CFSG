module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, a * b = g}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        rw [mul_assoc a b (a' * b'), ← mul_assoc b a' b', ← hcomm a' ha' b hb]
        simp only [mul_assoc]
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev, hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact hle hg

theorem commutatorElement_mul_of_commute {A B : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  let φ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun a b => hcomm a a.2 b b.2
  have h := map_commutatorElement φ (⟨a₁, ha₁⟩, ⟨b₁, hb₁⟩) (⟨a₂, ha₂⟩, ⟨b₂, hb₂⟩)
  exact h.symm

theorem commuting_product_fixed_subgroup_derived_containment {A B : Subgroup G}
    (hAB : ⁅A, B⁆ = ⊥) {x : G} (hxA : x ∈ normalizer (A : Set G))
    (hxB : x ∈ normalizer (B : Set G)) :
    (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) ≤ (A ⊔ B) ⊓ centralizer {x} ∧
    (((A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x})).subgroupOf
      ((A ⊔ B) ⊓ centralizer {x})).Normal ∧
    ⁅(A ⊔ B) ⊓ centralizer {x}, (A ⊔ B) ⊓ centralizer {x}⁆ ≤
      (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hAB ha) b hb).symm
  have hD : (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) ≤ (A ⊔ B) ⊓ centralizer {x} :=
    sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
  have hfix : ∀ {K₁ K₂ : Subgroup G}, (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) →
      ∀ {u v z w : G}, u ∈ K₁ → v ∈ K₁ → z ∈ K₁ → z ∈ K₂ → w ∈ K₂ →
        x * u * x⁻¹ = u * z → x * v * x⁻¹ = v * w → ⁅u, v⁆ ∈ centralizer {x} := by
    intro K₁ K₂ hK u v z w hu hv hz₁ hz₂ hw hxu hxv
    rw [mem_centralizer_singleton_iff]
    have hconj : x * ⁅u, v⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * v * x⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have h1 : ⁅u * z, v * w⁆ = ⁅u, v⁆ * ⁅z, w⁆ :=
      commutatorElement_mul_of_commute hK hu hv hz₂ hw
    have h2 : ⁅z, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hK z hz₁ w hw
    rw [hxu, hxv, h1, h2, mul_one] at hconj
    exact (mul_inv_eq_iff_eq_mul.1 hconj).symm
  have hderiv : ⁅(A ⊔ B) ⊓ centralizer {x}, (A ⊔ B) ⊓ centralizer {x}⁆ ≤
      (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) := by
    rw [commutator_le]
    intro c₁ hc₁ c₂ hc₂
    have hdec : ∀ c ∈ (A ⊔ B) ⊓ centralizer {x}, ∃ a ∈ A, ∃ b ∈ B, ∃ z ∈ A ⊓ B, a * b = c ∧
        x * a * x⁻¹ = a * z ∧ x * b * x⁻¹ = z⁻¹ * b := by
      intro c hc
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hc.1
      have hxa : x * a * x⁻¹ ∈ A := (mem_normalizer_iff.1 hxA a).1 ha
      have hxb : x * b * x⁻¹ ∈ B := (mem_normalizer_iff.1 hxB b).1 hb
      have hfixc : x * (a * b) * x⁻¹ = a * b := by
        have h3 : a * b ∈ centralizer {x} := hc.2
        rw [mul_inv_eq_iff_eq_mul]
        exact (mem_centralizer_singleton_iff.1 h3).symm
      have hsplit : (x * a * x⁻¹) * (x * b * x⁻¹) = a * b := by
        rw [← hfixc]
        group
      refine ⟨a, ha, b, hb, a⁻¹ * (x * a * x⁻¹), ⟨A.mul_mem (A.inv_mem ha) hxa, ?_⟩, rfl, ?_, ?_⟩
      · have : a⁻¹ * (x * a * x⁻¹) = b * (x * b * x⁻¹)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, hsplit]
        rw [this]
        exact B.mul_mem hb (B.inv_mem hxb)
      · group
      · rw [mul_inv_rev, inv_inv, mul_assoc _ a b, ← hsplit]
        group
    obtain ⟨a₁, ha₁, b₁, hb₁, z₁, hz₁, rfl, hxa₁, hxb₁⟩ := hdec c₁ hc₁
    obtain ⟨a₂, ha₂, b₂, hb₂, z₂, hz₂, rfl, hxa₂, hxb₂⟩ := hdec c₂ hc₂
    obtain ⟨hz₁A, hz₁B⟩ := mem_inf.1 hz₁
    obtain ⟨hz₂A, hz₂B⟩ := mem_inf.1 hz₂
    rw [commutatorElement_mul_of_commute hcomm ha₁ ha₂ hb₁ hb₂]
    have hcommB : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
    have hxb₁' : x * b₁ * x⁻¹ = b₁ * z₁⁻¹ := hxb₁.trans (hcomm _ (inv_mem hz₁A) _ hb₁)
    have hxb₂' : x * b₂ * x⁻¹ = b₂ * z₂⁻¹ := hxb₂.trans (hcomm _ (inv_mem hz₂A) _ hb₂)
    refine mul_mem (mem_sup_left ⟨?_, hfix hcomm ha₁ ha₂ hz₁A hz₁B hz₂B hxa₁ hxa₂⟩)
      (mem_sup_right ⟨?_, hfix hcommB hb₁ hb₂ (inv_mem hz₁B) (inv_mem hz₁A) (inv_mem hz₂A)
        hxb₁' hxb₂'⟩)
    · rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)
    · rw [commutatorElement_def]
      exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)
  refine ⟨hD, ?_, hderiv⟩
  rw [normal_subgroupOf_iff_le_normalizer hD]
  intro c hc
  rw [mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have hcd : ⁅c, d⁆ ∈ (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) :=
      hderiv (commutator_mem_commutator hc (hD hd))
    have : c * d * c⁻¹ = ⁅c, d⁆ * d := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact mul_mem hcd hd
  · intro hd
    have hcd : ⁅c⁻¹, c * d * c⁻¹⁆ ∈ (A ⊓ centralizer {x}) ⊔ (B ⊓ centralizer {x}) :=
      hderiv (commutator_mem_commutator (inv_mem hc) (hD hd))
    have : d = ⁅c⁻¹, c * d * c⁻¹⁆ * (c * d * c⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact mul_mem hcd hd

end CFSG.GroupTheory

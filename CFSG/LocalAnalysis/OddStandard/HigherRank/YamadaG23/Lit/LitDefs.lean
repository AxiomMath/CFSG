module

public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

@[expose] def litP {X : Type*} [Group X] (Z : Subgroup X) : Subgroup X := Z ⊔ CFSG.oddCore X

@[expose] def litC {X : Type*} [Group X] (Z A : Subgroup X) [Z.Normal] : Subgroup X where
  carrier := {c | c ∈ normalizer (A : Set X) ∧ ∀ a ∈ A, ⁅a, c⁆ ∈ Z}
  mul_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨mul_mem hc hd, fun a ha => ?_⟩
    have e : ⁅a, c * d⁆ = ⁅a, c⁆ * (c * ⁅a, d⁆ * c⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hc' a ha) (Normal.conj_mem inferInstance _ (hd' a ha) c)
  one_mem' := ⟨one_mem _, fun a _ => by simp⟩
  inv_mem' := by
    rintro c ⟨hc, hc'⟩
    refine ⟨inv_mem hc, fun a ha => ?_⟩
    have e : ⁅a, c⁻¹⁆ = c⁻¹ * ⁅a, c⁆⁻¹ * c := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h2 := Normal.conj_mem inferInstance _ (inv_mem (hc' a ha)) c⁻¹
    simpa using h2

theorem mem_litC {X : Type*} [Group X] {Z A : Subgroup X} [Z.Normal] {c : X} :
    c ∈ litC Z A ↔ c ∈ normalizer (A : Set X) ∧ ∀ a ∈ A, ⁅a, c⁆ ∈ Z := Iff.rfl

structure LitCtx {X : Type*} [Group X] (Z A : Subgroup X) [Z.Normal] : Prop where
  central : ∀ z ∈ Z, ∀ x : X, z * x = x * z
  card_Z : Nat.card Z = 4
  Z_le_A : Z ≤ A
  card_A : Nat.card A = 64
  comm_mem : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Z
  sq_mem : ∀ a ∈ A, a ^ 2 ∈ Z
  sylow : ¬ 2 ∣ A.relIndex (litC Z A)
  even : Even (normalizer (A : Set X)).index

structure LitBar {G : Type*} [Group G] (A : Subgroup G)
    (φ : ↥(normalizer (A : Set G)) →* Equiv.Perm (Fin 6)) : Prop where
  card : Nat.card A = 16
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  surj : Function.Surjective φ
  ker : ∀ g : ↥(normalizer (A : Set G)), φ g = 1 ↔ ∀ a ∈ A, (g : G) * a = a * g
  two_mem : ∀ c ∈ centralizer (A : Set G), (∃ k : ℕ, c ^ 2 ^ k = 1) → c ∈ A
  even : Even (normalizer (A : Set G)).index
  oddCore : CFSG.oddCore G = ⊥

end CFSG.OddStandard.HigherRank.YamadaG23

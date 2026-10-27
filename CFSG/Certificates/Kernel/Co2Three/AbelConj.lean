module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Co2Three

theorem false_of_conj {G : Type*} [Group G] {Q A : Subgroup G} [Finite Q] (hAQ : A ≤ Q)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {m : ℕ} (hcard : Nat.card Q ≤ m * Nat.card A)
    {x : G} (hx : x ∈ A) (h : Fin m → G) (hh : ∀ i, h i ∈ Q)
    (hinj : Function.Injective fun i => h i * x * (h i)⁻¹) {y₁ y₂ : G} (hy₁ : y₁ ∈ Q)
    (hy₂ : y₂ ∈ Q) (c₁ : x * y₁ = y₁ * x) (c₂ : x * y₂ = y₂ * x) (hn : y₁ * y₂ ≠ y₂ * y₁) :
    False := by
  classical
  set C : Subgroup G := Q ⊓ Subgroup.centralizer {x} with hC
  have memC {g : G} (hg : g ∈ Q) (e : x * g = g * x) : g ∈ C :=
    ⟨hg, Subgroup.mem_centralizer_iff.2 fun k hk => by rw [Set.mem_singleton_iff.1 hk]; exact e⟩
  have hAC : A ≤ C := fun a ha => memC (hAQ ha) (hA _ hx _ ha)
  have hCQ : C ≤ Q := inf_le_left
  have : Finite C := Finite.of_injective (Subgroup.inclusion hCQ) (Subgroup.inclusion_injective _)
  have hidx : m ≤ (C.subgroupOf Q).index := by
    rw [Subgroup.index]
    have hi := Nat.card_le_card_of_injective
      (fun i : Fin m => (QuotientGroup.mk (⟨h i, hh i⟩ : Q) : Q ⧸ C.subgroupOf Q)) (by
        intro i j hij
        have hm : (h i)⁻¹ * h j ∈ C := by
          have hm' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hij)
          rwa [Subgroup.coe_mul, InvMemClass.coe_inv] at hm'
        have e := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hm).2 x (Set.mem_singleton x)
        apply hinj
        change h i * x * (h i)⁻¹ = h j * x * (h j)⁻¹
        calc h i * x * (h i)⁻¹ = h i * (x * ((h i)⁻¹ * h j)) * (h j)⁻¹ := by group
          _ = h i * ((h i)⁻¹ * h j * x) * (h j)⁻¹ := by rw [e]
          _ = h j * x * (h j)⁻¹ := by group)
    simpa using hi
  have hmul := Subgroup.card_mul_index (C.subgroupOf Q)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCQ).toEquiv] at hmul
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hcard
      omega
    · exact h0
  have hle : Nat.card C ≤ Nat.card A := by
    refine Nat.le_of_mul_le_mul_left ?_ hm0
    calc m * Nat.card C ≤ (C.subgroupOf Q).index * Nat.card C := Nat.mul_le_mul_right _ hidx
      _ = Nat.card Q := by rw [mul_comm]; exact hmul
      _ ≤ m * Nat.card A := hcard
  have hAeq := Subgroup.eq_of_le_of_card_ge hAC hle
  have h₁ : y₁ ∈ A := hAeq ▸ memC hy₁ c₁
  have h₂ : y₂ ∈ A := hAeq ▸ memC hy₂ c₂
  exact hn (hA _ h₁ _ h₂)

end CFSG.KC.Co2Three

end

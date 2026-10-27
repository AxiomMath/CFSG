module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open Subgroup

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

theorem sec8Case_table517 (h : Hyp52 X) (hc : h.Sec8Case) : h.Table517 := by
  rcases hc with ⟨hJ, hKa, hK⟩ | ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hJ, hKa, hK⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩))

end Hyp52

namespace Eight2

theorem mem_normalizer_of_conj_mem_fin {G : Type*} [Group G] [Finite G] {K : Subgroup G} {g : G}
    (h1 : ∀ x ∈ K, g * x * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨w, hw, hwx⟩ := hx
  have hwx' : g * w * g⁻¹ = g * x * g⁻¹ := hwx
  rw [← mul_left_cancel (mul_right_cancel hwx')]
  exact hw

theorem eq_one_or_of_mem_zpowers_sq {G : Type*} [Group G] {g w : G} (hg : g * g = 1)
    (hw : w ∈ zpowers g) : w = 1 ∨ w = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hg, one_zpow, one_mul, zpow_one]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem comm_of_odd_of_isPGroup_mulAut {T : Subgroup X} (hT : IsPGroup 2 (MulAut ↥T)) {g : X}
    (hg : g ∈ normalizer (T : Set X)) (ho : Odd (orderOf g)) {d : X} (hd : d ∈ T) :
    g * d * g⁻¹ = d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := T.normalizerMonoidHom ⟨g, hg⟩ with hα
  have h1 : orderOf α ∣ orderOf g := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_map_dvd _ _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hT) α
  have h2 : orderOf α = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      rw [hn] at h1
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 (Nat.succ_ne_zero n)).trans h1))
  have h3 : α = 1 := orderOf_eq_one_iff.mp h2
  have h4 := Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨g, hg⟩ ⟨d, hd⟩
  rw [← hα, h3] at h4
  exact h4.symm

end Eight2

end CFSG.ComponentClassification.GSThmB

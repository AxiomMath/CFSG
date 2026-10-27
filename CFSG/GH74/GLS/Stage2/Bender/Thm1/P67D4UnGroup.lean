module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.PGroup

public section

open scoped Pointwise

namespace CFSG.GH74.GLS.SP

private theorem isPrimePow_natCard_of_orderOf_eq {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (h : ∀ a b : H, a ≠ 1 → b ≠ 1 → orderOf a = orderOf b) : IsPrimePow (Nat.card H) := by
  have h1 : Nat.card H ≠ 1 := (Finite.one_lt_card (α := H)).ne'
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hr.one_lt.ne hx
  have hpg : IsPGroup r H := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, by simp [hg]⟩
    · refine ⟨1, ?_⟩
      rw [pow_one, ← hx, ← h g x hg hx1]
      exact pow_orderOf_eq_one g
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  refine (isPrimePow_nat_iff _).2 ⟨r, n, hr, Nat.pos_of_ne_zero ?_, hn.symm⟩
  rintro rfl
  exact h1 (by simpa using hn)

private theorem normalCore_eq_bot {G : Type*} [Group G] (B U : Subgroup G)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U) : B.normalCore = ⊥ := by
  have hKU : ∀ u ∈ U, u ∈ B.normalCore → u = 1 := fun u hu hK => hmeet u hu (hK c₀)
  refine eq_bot_iff.mpr fun k hk => ?_
  have hkB : k ∈ B := Subgroup.normalCore_le B hk
  have hcomm : ∀ u ∈ U, k * u = u * k := by
    intro u hu
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ B.normalCore := by
      have h2 : u * k⁻¹ * u⁻¹ ∈ B.normalCore :=
        (Subgroup.normalCore_normal B).conj_mem k⁻¹ (B.normalCore.inv_mem hk) u
      simpa [mul_assoc] using B.normalCore.mul_mem hk h2
    have h3 : k * u * k⁻¹ * u⁻¹ ∈ U := U.mul_mem (hUnorm k hkB u hu) (U.inv_mem hu)
    have h4 := hKU _ h3 h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
    exact h4
  exact Subgroup.mem_bot.mpr (hKU k (hKC k hkB hcomm) hk)

private theorem exists_mul_mul_of_cells {G : Type*} [Group G] (B U : Subgroup G) (c₀ : G)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u) {a₁ a₂ : G} (h₁ : a₁ ∉ B)
    (h₂ : a₂ ∉ B) : ∃ b ∈ B, ∃ u ∈ U, a₂ = b * a₁ * u := by
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := (hcell a₁).resolve_left h₁
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := (hcell a₂).resolve_left h₂
  refine ⟨b₂ * b₁⁻¹, B.mul_mem hb₂ (B.inv_mem hb₁), u₁⁻¹ * u₂,
    U.mul_mem (U.inv_mem hu₁) hu₂, ?_⟩
  simp [mul_assoc]

private theorem exists_mul_eq_of_cells {G : Type*} [Group G] (B U : Subgroup G) (hUB : U ≤ B)
    (c₀ : G) (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u) (A : Subgroup G)
    [A.Normal] {a : G} (haA : a ∈ A) (haB : a ∉ B) (g : G) : ∃ x ∈ A, ∃ y ∈ B, g = x * y := by
  by_cases hg : g ∈ B
  · exact ⟨1, A.one_mem, g, hg, (one_mul g).symm⟩
  · obtain ⟨b, hb, u, hu, hbu⟩ := exists_mul_mul_of_cells B U c₀ hcell haB hg
    refine ⟨b * a * b⁻¹, ‹A.Normal›.conj_mem a haA b, b * u, B.mul_mem hb (hUB hu), ?_⟩
    rw [hbu]
    simp [mul_assoc]

private theorem inf_eq_bot_of_normalCore {G : Type*} [Group G] (A B : Subgroup G) [A.Normal]
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAB : ∀ g : G, ∃ x ∈ A, ∃ y ∈ B, g = x * y)
    (hK : B.normalCore = ⊥) : A ⊓ B = ⊥ := by
  refine eq_bot_iff.mpr fun n hn => ?_
  have hn' : n ∈ B.normalCore := by
    intro g
    obtain ⟨x, hx, y, hy, rfl⟩ := hAB g
    have h1 : y * n * y⁻¹ ∈ A := ‹A.Normal›.conj_mem n hn.1 y
    have h2 : y * n * y⁻¹ ∈ B := B.mul_mem (B.mul_mem hy hn.2) (B.inv_mem hy)
    have h3 : x * y * n * (x * y)⁻¹ = y * n * y⁻¹ := by
      calc x * y * n * (x * y)⁻¹ = (x * (y * n * y⁻¹)) * x⁻¹ := by simp [mul_assoc]
        _ = ((y * n * y⁻¹) * x) * x⁻¹ := by rw [hA x hx _ h1]
        _ = y * n * y⁻¹ := by simp
    rw [h3]
    exact h2
  rw [hK] at hn'
  exact hn'

theorem noAbel_of_two_cells {G : Type*} [Group G] [Finite G] (B U : Subgroup G) (hUB : U ≤ B)
    (hUnorm : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (c₀ : G) (hc₀ : c₀ ∉ B)
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ u ∈ U, g = b * c₀ * u)
    (hmeet : ∀ u ∈ U, c₀ * u * c₀⁻¹ ∈ B → u = 1)
    (hΩ : ¬ IsPrimePow B.index)
    (hKC : ∀ k ∈ B, (∀ u ∈ U, k * u = u * k) → k ∈ U)
    (A : Subgroup G) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  have _ := hc₀
  have hK : B.normalCore = ⊥ := normalCore_eq_bot B U hUnorm c₀ hmeet hKC
  by_cases hAB : A ≤ B
  · exact le_bot_iff.mp (hK ▸ Subgroup.normal_le_normalCore.mpr hAB)
  · exfalso
    obtain ⟨a, haA, haB⟩ := IsConcreteLE.not_le_iff_exists.mp hAB
    have hfac := exists_mul_eq_of_cells B U hUB c₀ hcell A haA haB
    have hinf : A ⊓ B = ⊥ := inf_eq_bot_of_normalCore A B hA hfac hK
    have hmem : ∀ x ∈ A, x ∈ B → x = 1 := fun x hx hxB => by
      have : x ∈ A ⊓ B := ⟨hx, hxB⟩
      rw [hinf] at this
      exact Subgroup.mem_bot.mp this
    have hcompl : A.IsComplement' B := by
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) ?_
      refine Set.eq_univ_iff_forall.mpr fun g => ?_
      obtain ⟨x, hx, y, hy, rfl⟩ := hfac g
      exact Set.mul_mem_mul hx hy
    have hindex : B.index = Nat.card A := hcompl.index_eq_card
    have hne : ∀ x ∈ A, x ≠ 1 → x ∉ B := fun x hx hx1 hxB => hx1 (hmem x hx hxB)
    have hconj : ∀ x ∈ A, ∀ y ∈ A, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, y = b * x * b⁻¹ := by
      intro x hx y hy hx1 hy1
      obtain ⟨b, hb, u, hu, hyx⟩ :=
        exists_mul_mul_of_cells B U c₀ hcell (hne x hx hx1) (hne y hy hy1)
      refine ⟨b, hb, ?_⟩
      have h1 : (b * x * b⁻¹)⁻¹ * y ∈ A :=
        A.mul_mem (A.inv_mem (‹A.Normal›.conj_mem x hx b)) hy
      have h2 : (b * x * b⁻¹)⁻¹ * y = b * u := by
        rw [hyx]
        simp [mul_assoc]
      have h3 : (b * x * b⁻¹)⁻¹ * y ∈ B := h2 ▸ B.mul_mem hb (hUB hu)
      exact (inv_mul_eq_one.mp (hmem _ h1 h3)).symm
    have hord : ∀ x y : A, x ≠ 1 → y ≠ 1 → orderOf x = orderOf y := by
      intro x y hx hy
      obtain ⟨b, hb, hyb⟩ := hconj x x.2 y y.2 (fun h => hx (Subtype.ext h))
        (fun h => hy (Subtype.ext h))
      rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe y]
      refine SemiconjBy.orderOf_eq b ?_
      rw [SemiconjBy, hyb]
      simp [mul_assoc]
    have ha1 : a ≠ 1 := fun h => haB (h ▸ B.one_mem)
    have : Nontrivial A := ⟨⟨⟨a, haA⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    rw [hindex] at hΩ
    exact hΩ (isPrimePow_natCard_of_orderOf_eq hord)

end CFSG.GH74.GLS.SP

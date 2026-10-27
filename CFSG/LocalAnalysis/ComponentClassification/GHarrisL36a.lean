module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL35

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.gen1_pow_four : SE.gen 1 ^ 4 = 1 := by decide

theorem SCert.SE.gen1_ne_one : SE.gen 1 ≠ 1 := by decide

theorem SCert.SE.gen1_ne_gen0 : SE.gen 1 ≠ SE.gen 0 := by decide

omit [Finite G] in
theorem mem_normalizer_zpowers {a b : G} (h1 : b * a * b⁻¹ ∈ zpowers a)
    (h2 : b⁻¹ * a * b ∈ zpowers a) : b ∈ normalizer (zpowers a : Set G) := by
  refine mem_normalizer_of_conj (fun w hw => ?_) fun w hw => ?_
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow]
    exact zpow_mem h1 k
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    have := conj_zpow (a := b⁻¹) (b := a) (i := k)
    rw [inv_inv] at this
    rw [← this]
    exact zpow_mem h2 k

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem z_mem_M : D.z ∈ D.M := mem_centralizer_singleton_iff.mpr rfl

omit [Finite G] in
theorem l_mem_M : D.l ∈ D.M := D.S_le_M (D.toG_mem _)

omit [Finite G] in
theorem l_pow_four : D.l ^ 4 = 1 := by rw [← map_pow, SE.gen1_pow_four, map_one]

theorem isolated_l_mod_z {g : G} (hg : g ∈ D.M)
    (hc : g * D.l * g⁻¹ * D.l = D.l * (g * D.l * g⁻¹) ∨
      g * D.l * g⁻¹ * D.l = D.l * (g * D.l * g⁻¹) * D.z) :
    g * D.l * g⁻¹ = D.l ∨ g * D.l * g⁻¹ = D.l * D.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u := g * D.l * g⁻¹ with hu
  have huM : u ∈ D.M := mul_mem (mul_mem hg D.l_mem_M) (inv_mem hg)
  have hz : ∀ y ∈ D.M, y * D.z = D.z * y := fun y hy => mem_centralizer_singleton_iff.mp hy
  have hl3 : D.l * D.z ∈ zpowers D.l := by
    rw [← D.l_mul_l]
    exact mul_mem (mem_zpowers _) (mul_mem (mem_zpowers _) (mem_zpowers _))
  have hu4 : u ^ (2 ^ 2) = 1 := by
    rw [hu, conj_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, D.l_pow_four]
    group
  have hlP : IsPGroup 2 (zpowers D.l) := by
    obtain ⟨b, -, hob⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show D.l ^ (2 ^ 2) = 1 from D.l_pow_four))
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hob])
  have huP : IsPGroup 2 (zpowers u) := by
    obtain ⟨b, -, hob⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu4)
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hob])
  have hun : u ∈ normalizer (zpowers D.l : Set G) := by
    have huz : u * D.z = D.z * u := hz u huM
    rcases hc with h | h
    · refine mem_normalizer_zpowers ?_ ?_
      · rw [show u * D.l * u⁻¹ = D.l by rw [h]; group]; exact mem_zpowers _
      · rw [show u⁻¹ * D.l * u = D.l by
          calc u⁻¹ * D.l * u = u⁻¹ * (D.l * u) := by group
            _ = u⁻¹ * (u * D.l) := by rw [← h]
            _ = D.l := by group]
        exact mem_zpowers _
    · refine mem_normalizer_zpowers ?_ ?_
      · rw [show u * D.l * u⁻¹ = D.l * D.z by
          calc u * D.l * u⁻¹ = D.l * u * D.z * u⁻¹ := by rw [h]
            _ = D.l * (u * D.z) * u⁻¹ := by group
            _ = D.l * (D.z * u) * u⁻¹ := by rw [huz]
            _ = D.l * D.z := by group]
        exact hl3
      · have h' : D.l * u = u * D.l * D.z := by
          calc D.l * u = D.l * u * D.z * D.z := by rw [mul_assoc _ D.z, D.z_mul_z, mul_one]
            _ = u * D.l * D.z := by rw [← h]
        rw [show u⁻¹ * D.l * u = D.l * D.z by
          calc u⁻¹ * D.l * u = u⁻¹ * (D.l * u) := by group
            _ = u⁻¹ * (u * D.l * D.z) := by rw [h']
            _ = D.l * D.z := by group]
        exact hl3
  have hP : IsPGroup 2 ↥(zpowers D.l ⊔ zpowers u) :=
    hlP.to_sup_of_normal_left' huP (zpowers_le.mpr hun)
  have hPM : zpowers D.l ⊔ zpowers u ≤ D.M :=
    sup_le (zpowers_le.mpr D.l_mem_M) (zpowers_le.mpr huM)
  have hSM : IsSylowOf 2 (D.S : Subgroup G) D.M := (isSylowOf_top D.S).of_le D.S_le_M le_top
  obtain ⟨c, hcM, hcP⟩ := exists_conj_le_of_isSylowOf hSM hPM hP
  have hw1 := D.eq_l_of_conj (g := c) hcM
    (hcP D.l (mem_sup_left (mem_zpowers _))) (Or.inl (by group))
  have hw2 := D.eq_l_of_conj (g := c * g) (mul_mem hcM hg)
    (hcP u (mem_sup_right (mem_zpowers _))) (Or.inl (by rw [hu]; group))
  have hcz : c⁻¹ * D.z * c = D.z := D.z_comm_of_mem_M hcM
  have hu' : u = c⁻¹ * (c * u * c⁻¹) * c := by group
  have hcl : c⁻¹ * D.l * c = D.l ∨ c⁻¹ * D.l * c = D.l * D.z := by
    rcases hw1 with h | h
    · left
      calc c⁻¹ * D.l * c = c⁻¹ * (c * D.l * c⁻¹) * c := by rw [h]
        _ = D.l := by group
    · right
      have h' : D.l = c⁻¹ * D.l * c * D.z := by
        calc D.l = c⁻¹ * (c * D.l * c⁻¹) * c := by group
          _ = c⁻¹ * (D.l * D.z) * c := by rw [h]
          _ = c⁻¹ * D.l * c * (c⁻¹ * D.z * c) := by group
          _ = c⁻¹ * D.l * c * D.z := by rw [hcz]
      calc c⁻¹ * D.l * c = c⁻¹ * D.l * c * D.z * D.z := by
            rw [mul_assoc (c⁻¹ * D.l * c), D.z_mul_z, mul_one]
        _ = D.l * D.z := by rw [← h']
  rw [hu']
  rcases hw2 with h | h <;> rw [h]
  · exact hcl
  · rw [show c⁻¹ * (D.l * D.z) * c = (c⁻¹ * D.l * c) * (c⁻¹ * D.z * c) by group, hcz]
    rcases hcl with h' | h' <;> rw [h']
    · exact Or.inr rfl
    · left; rw [mul_assoc, D.z_mul_z, mul_one]

end GHSylow

end CFSG.ComponentClassification.GHarris

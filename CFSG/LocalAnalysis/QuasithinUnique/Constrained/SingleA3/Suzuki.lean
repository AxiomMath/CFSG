module

public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour

public section

namespace CFSG.QuasithinUnique

variable {G : Type*} [Group G] [Finite G]

theorem suzuki_selfCentralizing_four {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hU4 : Nat.card U = 4) (hUexp : ∀ u ∈ U, u ^ 2 = 1)
    (hC : T ⊓ Subgroup.centralizer (U : Set G) ≤ U) (hne : U ≠ T) :
    (∃ k : ℕ, 2 ≤ k ∧ Nonempty (T ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (T ≃* CFSG.Open.SemidihedralGroup n) := by
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have hab : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hUexp _ (U.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hUexp a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hUexp b hb)
    calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  set V : Subgroup T := U.subgroupOf T with hV
  have hVab : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (hUab _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hUexp _ (Subgroup.mem_subgroupOf.mp hv)
  have hVcard : Nat.card V = 4 := by
    rw [hV, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUT).toEquiv, hU4]
  have hVcent : Subgroup.centralizer (V : Set T) = V := by
    refine le_antisymm (fun s hs => ?_) (fun v hv => ?_)
    · rw [hV, Subgroup.mem_subgroupOf]
      apply hC
      refine ⟨s.2, ?_⟩
      show (s : G) ∈ Subgroup.centralizer (U : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h := Subgroup.mem_centralizer_iff.mp hs ⟨u, hUT hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      exact congrArg Subtype.val h
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subtype.ext
        (hUab _ (Subgroup.mem_subgroupOf.mp hw) _ (Subgroup.mem_subgroupOf.mp hv))
  rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hT V hVab hVexp hVcard hVcent with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  ·
    have hcard : Nat.card T = 2 * 2 ^ (n - 1) := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hn3 : 3 ≤ n := by
      by_contra h
      obtain rfl : n = 2 := by omega
      have h4 : Nat.card T = 4 := hcard.trans (by norm_num)
      exact hne (Subgroup.eq_of_le_of_card_ge hUT (h4.trans hU4.symm).le)
    exact Or.inl ⟨n - 1, by omega, ⟨e⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e⟩⟩

end CFSG.QuasithinUnique

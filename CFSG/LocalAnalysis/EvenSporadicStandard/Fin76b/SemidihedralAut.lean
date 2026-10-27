module

public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open CFSG.Semidihedral

theorem isSolvable_mulAut_of_characteristic_cyclic {G : Type*} [Group G] (C : Subgroup G)
    [C.Characteristic] [IsCyclic C] (hC : C.index = 2) : Group.IsSolvable (MulAut G) := by
  obtain ⟨s, hs⟩ : ∃ s : G, s ∉ C := by
    by_contra hcon
    rw [(Subgroup.eq_top_iff' C).mpr fun g => not_not.mp fun hg => hcon ⟨g, hg⟩,
      Subgroup.index_top] at hC
    omega
  have hout : ∀ g : G, g ∉ C → s⁻¹ * g ∈ C := fun g hg =>
    (Subgroup.mul_mem_iff_of_index_two hC).mpr
      (iff_of_false (fun h => hs (by simpa using C.inv_mem h)) hg)
  set ρ : MulAut G →* MulAut C := MulAut.characteristic C
  have hfix : ∀ φ ∈ ρ.ker, ∀ c ∈ C, φ c = c := fun φ hφ c hc =>
    congrArg (fun ψ : MulAut C => (ψ ⟨c, hc⟩ : G)) (MonoidHom.mem_ker.mp hφ)
  have hshift : ∀ φ ∈ ρ.ker, ∃ a ∈ C, φ s = s * a := by
    intro φ hφ
    refine ⟨s⁻¹ * φ s, ?_, by simp⟩
    by_cases h : φ s ∈ C
    · exfalso
      have h1 : φ s = s := φ.injective (hfix φ hφ _ h)
      exact hs (h1 ▸ h)
    · exact hout _ h
  have hcomm : ∀ φ ∈ ρ.ker, ∀ ψ ∈ ρ.ker, φ * ψ = ψ * φ := by
    intro φ hφ ψ hψ
    obtain ⟨a, ha, hφs⟩ := hshift φ hφ
    obtain ⟨b, hb, hψs⟩ := hshift ψ hψ
    have hab : a * b = b * a := setLike_mul_comm (s := C) ha hb
    refine MulEquiv.ext fun x => ?_
    by_cases hx : x ∈ C
    · simp only [MulAut.mul_apply, hfix φ hφ x hx, hfix ψ hψ x hx]
    · obtain ⟨c, hc, rfl⟩ : ∃ c ∈ C, x = s * c := ⟨s⁻¹ * x, hout x hx, by simp⟩
      simp only [MulAut.mul_apply, map_mul, hφs, hψs, hfix φ hφ b hb, hfix ψ hψ a ha,
        hfix φ hφ c hc, hfix ψ hψ c hc]
      rw [mul_assoc s a b, mul_assoc s b a, hab]
  have : IsMulCommutative ρ.ker :=
    IsMulCommutative.of_comm fun φ ψ => Subtype.ext (hcomm φ φ.2 ψ ψ.2)
  have : Group.IsSolvable (MulAut C) :=
    Group.isSolvable_of_isSolvable_injective (f := (IsCyclic.mulAutMulEquiv C).toMonoidHom)
      (IsCyclic.mulAutMulEquiv C).injective
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by rw [Subgroup.range_subtype])

theorem mulAut_r_mem_zpowers {n : ℕ} (hn : 4 ≤ n) (φ : MulAut (SemidihedralGroup n)) :
    φ (r n) ∈ Subgroup.zpowers (r n) := by
  have hn3 : 3 ≤ n := by omega
  have hord : orderOf (φ (r n)) = 2 ^ (n - 1) := by
    rw [MulEquiv.orderOf_eq, orderOf_r n hn3]
    rfl
  obtain ⟨⟨i, e⟩, hie⟩ := (coordinateEquiv n hn3).symm.surjective (φ (r n))
  change element n hn3 i e = φ (r n) at hie
  rw [← hie] at hord ⊢
  rcases exponent_cases e with rfl | rfl
  · rw [element_eq]
    simp
  · exfalso
    have h8 : 8 ≤ 2 ^ (n - 1) :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    by_cases hi : i.val % 2 = 0
    · have h2 := (outside_involution_iff n hn3 i).mpr hi
      omega
    · have h4 := (outside_order_four_iff n hn3 i).mpr (by omega)
      omega

theorem zpowers_r_characteristic {n : ℕ} (hn : 4 ≤ n) :
    (Subgroup.zpowers (r n)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [map_zpow]
  exact Subgroup.zpow_mem _ (mulAut_r_mem_zpowers hn φ) k

theorem semidihedral_mulAut_isSolvable (n : ℕ) (hn : 4 ≤ n) :
    Group.IsSolvable (MulAut (SemidihedralGroup n)) := by
  have := zpowers_r_characteristic hn
  exact isSolvable_mulAut_of_characteristic_cyclic (Subgroup.zpowers (r n))
    (rotation_index n (by omega))

end CFSG.EvenSporadicStandard.Fin76b

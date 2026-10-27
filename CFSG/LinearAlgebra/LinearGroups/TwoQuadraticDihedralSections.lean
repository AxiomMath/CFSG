module

public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralSubgroupShapes

public section

namespace CFSG.LinearGroups

open CFSG.Semidihedral.Principal

universe v

theorem isCyclic_of_surjective_of_dihedral {D Q : Type*} [Group D] [Group Q] {m : ℕ}
    (hm : 2 ≤ m) (hD : Nonempty (DihedralGroup (2 ^ (m - 1)) ≃* D)) (f : D →* Q)
    (hf : Function.Surjective f) (huniq : ∀ u v : Q, orderOf u = 2 → orderOf v = 2 → u = v) :
    IsCyclic Q := by
  obtain ⟨⟨r, s, hr, hs, hrel, hgen⟩, hall⟩ := dihedral_rotation_involution_structure hm hD
  obtain ⟨-, hAidx, -, -, hinvol, -⟩ := hall r s hr hs hrel hgen
  have hsA : s ∉ Subgroup.zpowers r := by
    intro hs'
    have hle : Subgroup.closure ({r, s} : Set D) ≤ Subgroup.zpowers r := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_zpowers x
      · exact hs'
    rw [hgen, top_le_iff] at hle
    rw [hle, Subgroup.index_top] at hAidx
    exact absurd hAidx (by norm_num)
  have hdecomp : ∀ d : D, d ∉ Subgroup.zpowers r → s⁻¹ * d ∈ Subgroup.zpowers r := by
    intro d hd
    rw [Subgroup.mul_mem_iff_of_index_two hAidx]
    exact ⟨fun h => absurd (inv_mem_iff.mp h) hsA, fun h => absurd h hd⟩
  have hfr : ∀ c ∈ Subgroup.zpowers r, f c ∈ Subgroup.zpowers (f r) := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ⟨k, by rw [map_zpow]⟩
  by_cases hcase : f s ∈ Subgroup.zpowers (f r)
  · refine ⟨⟨f r, fun q => ?_⟩⟩
    obtain ⟨d, rfl⟩ := hf q
    by_cases hd : d ∈ Subgroup.zpowers r
    · exact hfr d hd
    · rw [show d = s * (s⁻¹ * d) by group, map_mul]
      exact Subgroup.mul_mem _ hcase (hfr _ (hdecomp d hd))
  · have hord2 : ∀ c ∈ Subgroup.zpowers r, orderOf (f (s * c)) = 2 := by
      intro c hc
      have hsc : s * c ∉ Subgroup.zpowers r := fun h =>
        hsA (by simpa using Subgroup.mul_mem _ h (Subgroup.inv_mem _ hc))
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow, ← hinvol _ hsc, pow_orderOf_eq_one, map_one]
      · intro h1
        apply hcase
        have : f s = (f c)⁻¹ := by
          rw [map_mul] at h1
          exact eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact Subgroup.inv_mem _ (hfr c hc)
    have hA1 : ∀ c ∈ Subgroup.zpowers r, f c = 1 := by
      intro c hc
      have hs2 : orderOf (f s) = 2 := by
        simpa using hord2 1 (Subgroup.one_mem (Subgroup.zpowers r))
      have h1 := huniq _ _ (hord2 c hc) hs2
      rw [map_mul] at h1
      simpa using h1
    refine ⟨⟨f s, fun q => ?_⟩⟩
    obtain ⟨d, rfl⟩ := hf q
    by_cases hd : d ∈ Subgroup.zpowers r
    · rw [hA1 d hd]
      exact (Subgroup.zpowers (f s)).one_mem
    · rw [show d = s * (s⁻¹ * d) by group, map_mul, hA1 _ (hdecomp d hd), mul_one]
      exact Subgroup.mem_zpowers _

theorem dihedral_sections_two_quadratic_generators_have_odd_order {G : Type*} [Group G]
    [Finite G] (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) (H : Subgroup G)
    (N : Subgroup H) [N.Normal] {F : Type*} [Field F] {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    [CharP F p] {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (ρ : H ⧸ N →* LinearMap.GeneralLinearGroup F V) (hρ : Function.Injective ρ)
    (hirr : ∀ W : Submodule F V, (∀ g : H ⧸ N, ∀ w ∈ W, (ρ g : V →ₗ[F] V) w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (a b : H ⧸ N) (hab : Subgroup.closure ({a, b} : Set (H ⧸ N)) = ⊤) (hX1 : ρ a ≠ 1)
    (hY1 : ρ b ≠ 1) (hX : ((ρ a : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hY : ((ρ b : V →ₗ[F] V) - 1) ^ 2 = 0) :
    Odd (Nat.card (H ⧸ N)) := by
  have huniq := two_quadratic_unique_involution hp hodd ρ hρ hirr a b hab hX1 hY1 hX hY
  obtain ⟨D, T, f, hDp, hf⟩ := exists_two_subgroup_onto_sylow H N
  have hTuniq : ∀ u v : (T : Subgroup (H ⧸ N)), orderOf u = 2 → orderOf v = 2 → u = v :=
    fun u v hu hv => Subtype.ext (huniq u v (by rw [Subgroup.orderOf_coe]; exact hu)
      (by rw [Subgroup.orderOf_coe]; exact hv))
  have hTcyc : IsCyclic (T : Subgroup (H ⧸ N)) := by
    rcases (sylow_dihedral_two_subgroup_shapes S hn hS).1 D hDp with hc | ⟨m, hm, -, ⟨e⟩⟩
    · exact isCyclic_of_surjective f hf
    · exact isCyclic_of_surjective_of_dihedral hm ⟨e.symm⟩ f hf hTuniq
  exact odd_card_of_cyclic_sylow_two a b hab (odd_orderOf_of_quadratic hp hodd ρ hρ hX)
    (odd_orderOf_of_quadratic hp hodd ρ hρ hY) T hTcyc

end CFSG.LinearGroups

module

public import CFSG.LargeExtraspecial.AS35ZSDisjC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

namespace ZSHyp

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : PG n →* (V ≃ₗ[ZMod 2] V)} {q : QuadraticForm (ZMod 2) V} (h : ZSHyp n q ρ)
include h

theorem inf_lineA_eq_bot_of_perp {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy : herm frob y y = 0) (hxy : herm frob x y = 0) (hyx : ∀ c : K, y ≠ c • x) :
    lineA ρ x ⊓ lineA ρ y = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := h.four_le; omega⟩
  rcases (by have := h.four_le; omega : m = 2 ∨ 3 ≤ m) with rfl | hm
  · exact h.inf_lineA_eq_bot_of_perp_four hx0 hx hy hxy hyx
  · exact h.inf_lineA_eq_bot_of_perp_five hm hx0 hx hy hxy hyx

theorem apply_eq_self_of_perp {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y = 0) {v : V}
    (hv : v ∈ lineA ρ x) : ρ (tq y) v = v := by
  by_cases hyx : ∀ c : K, y ≠ c • x
  · have hm : ρ (tq y) v - v ∈ lineA ρ x ⊓ lineA ρ y :=
      Submodule.mem_inf.2 ⟨(lineA ρ x).sub_mem
        (apply_mem_lineA_of_perp hx hy hxy hv) hv, sub_mem_commSpace _ _⟩
    rw [h.inf_lineA_eq_bot_of_perp hx0 hx hy hxy hyx, Submodule.mem_bot, sub_eq_zero] at hm
    exact hm
  · push Not at hyx
    obtain ⟨c, rfl⟩ := hyx
    have hc : c ≠ 0 := by rintro rfl; exact hy0 (zero_smul K x)
    rw [tq, tvU_smul_vec hx hc]
    exact apply_eq_self_of_mem_lineA hx hv

theorem polar_eq_zero_of_perp {x y : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0)
    (hy0 : y ≠ 0) (hy : herm frob y y = 0) (hxy : herm frob x y = 0) {a b : V}
    (ha : a ∈ lineA ρ x) (hb : b ∈ lineA ρ y) : polar q a b = 0 := by
  have hfix : a ∈ fixSpace (ρ (tq y)) :=
    mem_fixSpace.2 (h.apply_eq_self_of_perp hx0 hx hy0 hy hxy ha)
  rw [fixSpace_eq_orthogonal_commSpace h.nondeg (h.a2.mem_orthogonalGroup _) (tq_mul_self' hy),
    LinearMap.BilinForm.mem_orthogonal_iff] at hfix
  have := hfix b hb
  rw [polar_comm]
  exact this

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS

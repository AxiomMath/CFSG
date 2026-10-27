module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

section SylowConj

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow (S : Sylow 2 G) {y : G} (hy : y * y = 1) :
    ∃ g : G, g * y * g⁻¹ ∈ (S : Subgroup G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(zpowers y) := by
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; rfl)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨g, ?_⟩
  have hyQ : y ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers y)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨y, hyQ, by simp [MulAut.conj_apply]⟩

end SylowConj

section Thompson

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_mem_of_thompson (hsimple : IsSimpleGroup X)
    (hnonab : ∃ a b : X, a * b ≠ b * a) {T U : Subgroup X} (hT : IsPGroup 2 ↥T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : X} (hxT : x ∈ T)
    (hxU : x ∉ U) (hx2 : orderOf x = 2) : ∃ g : X, g⁻¹ * x * g ∈ U := by
  by_contra hcon
  push Not at hcon
  have hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have h2 : 0 < orderOf y := orderOf_pos y
    rw [hx2]
    omega
  obtain ⟨M, hM, hMidx⟩ := ThompsonIndexTwo.exists_normal_index_two_of_thompson hT hTidx hUT hUidx
    hxT hxU hmin hcon
  rcases hM.eq_bot_or_eq_top with h1 | h1
  · rw [h1, Subgroup.index_bot] at hMidx
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isCyclic_of_prime_card (α := X) hMidx
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h1, Subgroup.index_top] at hMidx
    exact absurd hMidx (by norm_num)

end Thompson

end CFSG.OddStandard.Solomon75

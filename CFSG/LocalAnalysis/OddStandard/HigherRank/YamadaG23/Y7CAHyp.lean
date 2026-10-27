module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAHyp1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAOdd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.ASVolI.ChIJK CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

private theorem y7c_inv_eq_self_of_sq {G : Type} [Group G] {x : G} (hx : x ^ 2 = 1) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)

private theorem y7c_orderOf_eq_two {G : Type} [Group G] {x : G} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

private theorem y7c_conjugate_one (L : Subgroup Γ) : CFSG.conjugate L (1 : Γ) = L := by
  ext x
  simp [CFSG.conjugate]

theorem y7c_component_cover (hI31 : CFSG.ASVolI.I_3_1) (c : K7Abs ρ t J Q P M6 M7) :
    ∃ K : Subgroup Γ, CFSG.IsComponent K ∧ J ≤ K ⊔ conjSub t K := by
  have ht2 : t ^ 2 = 1 := c.t_sq
  have ht_inv : t⁻¹ = t := y7c_inv_eq_self_of_sq ht2
  have hord : orderOf t = 2 := y7c_orderOf_eq_two ht2 c.t_ne
  have hPt : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by
      simpa using orderOf_dvd_of_pow_eq_one ht2)
  obtain ⟨K, hK1, hK2, _⟩ :=
    hI31 Γ c.kgroup (Subgroup.zpowers t) hPt J (y7c_J_isTwoComponent c)
  have hKcomp : CFSG.IsComponent K := by
    have hKi : IsComponentIn K ⊤ := (hK2 (y7c_J_le_cent_oddCore c)).2
    unfold IsComponentIn at hKi
    exact ⟨hKi.2.1, IsSubnormal.trans le_top hKi.2.2 IsSubnormal.top⟩
  have hJle : J ≤ conjClosure J (oddCoreE Γ) := by
    unfold conjClosure
    exact le_iSup₂_of_le (1 : Γ) (Subgroup.one_mem _) (y7c_conjugate_one J).ge
  have hconj_t : CFSG.conjugate K t = conjSub t K := by
    unfold CFSG.conjugate conjSub
    rw [ht_inv]
  have hcl : conjClosure K (Subgroup.zpowers t) ≤ K ⊔ conjSub t K := by
    unfold conjClosure
    refine iSup₂_le fun y hy => ?_
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨k, rfl⟩ := hy
    have hk : t ^ k = 1 ∨ t ^ k = t := by
      have hmod : t ^ k = t ^ (k % (2 : ℤ)) := by
        rw [← zpow_mod_orderOf t k, hord]
        rfl
      rw [hmod]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · exact Or.inl (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp)
    rcases hk with hk | hk
    · rw [hk, y7c_conjugate_one K]
      exact le_sup_left
    · rw [hk, hconj_t]
      exact le_sup_right
  refine ⟨K, hKcomp, hJle.trans ?_⟩
  rw [hK1.2]
  exact hcl

end CFSG.OddStandard.HigherRank.YamadaG23

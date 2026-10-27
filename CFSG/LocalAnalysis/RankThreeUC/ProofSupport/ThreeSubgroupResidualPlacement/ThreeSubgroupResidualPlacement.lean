module


public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ThreeSubgroupResidualPlacement

open CFSG.LocalAnalysis.RankThreeUC

theorem card_three_le_oPrimeResidual {G : Type} [Group G] {W D : Subgroup G}
    (hDW : D ≤ W) (hD : Nat.card D = 3) : D ≤ SourceSetting.oPrimeResidual 3 W := by
  intro x hx
  haveI : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have h1 : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : D)
    rwa [hD, Subgroup.orderOf_mk] at this
  have h3 : orderOf x ∣ 3 ^ 1 := by simpa using h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h3
  exact Subgroup.subset_closure ⟨hDW hx, k, hk⟩

theorem exists_card_three_le {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : SourceSetting.oPrimeResidual 3 X = X) (hnb : X ≠ ⊥) :
    ∃ D : Subgroup G, D ≤ X ∧ Nat.card D = 3 := by
  by_contra hcon
  apply hnb
  rw [← hX, eq_bot_iff, SourceSetting.oPrimeResidual, Subgroup.closure_le]
  rintro x ⟨hxX, k, hk⟩
  by_contra hx1
  have hx1' : x ≠ 1 := by simpa using hx1
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1' (orderOf_eq_one_iff.1 (by simpa using hk))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set g := x ^ (3 ^ j) with hg
  have hord : orderOf g = 3 := by
    have h3 : 0 < 3 ^ j := pow_pos (by norm_num) _
    rw [hg, orderOf_pow_of_dvd h3.ne' (by rw [hk]; exact pow_dvd_pow 3 (by omega)), hk,
      pow_succ, Nat.mul_div_cancel_left _ h3]
  apply hcon
  refine ⟨Subgroup.zpowers g, ?_, ?_⟩
  · rw [Subgroup.zpowers_le]; exact Subgroup.pow_mem _ hxX _
  · rw [Nat.card_zpowers, hord]

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ThreeSubgroupResidualPlacement

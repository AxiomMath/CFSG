module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK7Cent
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK7TriLift
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalKron
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalKronOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open

variable {K : Type} [Field K]

theorem dvd_natCard_centralizer_singleton_of_commute {G : Type*} [Group G] [Finite G]
    {x g : G} {p : ℕ} (hcomm : Commute x g) (hord : orderOf g = p) :
    p ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have hg : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : ↥(Subgroup.centralizer ({x} : Set G)))
  rwa [Subgroup.orderOf_mk, hord] at h

private theorem dvd_card_mul_sq_sub_one [Finite K] {p : ℕ}
    (hdvd : p ∣ cardPlusPi (Nat.card K)) : p ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
  dvd_mul_sq_sub_one_of_dvd_cardPlusPi Nat.card_pos hdvd

theorem dvd_natCard_centralizer_c₀_weight_one [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardPlusPi (Nat.card K)) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ F (Multiplicative.ofAdd ![1, 0, 0])} : Set ↥(Omega7 K))) := by
  obtain ⟨g, hord, hcomm⟩ := exists_orderOf_eq_commute_c₀_of_two_eq_zero F hp hp2
    (dvd_card_mul_sq_sub_one hdvd)
  exact dvd_natCard_centralizer_singleton_of_commute (hcomm _ rfl) hord

theorem dvd_natCard_centralizer_c₀_weight_two [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardPlusPi (Nat.card K)) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ F (Multiplicative.ofAdd ![1, 1, 0])} : Set ↥(Omega7 K))) := by
  obtain ⟨g, hord, hcomm⟩ := exists_orderOf_eq_commute_c₀_of_two_eq_zero F hp hp2
    (dvd_card_mul_sq_sub_one hdvd)
  exact dvd_natCard_centralizer_singleton_of_commute (hcomm _ rfl) hord

theorem dvd_natCard_centralizer_c₀_weight_three [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ cardPlusPi (Nat.card K)) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ F (Multiplicative.ofAdd ![1, 1, 1])} : Set ↥(Omega7 K))) := by
  obtain ⟨A, hAorth, hAord⟩ := exists_orthogonal_orderOf_eq (K := K) F.hK hp
    (dvd_card_mul_sq_sub_one hdvd)
  have hodd : Odd (orderOf A) := by
    rw [hAord]
    exact hp.eq_two_or_odd'.resolve_left hp2
  have hu : (![1, 1, 1] : Fin 3 → ZMod 3) = fun _ => 1 := by
    funext i
    fin_cases i <;> rfl
  rw [hu]
  exact dvd_natCard_centralizer_singleton_of_commute (commute_c₀_kronElt F hAorth hodd 1)
    (by rw [orderOf_kronElt, hAord])

theorem k7_b_omega7 [Finite K] (F : Frame K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ cardPlusPi (Nat.card K)) :
    ¬ p ∣ Nat.card (Subgroup.centralizer ((c₀ F).range : Set ↥(Omega7 K))) ∧
      p ∣ Nat.card (Subgroup.centralizer
        ({c₀ F (Multiplicative.ofAdd ![1, 0, 0])} : Set ↥(Omega7 K))) ∧
      p ∣ Nat.card (Subgroup.centralizer
        ({c₀ F (Multiplicative.ofAdd ![1, 1, 0])} : Set ↥(Omega7 K))) ∧
      p ∣ Nat.card (Subgroup.centralizer
        ({c₀ F (Multiplicative.ofAdd ![1, 1, 1])} : Set ↥(Omega7 K))) :=
  ⟨not_dvd_natCard_centralizer_range F hp hp2 hdvd,
    dvd_natCard_centralizer_c₀_weight_one F hp hp2 hdvd,
    dvd_natCard_centralizer_c₀_weight_two F hp hp2 hdvd,
    dvd_natCard_centralizer_c₀_weight_three F hp hp2 hdvd⟩

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

module

public import CFSG.ClassicalInvolution.Q3.Q3MFin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open scoped MatrixGroups commutatorElement
open CFSG.ClassicalInvolution

private theorem comm_pow_four : ∀ a b : SL(2, ZMod 3), ⁅a, b⁆ ^ 4 = 1 := by decide +kernel

private theorem exists_comm_of_pow_four :
    ∀ g : SL(2, ZMod 3), g ^ 4 = 1 → ∃ a b : SL(2, ZMod 3), ⁅a, b⁆ = g := by decide +kernel

private theorem comm_pow_four_mem_center :
    ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = -1 := by decide +kernel

private theorem exists_comm_neg_one :
    ∃ a b : SL(2, ZMod 3), a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ ⁅a, b⁆ = -1 := by decide +kernel

private theorem sq_eq_one_cases : ∀ y : SL(2, ZMod 3), y ^ 2 = 1 → y = 1 ∨ y = -1 := by
  decide +kernel

private theorem pow_eight_imp_pow_four : ∀ y : SL(2, ZMod 3), y ^ 8 = 1 → y ^ 4 = 1 := by
  decide +kernel

private theorem coset_pow_four :
    ∀ x g : SL(2, ZMod 3), x ^ 4 ≠ 1 → ∃ k : Fin 3, (g * (x ^ (k : ℕ))⁻¹) ^ 4 = 1 := by
  decide +kernel

theorem sl2Three_commutator_eq : commutator SL(2, ZMod 3) = sl2ThreeQ := by
  refine le_antisymm ?_ ?_
  · rw [commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => mem_sl2ThreeQ_iff.mpr (comm_pow_four a b)
  · intro g hg
    obtain ⟨a, b, rfl⟩ := exists_comm_of_pow_four g (mem_sl2ThreeQ_iff.mp hg)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem sl2Three_mem_commutator_iff {g : SL(2, ZMod 3)} :
    g ∈ commutator SL(2, ZMod 3) ↔ g ^ 4 = 1 := by
  rw [sl2Three_commutator_eq, mem_sl2ThreeQ_iff]

theorem sl2Three_card_commutator : Nat.card (commutator SL(2, ZMod 3)) = 8 := by
  rw [sl2Three_commutator_eq]
  exact natCard_sl2ThreeQ

theorem sl2Three_derived₂_eq_center :
    ⁅commutator SL(2, ZMod 3), commutator SL(2, ZMod 3)⁆ = Subgroup.center SL(2, ZMod 3) := by
  rw [sl2Three_commutator_eq]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_center_sl2_iff]
    exact comm_pow_four_mem_center a b (mem_sl2ThreeQ_iff.mp ha) (mem_sl2ThreeQ_iff.mp hb)
  · intro x hx
    rcases (mem_center_sl2_iff x).mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · obtain ⟨a, b, ha, hb, hab⟩ := exists_comm_neg_one
      rw [← hab]
      exact Subgroup.commutator_mem_commutator (mem_sl2ThreeQ_iff.mpr ha)
        (mem_sl2ThreeQ_iff.mpr hb)

theorem sl2Three_neg_one_mem_derived₂ :
    (-1 : SL(2, ZMod 3)) ∈ ⁅commutator SL(2, ZMod 3), commutator SL(2, ZMod 3)⁆ := by
  rw [sl2Three_derived₂_eq_center, mem_center_sl2_iff]
  exact Or.inr rfl

theorem sl2Three_derived₃_eq_bot :
    ⁅⁅commutator SL(2, ZMod 3), commutator SL(2, ZMod 3)⁆,
      ⁅commutator SL(2, ZMod 3), commutator SL(2, ZMod 3)⁆⁆ = ⊥ := by
  rw [sl2Three_derived₂_eq_center, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_center_iff.mp hb a

theorem sl2Three_isSolvable : Group.IsSolvable SL(2, ZMod 3) := by
  refine ⟨⟨3, ?_⟩⟩
  rw [derivedSeries_succ, derivedSeries_succ, derivedSeries_succ, derivedSeries_zero,
    ← commutator_def]
  exact sl2Three_derived₃_eq_bot

theorem sl2Three_not_isPerfect : ¬ Group.IsPerfect SL(2, ZMod 3) := fun h => by
  have h8 := sl2Three_card_commutator
  rw [h.commutator_eq_top, Subgroup.card_top, natCard_sl2Three] at h8
  omega

theorem sl2Three_pow_four_of_two_element {g : SL(2, ZMod 3)} (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) :
    g ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := hg
  have hdvd : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h24 : orderOf g ∣ 8 * 3 := orderOf_dvd_of_pow_eq_one (Q3.M.sl2_pow_24 g)
  have hcop : Nat.Coprime (orderOf g) 3 :=
    Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left n (by norm_num))
  have h8 : orderOf g ∣ 8 := hcop.dvd_of_dvd_mul_right h24
  exact pow_eight_imp_pow_four g (orderOf_dvd_iff_pow_eq_one.mp h8)

theorem sl2Three_mem_commutator_of_two_element {g : SL(2, ZMod 3)}
    (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) : g ∈ commutator SL(2, ZMod 3) :=
  sl2Three_mem_commutator_iff.mpr (sl2Three_pow_four_of_two_element hg)

theorem sl2Three_normal_cases (N : Subgroup SL(2, ZMod 3)) (hN : N.Normal) :
    N = ⊥ ∨ N = Subgroup.center SL(2, ZMod 3) ∨ N = commutator SL(2, ZMod 3) ∨ N = ⊤ := by
  by_cases h2 : ∃ y ∈ N, y ^ 2 ≠ 1
  · obtain ⟨y, hy, hy2⟩ := h2
    have hQ : sl2ThreeQ ≤ N := Q3.M.sl2_normal_Q N hy hy2
    by_cases h4 : ∀ x ∈ N, x ^ 4 = 1
    · right; right; left
      rw [sl2Three_commutator_eq]
      exact le_antisymm (fun x hx => mem_sl2ThreeQ_iff.mpr (h4 x hx)) hQ
    · right; right; right
      push Not at h4
      obtain ⟨x, hx, hx4⟩ := h4
      refine eq_top_iff.mpr fun g _ => ?_
      obtain ⟨k, hk⟩ := coset_pow_four x g hx4
      have hq : g * (x ^ (k : ℕ))⁻¹ ∈ N := hQ (mem_sl2ThreeQ_iff.mpr hk)
      have := N.mul_mem hq (N.pow_mem hx k)
      rwa [inv_mul_cancel_right] at this
  · push Not at h2
    have hle : N ≤ Subgroup.center SL(2, ZMod 3) := fun y hy => by
      rw [mem_center_sl2_iff]
      exact sq_eq_one_cases y (h2 y hy)
    by_cases hneg : (-1 : SL(2, ZMod 3)) ∈ N
    · right; left
      refine le_antisymm hle fun x hx => ?_
      rcases (mem_center_sl2_iff x).mp hx with rfl | rfl
      · exact N.one_mem
      · exact hneg
    · left
      refine (Subgroup.eq_bot_iff_forall N).mpr fun x hx => ?_
      rcases (mem_center_sl2_iff x).mp (hle hx) with rfl | rfl
      · rfl
      · exact absurd hx hneg

theorem sq_eq_one_of_card_three {F : Type*} [Field F] (hF : Nat.card F = 3) {a : F}
    (ha : a ≠ 0) : a ^ 2 = 1 := by
  have h2 : Nat.card Fˣ = 2 := by rw [Nat.card_units, hF]
  have := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 a ha)
  rw [h2] at this
  simpa using congrArg Units.val this

theorem not_exists_ne_zero_sq_ne_one_of_card_three {F : Type*} [Field F] (hF : Nat.card F = 3) :
    ¬ ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 :=
  fun ⟨_, ha, h⟩ => h (sq_eq_one_of_card_three hF ha)

end CFSG.ClassicalInvolution.Q3.Q3T6

module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem l2_om_pigeon {Ω S : Type} [Group Ω] [Finite Ω] [Group S] [Finite S] (π : Ω →* S)
    (hker : Nat.card π.ker ≤ 2) {A : Subgroup S} (hA : Nat.card ↥A ≤ 16) (D : Finset Ω)
    (hD : 33 ≤ D.card) : ∃ d ∈ D, π d ∉ A := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  letI : Fintype S := Fintype.ofFinite S
  by_contra h
  push_neg at h
  let t : Finset S := (A : Set S).toFinset
  have htcard : t.card = Nat.card ↥A := by
    change (A : Set S).toFinset.card = Nat.card ↥A
    rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    rfl
  have hfiber : ∀ b ∈ t, (D.filter fun x => π x = b).card ≤ Nat.card π.ker := by
    intro b _
    rcases (D.filter fun x => π x = b).eq_empty_or_nonempty with hempty | ⟨d0, hd0⟩
    · rw [hempty]
      exact Nat.zero_le _
    · have hd0' : π d0 = b := (Finset.mem_filter.mp hd0).2
      have hcard : (D.filter fun x => π x = b).card ≤ Fintype.card ↥π.ker := by
        rw [← Fintype.card_coe (D.filter fun x => π x = b)]
        refine Fintype.card_le_of_injective
          (fun x : ↥(D.filter fun x => π x = b) =>
            (⟨d0⁻¹ * (x : Ω), by
              have hx : π (x : Ω) = b := (Finset.mem_filter.mp x.2).2
              show π (d0⁻¹ * (x : Ω)) = 1
              rw [map_mul, map_inv, hd0', hx, inv_mul_cancel]⟩ : ↥π.ker)) ?_
        intro x y hxy
        exact Subtype.ext (mul_left_cancel (Subtype.ext_iff.mp hxy))
      simpa [Nat.card_eq_fintype_card] using hcard
  have hDle : D.card ≤ 2 * t.card :=
    Finset.card_le_mul_card_image_of_maps_to (f := π) (s := D) (t := t) (n := 2)
      (fun a ha => by
        have : π a ∈ A := h a ha
        simpa [t] using this)
      (fun b hb => le_trans (hfiber b hb) hker)
  have htle : t.card ≤ 16 := by
    rw [htcard]
    exact hA
  have hle32 : D.card ≤ 32 :=
    calc D.card ≤ 2 * t.card := hDle
      _ ≤ 2 * 16 := Nat.mul_le_mul_left 2 htle
      _ = 32 := rfl
  exact (Nat.not_succ_le_self 32) (le_trans hD hle32)

end CFSG.OddStandard.HigherRank.YamadaG23
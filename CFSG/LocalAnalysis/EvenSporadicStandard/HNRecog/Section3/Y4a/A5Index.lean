module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private theorem y4aA5Index_card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

private theorem y4aA5Index_pow_six :
    ∀ g : alternatingGroup (Fin 5), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

theorem y4a_eq_top_of_index_le_four {H : Subgroup (alternatingGroup (Fin 5))}
    (h : H.index ≤ 4) : H = ⊤ := by
  have hsimple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  let φ : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (↥(alternatingGroup (Fin 5)) ⧸ H) :=
    MulAction.toPermHom _ _
  rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h0 | h1
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h0
    have hle := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, y4aA5Index_card] at hle
    have h4 : Nat.card (↥(alternatingGroup (Fin 5)) ⧸ H) ≤ 4 := h
    have h5 := Nat.factorial_le h4
    have h24 : Nat.factorial 4 = 24 := by decide
    omega
  · rw [eq_top_iff]
    intro g _
    have h2 : φ g = 1 := by
      rw [← MonoidHom.mem_ker, h1]
      exact Subgroup.mem_top g
    have h3 : g • (QuotientGroup.mk 1 : ↥(alternatingGroup (Fin 5)) ⧸ H) = QuotientGroup.mk 1 := by
      have := congrArg (fun f : Equiv.Perm (↥(alternatingGroup (Fin 5)) ⧸ H) =>
        f (QuotientGroup.mk 1)) h2
      simpa [φ] using this
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h3
    simpa using H.inv_mem h3

theorem y4a_exists_not_comm_of_card_six {H : Subgroup (alternatingGroup (Fin 5))}
    (h : Nat.card ↥H = 6) : ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  by_contra hcomm
  push Not at hcomm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 (by rw [h]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 3 (by rw [h]; norm_num)
  have hxy : Commute x y := Subtype.ext (hcomm x x.2 y y.2)
  have hord : orderOf (x * y) = 6 := by
    rw [hxy.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hy]; norm_num), hx, hy]
  have hord' : orderOf ((x * y : ↥H) : alternatingGroup (Fin 5)) = 6 := by
    rw [Subgroup.orderOf_coe, hord]
  rcases y4aA5Index_pow_six _ (by rw [← hord']; exact pow_orderOf_eq_one _) with h2 | h3
  · have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hord'] at hd
    norm_num at hd
  · have hd := orderOf_dvd_of_pow_eq_one h3
    rw [hord'] at hd
    norm_num at hd

end CFSG.EvenSporadicStandard.HNRecog.Section3

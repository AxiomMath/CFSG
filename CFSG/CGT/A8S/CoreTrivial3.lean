module

public import CFSG.CGT.A8S.Components3
public import CFSG.CGT.A8S.HoltA9

public section

namespace CFSG.CGT.A8S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General CFSG.CGT.M24S

section Elementary

variable {G : Type} [Group G]

private theorem eq_one_of_sq_eq_one_of_odd' {x : G} (h2 : x ^ 2 = 1) (hodd : Odd (orderOf x)) :
    x = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr even_two)

private theorem odd_orderOf_of_mem_oddCoreOf' [Finite G] {B : Subgroup G} {g : G}
    (hg : g ∈ oddCoreOf B) : Odd (orderOf g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (oddCoreOf B)) := by
    rw [oddCoreOf, Subgroup.card_map_of_injective B.subtype_injective]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := B))
  exact hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hg)

end Elementary

theorem coreStatementA8_of_holt (hHolt : CFSG.Holt.H78.HoltTheorem1) : CoreStatementA8 := by
  intro G _ _ _ _ T H h
  have hL := h.localFacts3
  obtain ⟨S, hTS, -, z, hzT, hz1, hZ⟩ := hL.sylow
  by_cases hM : componentStab T = ⊤
  · left
    have hMK := componentStab_le_normalizer_oddCore3 h hL
    rw [hM, top_le_iff, Subgroup.normalizer_eq_top_iff] at hMK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (oddCoreOf (Subgroup.centralizer (T : Set G))) with hK | hK
    · rw [hL.centralizer_T_eq, hK, sup_bot_eq]
    · exfalso
      have hzK : z ∈ oddCoreOf (Subgroup.centralizer (T : Set G)) := hK ▸ Subgroup.mem_top z
      exact hz1 (eq_one_of_sq_eq_one_of_odd' (h.wc.1.2 z hzT) (odd_orderOf_of_mem_oddCoreOf' hzK))
  · right
    have hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s := fun s hs =>
      ((hZ z (hTS hzT)).mpr (Or.inr rfl) s hs).symm
    have hTrip := isHoltTriple_componentStab3 h hL (hTS hzT) hzT hz1 hSz
    exact (holtA9Statement_of_holt hHolt G (componentStab T) hM S z (hL.card_sylow S) hZ
      hTrip).2

end CFSG.CGT.A8S

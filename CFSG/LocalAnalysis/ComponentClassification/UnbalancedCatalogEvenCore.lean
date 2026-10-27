module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

variable {G : Type*} [Group G]

theorem le_oddCore_of_normal {N : Subgroup G} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ CFSG.oddCore G :=
  le_sSup ⟨hN, hodd⟩

theorem odd_card_oddCore [Finite G] : Odd (Nat.card (CFSG.oddCore G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem not_mem_oddCore_of_orderOf_eq_two [Finite G] {x : G} (hx : orderOf x = 2) :
    x ∉ CFSG.oddCore G := fun hmem => by
  have h2 : 2 ∣ Nat.card (CFSG.oddCore G) := hx ▸ Subgroup.orderOf_dvd_natCard _ hmem
  exact (Nat.not_even_iff_odd.mpr odd_card_oddCore) (even_iff_two_dvd.mpr h2)

theorem not_mem_oddCore_of_sq_eq_one [Finite G] {x : G} (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    x ∉ CFSG.oddCore G :=
  not_mem_oddCore_of_orderOf_eq_two (orderOf_eq_prime hx2 hx1)

theorem oddCore_eq_bot_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H)
    (hG : CFSG.oddCore G = ⊥) : CFSG.oddCore H = ⊥ := by
  refine sSup_eq_bot.mpr fun N hN => ?_
  have hc : Nat.card (N.comap e.toMonoidHom) = Nat.card N :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  have hle : N.comap e.toMonoidHom ≤ CFSG.oddCore G :=
    le_oddCore_of_normal (hN.1.comap _) (hc ▸ hN.2)
  rw [hG, le_bot_iff] at hle
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N, hle,
    Subgroup.map_bot]

theorem oddCore_eq_bot_of_isSimpleGroup [Finite G] [IsSimpleGroup G] (heven : Even (Nat.card G)) :
    CFSG.oddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
  · exact h
  · have hodd := odd_card_oddCore (G := G)
    rw [h, Subgroup.card_top] at hodd
    exact absurd heven (Nat.not_even_iff_odd.mpr hodd)

theorem map_eq_one_of_commutator_eq_top {P S : Type*} [Group P] [Group S] [Group.IsSolvable S]
    (hP : commutator P = ⊤) (φ : P →* S) (x : P) : φ x = 1 := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := S)
  have hder : ∀ m, derivedSeries P m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero P
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hP]
  have hx : φ x ∈ (derivedSeries P n).map φ := ⟨x, by rw [hder]; trivial, rfl⟩
  have := map_derivedSeries_le_derivedSeries φ n hx
  rwa [hn, Subgroup.mem_bot] at this

end CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

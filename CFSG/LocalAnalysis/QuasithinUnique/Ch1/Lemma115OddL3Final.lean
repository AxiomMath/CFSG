module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem oddDegreeThreeCentralizers : OddDegreeThreeCentralizers := by
  intro K _ _ p hp hp5 hm t ht1 ht2 hC
  have : Fact p.Prime := ⟨hp⟩
  have hs1 : ∀ {X : Type} [Group X] (e : K ≃* X), e t ≠ 1 := fun e h =>
    ht1 (e.injective (by rw [h, map_one]))
  have hs2 : ∀ {X : Type} [Group X] (e : K ≃* X), e t * e t = 1 := fun e => by
    rw [← map_mul, ht2, map_one]
  rcases hm with hm | hm
  · obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hcard])
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP (by omega)
    have h4 : 4 ≤ Nat.card F := by
      rw [hcard, pow_one]
      omega
    have hCX : CharTwo (Subgroup.centralizer ({e t} : Set (StatedProj (StatedSL 3 F)))) := by
      have := charTwo_map_mulEquiv e hC
      rwa [map_centralizer_singleton] at this
    exact not_charTwo_centralizer_statedSL3 h2 h4 (hs2 e) (hs1 e) hCX
  · obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
    have hCX : CharTwo (Subgroup.centralizer
        ({e t} : Set (StatedProj (StatedSU 3 (p ^ 1) F)))) := by
      have := charTwo_map_mulEquiv e hC
      rwa [map_centralizer_singleton] at this
    exact not_charTwo_centralizer_statedSU3 hp hp5 hcard (hs2 e) (hs1 e) hCX

theorem oddInvolutionCentralizers : OddInvolutionCentralizers :=
  oddInvolutionCentralizers_of oddDegreeThreeCentralizers

end CFSG.QuasithinUnique.Ch1

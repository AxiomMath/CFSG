module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Arms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Blueprint.NativeSporadic



theorem sporadic_order_table : ∀ s : TauCeti.SporadicName,
    44352000 ∣ CFSG.AGLEmbedding.sporOrd s → ¬ 3 ^ 5 ∣ CFSG.AGLEmbedding.sporOrd s → s = .HS := by
  decide +kernel

theorem kgHS3_sporadic {S : Type} [Group S] [Finite S] (hS : SporadicRep S)
    (h3 : (Nat.card S).factorization 3 ≤ 4) (K : Subgroup S) (hK : HSType ↥K) : K = ⊤ := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  have hcard : Nat.card S = CFSG.AGLEmbedding.sporOrd s :=
    (Nat.card_congr e.toEquiv).trans
      ((card_carrier_eq_sporOrder_all s).trans (sporOrder_eq_sporOrd s))
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hdvd : 44352000 ∣ CFSG.AGLEmbedding.sporOrd s := hcard ▸ hK.dvd_card
  have hn3 : ¬ 3 ^ 5 ∣ CFSG.AGLEmbedding.sporOrd s := by
    intro h
    rw [← hcard] at h
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos.ne').mp h
    omega
  have hs : s = .HS := sporadic_order_table s hdvd hn3
  subst hs
  have h1 : Nat.card S = 44352000 := hcard.trans (by decide)
  have hK1 : 44352000 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hK.dvd_card_self
  exact Subgroup.eq_top_of_card_eq K (le_antisymm (Subgroup.card_le_card_group K) (h1 ▸ hK1))

end CFSG.ComponentClassification.CatFC.KGHS3

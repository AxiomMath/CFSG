
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Type

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L238

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_isAltQuotient {X T L K J : Subgroup G} (hX : CharTwo X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hL : IsBlock2 X L)
    (hUV : blockU L ≤ VZ T X) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (halt : IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m) (hKL : K ≤ L)
    (hK2 : ¬ IsPGroup 2 K) (hJT : J ≤ T) (hKJ : ⁅K, J⁆ ≤ L) :
    J ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨α, hαs, hαk⟩ := L246.exists_alt_pCore hX hT hL hUV halt
  have hcard := L246.card_quotient_pCore_of_alt α hαs hαk
  by_cases h3 : m = 3
  · subst h3
    have hK0 : K ≠ ⊥ := fun h => hK2 (by rw [h]; exact isPGroup_two_bot)
    refine le_normalizer_of_commutator_le_alt3 hX hL (L246.isAltType_three hL.1 ?_) hKL hK0
      (hJT.trans hT.1) hKJ
    rw [hcard, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · have hm5 : 5 ≤ m := by
      obtain ⟨k, rfl⟩ := hm
      omega
    have hLc : L ∈ cComp X := by
      refine mem_cComp_of_isBlock2 hL ?_
      intro h
      have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [hcard, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h
      have h5 : Nat.factorial 5 = 120 := by decide
      have h120 : Nat.factorial 5 ≤ Nat.factorial m := Nat.factorial_le hm5
      omega
    exact le_normalizer_of_commutator_le h38 hT hLc hKL hK2 hJT hKJ

end L238

end CFSG.QuasithinUnique

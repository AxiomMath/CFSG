module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaPU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_of_l34 (hI : KFactL34Inner) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K) :
    Group.IsSolvable (X₀ ⊓ K : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hd he
  have hcardK : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hX₀ := hK.eq_normalizer_of_l34 hI hd he hAK
  have hAc : Nat.card (A.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hK.card_A, hcardK,
      factorization_20160_three]
  let T : Sylow 3 K := Sylow.ofCard (A.subgroupOf K) hAc
  have hT : (T : Subgroup K) = A.subgroupOf K := rfl
  have hloc := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T
  have hT9 : Nat.card (T : Subgroup K) = 9 :=
    KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hL T
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ (T : Subgroup K), t ≠ 1 := by
    by_contra hcon
    have hbot : (T : Subgroup K) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr fun t ht => by_contra fun h => hcon ⟨t, ht, h⟩
    rw [hbot, Subgroup.card_bot] at hT9
    omega
  have hC : Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ T := fun g hg =>
    hloc.centralizer_le t ht ht1 g (Subgroup.mem_centralizer_iff.mp hg t ht).symm
  have hsolvN : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup K) : Set K)) :=
    isSolvable_normalizer_of_card_eq_nine_of_le hT9 hC
  have hXK : X₀.subgroupOf K = Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hAK, ← hX₀]
  exact isSolvable_inf_of_subgroupOf (hXK ▸ hsolvN)

end CFSG.LocalAnalysis.RankThreeTheoremC

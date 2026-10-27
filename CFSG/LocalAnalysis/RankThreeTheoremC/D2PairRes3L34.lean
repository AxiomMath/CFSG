module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3Auto
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaPU
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem exists_mem_normalizer_not_normalizer_of_isLinThreeFour {K : Type} [Group K] [Finite K]
    (hK : IsLinThreeFour K) {T Y : Subgroup K} (hT : Nat.card T = 9) (hYT : Y ≤ T)
    (hY : Nat.card Y = 3) :
    ∃ n ∈ Subgroup.normalizer (T : Set K), n ∉ Subgroup.normalizer (Y : Set K) := by
  obtain ⟨ε⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := KFactProofs.UPrimeExcL34.card_galoisField_two_two
  have hTc : Nat.card (T.map ε.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε.injective, hT]
  have hYc : Nat.card (Y.map ε.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective ε.injective, hY]
  obtain ⟨n, hn, x, hx, hnx⟩ :=
    CFSG.RankThree.PartTwo.KFacts.L34.exists_mem_normalizer_conj_not_mem hk hTc
      (Subgroup.map_mono hYT) hYc
  refine ⟨ε.symm n, ?_, fun hnY => hnx ?_⟩
  · have := (Subgroup.map_equiv_normalizer_eq T ε).symm
    rw [this] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    have : m = ε.symm n := by rw [← hmn]; simp
    exact this ▸ hm
  · have hxY : ε.symm x ∈ Y := by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    have h1 := (Subgroup.mem_normalizer_iff.mp hnY (ε.symm x)).mp hxY
    have h2 : ε (ε.symm n * ε.symm x * (ε.symm n)⁻¹) ∈ Y.map ε.toMonoidHom := ⟨_, h1, rfl⟩
    simpa using h2

theorem automizerIrreducible_of_l34 (hI : KFactL34Inner) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K)
    (hR9 : Nat.card (R : Subgroup X) = 9) :
    AutomizerIrreducible 3 (R : Subgroup X) X₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRA : (R : Subgroup X) = A :=
    (Subgroup.eq_of_le_of_card_ge hK.A_le (by rw [hR9, hK.card_A]; norm_num)).symm
  have hX₀ := hK.eq_normalizer_of_l34 hI hd he hAK
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hd he
  intro Y hYR hY3
  have hYA : Y ≤ A := hRA ▸ hYR
  have hYK : Y ≤ K := hYA.trans hAK
  have hTc : Nat.card (A.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hK.card_A]
    norm_num
  have hYc : Nat.card (Y.subgroupOf K) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv, hY3]
  obtain ⟨n, hn, hnY⟩ := exists_mem_normalizer_not_normalizer_of_isLinThreeFour hL hTc
    (Subgroup.subgroupOf_mono K hYA) hYc
  rw [← Subgroup.subgroupOf_normalizer_eq hAK] at hn
  refine ⟨(n : X), ⟨hX₀ ▸ Subgroup.mem_subgroupOf.mp hn, ?_⟩, fun hY' => hnY ?_⟩
  · rw [hRA]
    exact Subgroup.mem_subgroupOf.mp hn
  · rw [← Subgroup.subgroupOf_normalizer_eq hYK]
    exact hY'

end CFSG.LocalAnalysis.RankThreeTheoremC

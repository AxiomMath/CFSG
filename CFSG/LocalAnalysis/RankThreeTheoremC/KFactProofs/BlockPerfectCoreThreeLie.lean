module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusVoid
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoVoid
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsThreeDvd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock

theorem three_dvd_of_mem_linBlockOrders {K : Type} {f : ℕ} (hK : Nat.card K = 2 ^ f) {N : ℕ}
    (hN : N ∈ linBlockOrders K) : 3 ∣ N := by
  obtain ⟨m, hm, rfl⟩ := hN
  rw [hK]
  exact three_dvd_ordA (by omega)

theorem three_dvd_of_mem_uniBlockOrders {f s ε N : ℕ} (hN : N ∈ uniBlockOrders f s ε)
    (h1 : 1 < N) : 3 ∣ N := by
  rcases hN with ⟨k, rfl⟩ | rfl
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd h1 (by rw [ordA_zero]; exact lt_irrefl 1)
    · have hq : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
      rw [hq]
      exact three_dvd_ordA hk
  · rcases Nat.eq_zero_or_pos (2 * s + ε - 1) with h0 | hk
    · rw [h0, ordTwistedA_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact three_dvd_ordTwistedA hk

theorem three_dvd_of_mem_spBlockOrders {f N : ℕ} (hN : N ∈ spBlockOrders (2 ^ f))
    (h1 : 1 < N) : 3 ∣ N := by
  rcases hN with ⟨k, rfl⟩ | ⟨m, rfl⟩ | rfl
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd h1 (by rw [ordA_zero]; exact lt_irrefl 1)
    · exact three_dvd_ordA hk
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd h1 (not_lt.2 (ordBC_zero_le _))
    · exact three_dvd_ordBC hm
  · norm_num

theorem three_dvd_of_mem_plusBlockOrders {K : Type} {f : ℕ} (hK : Nat.card K = 2 ^ f) {N : ℕ}
    (hN : N ∈ plusBlockOrders (Nat.card K)) : 3 ∣ N := by
  rw [hK] at hN
  rcases hN with ⟨k, hk, rfl⟩ | ⟨m, hm, rfl⟩
  · exact three_dvd_ordA (by omega)
  · exact three_dvd_ordD (by omega)

theorem three_dvd_of_mem_orthMinusBlockOrders {f N : ℕ} (hN : N ∈ orthMinusBlockOrders (2 ^ f)) :
    3 ∣ N := by
  rcases hN with ⟨k, hk, rfl⟩ | ⟨m, hm, rfl⟩
  · exact three_dvd_ordA (by omega)
  · exact three_dvd_ordTwistedD hm

theorem kFactCompParabPerfectCoreThreeOn_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabPerfectCoreThreeOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, -, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact perfectCoreThree_of_cover hCP.parab.1 ρ hρs hQ fun N hN _ =>
    three_dvd_of_mem_linBlockOrders hK hN

theorem kFactCompParabPerfectCoreThreeOn_twistedA :
    KFactCompParabPerfectCoreThreeOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, -, hρ, -, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d hd e
  have : Finite K := h.finite
  exact perfectCoreThree_of_cover hCP.parab.1 ρ hρ (hasLeviBlocks_hypStab h hε hI g hJ)
    fun N hN h1 => three_dvd_of_mem_uniBlockOrders hN h1

theorem exists_hasLeviBlocks_spBlockOrders_of_idxB (hZ : OddCenterRest) {Y : Type} [Group Y]
    [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hB : IsLieOf IdxB (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (f : ℕ),
      Function.Surjective ρ ∧
        HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (spBlockOrders (2 ^ f)) := by
  obtain ⟨r, K, _, _, _, -, ⟨φ⟩⟩ := exists_mulEquiv_statedSp_of_idxB hZ hCP.comp hCP.odd hB
  obtain ⟨ρ, I, t, hI, htI, hmax, hρ⟩ := exists_flagStabilizer_of_compParab hCP φ
  obtain ⟨f, -, hq⟩ := spFlag_card_eq_two_pow (K := K)
  refine ⟨_, inferInstance, inferInstance, ρ.toMonoidHom, f, ρ.surjective, ?_⟩
  rw [hρ, ← hq]
  exact hasLeviBlocks_spFlag hI htI hmax

theorem kFactCompParabPerfectCoreThreeOn_idxB (hZ : OddCenterRest) :
    KFactCompParabPerfectCoreThreeOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := exists_hasLeviBlocks_spBlockOrders_of_idxB hZ hCP hB
  exact perfectCoreThree_of_cover hCP.parab.1 ρ hρ hQ fun N hN h1 =>
    three_dvd_of_mem_spBlockOrders hN h1

theorem kFactCompParabPerfectCoreThreeOn_idxD (hZ : OddCenterRest) :
    KFactCompParabPerfectCoreThreeOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, -, hQ, -⟩ := exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : Finite ↥(LocalAnalysis.ComponentInitial.orthElementaryGroup
      (LieType.Universal.Spin.quadPlus r K)) := Finite.of_equiv _ ρ.symm.toEquiv
  exact perfectCoreThree_of_cover hCP.parab.1 ρ.toMonoidHom ρ.surjective hQ fun N hN _ =>
    three_dvd_of_mem_plusBlockOrders hK hN

theorem kFactCompParabPerfectCoreThreeOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabPerfectCoreThreeOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP ⟨dI, hdI, ⟨e⟩⟩
  obtain ⟨K, _, _, ρ, f, hρ, hQ, -⟩ := exists_hasLeviBlocks_of_twistedD hZ hCP dI hdI e
  exact perfectCoreThree_of_cover hCP.parab.1 ρ hρ hQ fun N hN _ =>
    three_dvd_of_mem_orthMinusBlockOrders hN

theorem kFactCompParabPerfectCoreThreeOn_g2
    (hGA : GriessAllModelsStatement) : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := hasLeviBlocks_g2 hGA hCP hG
  exact perfectCoreThree_of_cover hCP.parab.1 ρ hρ hQ (by
    rintro n rfl -
    exact three_dvd_ordA (by norm_num))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

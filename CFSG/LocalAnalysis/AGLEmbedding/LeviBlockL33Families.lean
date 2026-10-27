module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Section
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Orders
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSmall
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeLie
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusTypes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

theorem kFactCompParabNoL33U35L37HeOn_linear
    (hGA : GriessAllModelsStatement) :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA
  obtain ⟨n, f, ρ, -, I, hn, hf, hρs, -, -, -, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) (linBlockOrders (GaloisField 2 f)) :=
    hcomap ▸ hasLeviBlocks_flagStabilizer (by omega) I
  exact noL33U35L37HeAt_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ, _,
    hρs, hQ, LeviBlock.not_isL33U35L37HeOrder_of_mem_linBlockOrders hf⟩

theorem kFactCompParabNoL33U35L37HeOn_twistedA :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxTwistedA) := by
  intro Y _ _ L P hCP hC
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hJ⟩ :=
    exists_uniFlag_of_compParab hCP d hd e
  have : Finite K := h.finite
  exact noL33U35L37HeAt_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ,
    uniBlockOrders f s ε, hρ, hasLeviBlocks_hypStab h hε hI g hJ,
    LeviBlock.not_isL33U35L37HeOrder_of_mem_uniBlockOrders f s ε⟩

theorem kFactCompParabNoL33U35L37HeOn_idxB (hZ : OddCenterRest) :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxB) := by
  intro Y _ _ L P hCP hB
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ :=
    LocalAnalysis.RankThreeTheoremC.KFactProofs.exists_hasLeviBlocks_spBlockOrders_of_idxB hZ
      hCP hB
  exact noL33U35L37HeAt_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ,
    LeviBlock.spBlockOrders (2 ^ f), hρ, hQ,
    LeviBlock.not_isL33U35L37HeOrder_of_mem_spBlockOrders rfl⟩

theorem kFactCompParabNoL33U35L37HeOn_idxD (hZ : OddCenterRest) :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨r, K, _, _, _, ρ, -, hQ, -⟩ := LeviBlock.exists_hasLeviBlocks_of_idxD hZ hCP hD
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact noL33U35L37HeAt_of_levi hCP.parab.1 ⟨_, inferInstance,
    Finite.of_equiv _ ρ.symm.toEquiv, ρ.toMonoidHom, plusBlockOrders (Nat.card K),
    ρ.surjective, hQ,
    LeviBlock.not_isL33U35L37HeOrder_of_mem_plusBlockOrders (q := Nat.card K) (f := n)
      (by rw [Nat.card_eq_fintype_card, hn])⟩

theorem kFactCompParabNoL33U35L37HeOn_twistedD (hZ : OddCenterRest) :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxTwistedD) := by
  intro Y _ _ L P hCP hD
  obtain ⟨dI, hdI, ⟨e⟩⟩ := hD
  obtain ⟨K, _, _, ρ, f, hρ, hQ, -⟩ :=
    LeviBlock.exists_hasLeviBlocks_of_twistedD hZ hCP dI hdI e
  exact noL33U35L37HeAt_of_levi hCP.parab.1 ⟨K, inferInstance, inferInstance, ρ,
    orthMinusBlockOrders (2 ^ f), hρ, hQ,
    LeviBlock.not_isL33U35L37HeOrder_of_mem_orthMinusBlockOrders⟩

theorem kFactCompParabNoL33U35L37HeOn_g2
    (hGA : GriessAllModelsStatement) :
    KFactCompParabNoL33U35L37HeOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG
  obtain ⟨K, _, _, ρ, f, hρ, hQ⟩ := hasLeviBlocks_g2 hGA hCP hG
  refine noL33U35L37HeAt_of_levi hCP.parab.1 ⟨_, inferInstance, inferInstance, ρ,
    {ordA 1 (2 ^ f)}, hρ, hQ, ?_⟩
  intro n hn
  rw [Set.mem_singleton_iff] at hn
  subst hn
  exact LeviBlock.ordA_not_isL33U35L37HeOrder (n := 1) (f := f) rfl

theorem kFactCompParabNoL33U35L37He_small : KFactCompParabNoL33U35L37HeOn IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS O W hOP hPO hO3 hWP hPWO _ U _ _ _ ψ hψ hU
  exfalso
  have h2 : 2 ∣ Nat.card U := by
    rcases hU with h | h | h | h <;> rw [h] <;> norm_num
  have h1 := LeviBlock.card_dvd_card_centerQuotient (hWP.trans hCP.parab.1) hCP.odd h2 ψ hψ
  rcases LeviBlock.card_small_cases hS with h | h | h | h | h
  all_goals rw [h] at h1
  all_goals rcases hU with hU | hU | hU | hU <;> rw [hU] at h1 <;> norm_num at h1

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Module
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Quasithin.Background.B15P4LayerDict

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

theorem K534_holds : K534 := by
  intro X _ _ T hX Ls hL hJ h3
  have hC : CharTwo (⊤ : Subgroup X) := hX.charTwo
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  obtain ⟨A, hA, hAN, hLA⟩ := exists_offender_of_le hV hVT Ls hL hJ
  obtain ⟨hq, hZ, ⟨e6⟩⟩ := h3
  set ρ := gnRep hV with hρ
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hA2 := isElementaryAbelian_map_mk hA
  have hfaith : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ hfaith).mp ⟨hA2, isBestOffender_gnRep_of_le hV hVT hA⟩
  have hfin := K534Proof.q3a6_finrank_commOn ρ hinj hq hZ e6 hA2 hAN hLA hb
  have hUs := subOf_commOn hV Ls
  change Nat.card ↥⁅gnV T, Ls.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6
  rw [← hUs, card_subOf, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hfin]

end CFSG.LocalAnalysis.RankThreeUC.S15

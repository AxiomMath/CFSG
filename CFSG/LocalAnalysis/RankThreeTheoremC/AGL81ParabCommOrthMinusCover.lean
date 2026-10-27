module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpCover
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.Assembly.LowTwoRank

theorem exists_mulEquiv_orthElementary_of_isQuasisimple_idxTwistedD
    (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxTwistedD (↥Y ⧸ Subgroup.center ↥Y)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (b c : K), 3 ≤ r ∧
      (∀ t : K, t ^ 2 + b * t + c ≠ 0) ∧
      Nonempty (↥Y ≃* ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    Sp.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  have hL : IsComponentOf (⊤ : Subgroup ↥Y) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hY
  let eT : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup ↥Y)).map eT.toMonoidHom = Subgroup.center ↥Y :=
    Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup ↥Y)) = Nat.card (Subgroup.center ↥Y) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup ↥Y) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥Y) ≃*
      ↥Y ⧸ Subgroup.center ↥Y := QuotientGroup.congr _ _ eT hcT
  obtain ⟨d, hd, ⟨e⟩⟩ := hF
  obtain ⟨r, K, hf, hfin, hK, b, c, hr, hirr, -, ⟨φ⟩⟩ :=
    exists_mulEquiv_orthElementary_of_twistedD (oddCenterRest_of_griess hGA) hL (hcard ▸ hodd) d hd
      (eQ.trans e)
  exact ⟨r, K, hf, hfin, hK, b, c, hr, hirr, ⟨eT.symm.trans φ⟩⟩

structure OmCover {A : Type} [Group A] (Y P : Subgroup A) (r : ℕ) (K : Type) [Field K] (b c : K)
    {s : ℕ} (d : Fin (s + 1) → ℕ) where
  ρ : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))) ≃* ↥Y
  comap_eq : (P.subgroupOf Y).comap ρ.toMonoidHom = orthParab r (minusTailForm K b c) d

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

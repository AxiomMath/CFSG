module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphAltEightLevi
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

theorem exists_levi_equiv {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hA8 : Nonempty (↥Y ⧸ Subgroup.center ↥Y ≃* alternatingGroup (Fin 8)))
    (hP : IsParabolicTwo Y P) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (a : Fin 4 → ℕ), Nat.card K = 2 ∧
      (∑ i, a i) ≤ 4 ∧
      Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃* ∀ i, Matrix.GeneralLinearGroup (Fin (a i)) K) := by
  classical
  obtain ⟨eA⟩ := hA8
  have hodd : Odd (Nat.card (center ↥Y)) := ParabCensus.odd_card_center_of_pCoreOf_eq_bot hO
  have hZ : center ↥Y = ⊥ := ToralCensus.center_eq_bot_of_mulEquiv_alt_eight hY hodd eA
  obtain ⟨e8⟩ := ToralCensus.nonempty_alt_eight_mulEquiv_projectiveSL
  obtain ⟨ρ, hρ⟩ := ToralCensus.exists_compat_of_center_eq_bot hZ (eA.trans e8)
  obtain ⟨hρs, -⟩ := ToralCensus.surjective_and_ker_le_of_compat hY.1 (eA.trans e8) ρ hρ
  obtain ⟨σ, e', I, hσs, hσ, -, hcomap, -, -⟩ :=
    exists_comap_eq_flagStabilizer hodd (n := 4) (by norm_num) (eA.trans e8) hρs hρ hP
  obtain ⟨-, hσk⟩ := ToralCensus.surjective_and_ker_le_of_compat hY.1 e' σ hσ
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    refine hσk.trans ?_
    rw [CFSG.LargeExtraspecial.A2Mod.sl_center_eq_bot_of_card_two hK]
  let eσ : ↥((P.subgroupOf Y).comap σ) ≃* ↥(P.subgroupOf Y) :=
    MulEquiv.ofBijective (σ.subgroupComap (P.subgroupOf Y))
      ⟨σ.subgroupComap_injective _ hσinj, σ.subgroupComap_surjective _ hσs⟩
  let φ : ↥(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.flagStabilizer 4 (GaloisField 2 1) I)
      ≃* ↥P :=
    ((MulEquiv.subgroupCongr hcomap.symm).trans eσ).trans (Subgroup.subgroupOfEquivOfLe hP.1)
  obtain ⟨e⟩ := nonempty_quotient_pCore_flagStabilizer_linLevi hK (n := 4) (by norm_num) I
  obtain ⟨e2⟩ := ParabCensus.nonempty_quotient_pCore_of_mulEquiv φ
  exact ⟨GaloisField 2 1, inferInstance, inferInstance, LeviBlock.linBlockLen 4 I, hK,
    sum_linBlockLen_le 4 I, ⟨e2.symm.trans e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

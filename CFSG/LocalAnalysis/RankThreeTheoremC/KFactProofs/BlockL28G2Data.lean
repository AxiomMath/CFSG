module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LieType.Chevalley.PerfectSimpleRoot
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem gtwo_exists_cover
    (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hCP : CompParab L P) (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (f : ℕ) (π : ↥(adjointGroup .G2 (GaloisField 2 f)) →* ↥L), Function.Surjective π ∧
      Function.Injective π ∧ HasLeviBlocks ↥((P.subgroupOf L).comap π) {ordA 1 (2 ^ f)} := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP hG
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  have : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) := eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  obtain ⟨G, _, _, S, β, hker, hpi, hcomm, ⟨eS⟩⟩ :=
    exists_leviData_of_negIndices_eq hQ hBA hI (rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc)
  obtain ⟨hqs, hZ, hcard⟩ := sl2Block_facts h4 (eL.trans eS)
  refine ⟨f, π', hQ.surj, ?_, 1, fun _ => G, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => S, β, hker, hpi, hcomm, fun _ => Or.inl hqs, fun _ _ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro z hz
    have hc := hQ.ker_central z hz
    rwa [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
  · rw [Set.mem_singleton_iff, card_quotient_center_of_eq_bot hZ, hcard, hF,
      ordA_one_eq_two_pow (by omega)]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

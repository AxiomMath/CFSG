module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.Sporadic.Bridge.Y322Central
import CFSG.YGroups.Y443.Tri.Finiteness
import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.Open.MonsterDefs
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Monster.Generated
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem d2FreeCaseAt_M_of_datumPlus
    {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      Nonempty (L ≃* NativeSporadic.Carrier .M) → ∀ p, p.Prime → p ≠ 2 → Pp p →
        D2IndexDatumPlus L p) :
    D2FreeCaseAt (.sporadic .M) Pp := by
  intro X _ _ p hpc R A X₀ K hK ⟨e⟩
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
  have : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  exact hK.false_of_datumPlus (h K ⟨e.trans f.symm⟩ p hK.prime hK.ne_two hpc)

section Rows

theorem d2IndexDatum_M_seven (h7 : 3 ≤ Open.pRank 7 (⊤ : Subgroup Gmat)) {L : Type} [Group L]
    [Finite L] [IsSimpleGroup L] (e : L ≃* NativeSporadic.Carrier .M) : D2IndexDatum L 7 := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  refine ⟨?_, Or.inr (Or.inl ?_)⟩
  · rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
    norm_num
  · have := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 7 (by norm_num)
      ε.symm.toMonoidHom ε.symm.injective (⊤ : Subgroup Gmat)
    rw [Subgroup.map_top_of_surjective _ ε.symm.surjective] at this
    rw [this]
    exact h7

theorem d2IndexDatum_M_eleven (h11 : FusionGenerationOf Gmat 11) {L : Type} [Group L]
    [Finite L] [IsSimpleGroup L] (e : L ≃* NativeSporadic.Carrier .M) : D2IndexDatum L 11 := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨?_, fusionGenerationOf_of_mulEquiv ε.symm h11⟩))⟩
  · rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
    norm_num
  · rw [Nat.card_congr ε.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    norm_num [CFSG.Open.monsterOrder]

theorem d2IndexDatumPlus_M_thirteen
    (h13 : ∀ S : Sylow 13 Gmat, ∀ A : Subgroup Gmat, A ≤ (S : Subgroup Gmat) →
      IsElemAbelian 13 A → Nat.card A = 13 ^ 2 →
        GLBCore 13 2 (S : Subgroup Gmat) ⊔ GLBCore 13 1 A = ⊤)
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* NativeSporadic.Carrier .M) :
    D2IndexDatumPlus L 13 := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  refine Or.inr (D2IndexDatumSup.of_mulEquiv (by norm_num) ε ⟨?_, h13⟩)
  rw [← CFSG.RankThree.PartOne.card_outer_eq_of_mulEquiv ε,
    CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
  norm_num

theorem d2IndexCaseAt_M_rows_of_Gmat (h7 : 3 ≤ Open.pRank 7 (⊤ : Subgroup Gmat))
    (h11 : FusionGenerationOf Gmat 11)
    (h13 : ∀ S : Sylow 13 Gmat, ∀ A : Subgroup Gmat, A ≤ (S : Subgroup Gmat) →
      IsElemAbelian 13 A → Nat.card A = 13 ^ 2 →
        GLBCore 13 2 (S : Subgroup Gmat) ⊔ GLBCore 13 1 A = ⊤) :
    D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13 :=
  (d2FreeCaseAt_M_of_datumPlus fun _ _ _ _ ⟨e⟩ p _ _ hp => by
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (d2IndexDatum_M_seven h7 e)
    · exact Or.inl (d2IndexDatum_M_eleven h11 e)
    · exact d2IndexDatumPlus_M_thirteen h13 e).indexCaseAt

end Rows

end CFSG.AGLEmbeddingD2

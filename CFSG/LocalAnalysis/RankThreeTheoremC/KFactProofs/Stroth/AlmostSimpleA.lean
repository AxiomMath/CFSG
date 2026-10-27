module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOutTower

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG Subgroup in
theorem pClosed_of_outTower {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {L : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hT : CFSG.AGLEmbedding.OutTowerAt ↥L p) :
    ∀ P : Sylow p (X ⧸ L), (P : Subgroup (X ⧸ L)).Normal := by
  intro P
  have hq : Function.Surjective (QuotientGroup.mk' L) := QuotientGroup.mk'_surjective L
  obtain ⟨R, hR⟩ := Sylow.mapSurjective_surjective hq p P
  have hN : (L ⊔ (R : Subgroup X)).Normal :=
    CFSG.AGLEmbedding.sup_sylow_normal_of_outTower hC hT R
  have hLbot : L.map (QuotientGroup.mk' L) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff x).2 hx
  have hPeq : (P : Subgroup (X ⧸ L)) = (L ⊔ (R : Subgroup X)).map (QuotientGroup.mk' L) := by
    rw [← hR, Sylow.coe_mapSurjective, Subgroup.map_sup, hLbot, bot_sup_eq]
  rw [hPeq]
  exact hN.map (QuotientGroup.mk' L) hq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

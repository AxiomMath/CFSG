module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeUC.S15

section Join

variable {X : Type} [Group X]

@[expose] def threeNormalizerJoin (T L : Subgroup X) : Subgroup X :=
  ⨆ (B : Subgroup X) (_ : B ≤ T) (_ : B ≠ ⊥) (_ : (B.subgroupOf T).Characteristic)
    (_ : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (B : Set X))), L ⊓ Subgroup.normalizer (B : Set X)

theorem threeNormalizerJoin_le (T L : Subgroup X) : threeNormalizerJoin T L ≤ L :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    inf_le_left

theorem inf_normalizer_le_threeNormalizerJoin {T L B : Subgroup X} (hBT : B ≤ T) (hB : B ≠ ⊥)
    (hc : (B.subgroupOf T).Characteristic)
    (h3 : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (B : Set X))) :
    L ⊓ Subgroup.normalizer (B : Set X) ≤ threeNormalizerJoin T L :=
  le_iSup_of_le B (le_iSup_of_le hBT (le_iSup_of_le hB (le_iSup_of_le hc (le_iSup_of_le h3 le_rfl))))

end Join

@[expose] def AGL81FiveTwentySixAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T L : Subgroup X), GNSetting X T → IsC2 L →
    ∀ C₁ C₂ : Subgroup X, CFSG.Quasithin.IsC118Pair T C₁ C₂ →
      GNYComponent T C₁ C₂ (L.map (toStar T)) → ∀ n : ℕ, (n = 7 ∨ 8 < n) →
        Nonempty (↥(L.map (toStar T)) ≃* alternatingGroup (Fin n)) →
          L ≤ threeNormalizerJoin T L

end CFSG.LocalAnalysis.RankThreeTheoremC

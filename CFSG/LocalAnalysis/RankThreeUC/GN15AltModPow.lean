module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltTop
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModCover

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

@[expose] def GNLayerHolds : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ∀ n : ℕ, 9 ≤ n → Odd n → Nonempty (↥L ≃* alternatingGroup (Fin n)) →
        GNNaturalOnLayer T L n

@[expose] def GNBaumNormalizes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ∀ n : ℕ, 9 ≤ n → Odd n → Nonempty (↥L ≃* alternatingGroup (Fin n)) →
        gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T))

@[expose] def GNBlockLift : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ∀ n : ℕ, 9 ≤ n → Odd n → Nonempty (↥L ≃* alternatingGroup (Fin n)) →
        GNNaturalOnLayer T L n → ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H →
          IsBlock2 H Kb → IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False

theorem altOddCoverPow_of_inputs (hlayer : GNLayerHolds) (hM2 : GNBaumNormalizes)
    (hBL : GNBlockLift) : AltOddCoverPow := by
  intro X _ _ T hX _ T₁ T₂ hP Ls hY m hm he
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  have hn9 : 9 ≤ 2 ^ m + 1 := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hZ : Subgroup.center ↥Ls = ⊥ :=
    altOddCentreTrivial ↥Ls hY.1.2.2 (not_two_dvd_card_center hX hY.1) (2 ^ m + 1) hn9 he
  let e : ↥Ls ≃* alternatingGroup (Fin (2 ^ m + 1)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans he.some
  have hl := hlayer X T hX Ls hY.1 hJ (2 ^ m + 1) hn9 hodd ⟨e⟩
  exact false_of_gnYComponent_two_pow_succ hX hP hY hm e hl
    (hM2 X T hX Ls hY.1 hJ (2 ^ m + 1) hn9 hodd ⟨e⟩)
    (hBL X T hX Ls hY.1 hJ (2 ^ m + 1) hn9 hodd ⟨e⟩ hl)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

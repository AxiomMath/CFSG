module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SU3Main
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.Coordinator (TFAbLie LieCentralQuotient)

@[expose] def TFAbClassification : Prop :=
  ∀ (L : Type) [Group L] [Finite L], LieCentralQuotient L → CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsKGroup L → Nat.card (Subgroup.center L) = 3 →
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 → CFSG.Open.GLATwoLocalRank 3 L = 1 →
        ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Odd f ∧ 3 ≤ f ∧
          Nat.card K = (2 ^ f) ^ 2 ∧ Nonempty (L ≃* ↥(StatedSU 3 (2 ^ f) K))

theorem tfabLie_of (hCl : TFAbClassification) (hD : SU3DiagonalRank) : TFAbLie := by
  intro L _ _ hF hq hK hZ hm hw H hH hc
  obtain ⟨f, K, _, _, hfo, hf3, hKc, ⟨e⟩⟩ := hCl L hF hq hK hZ hm hw
  have h : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, by omega, by rw [hKc, ← pow_mul, mul_comm]⟩
  let e' : L ≃* S3 h := e.trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3))
  have : Finite (S3 h) := Finite.of_equiv L e'.toEquiv
  have hZ' : Nat.card (Subgroup.center (S3 h)) = 3 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e').toEquiv]
    exact hZ
  have hm' : CFSG.Open.pRank 3 (⊤ : Subgroup (S3 h)) = 2 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
    exact hm
  have hw' : CFSG.Open.GLATwoLocalRank 3 (S3 h) = 1 := by
    rw [glaTwoLocalRank_congr (by norm_num) e']
    exact hw
  refine fieldBonus_of_mulEquiv (by norm_num) e' H ?_
  exact fieldBonus_su3 h hD hfo hf3 hZ' hm' hw' _ (isElemAbelian_map (MulAut.congr e') hH)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr e').injective]; exact hc)

end CFSG.HardMathSupport.Timmesfeld.FieldBonus

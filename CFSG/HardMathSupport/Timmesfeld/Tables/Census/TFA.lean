module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TableL2
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def TFAaModels : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 → CFSG.Open.GLATwoLocalRank 3 X = 1 →
      ∀ H : Subgroup (MulAut X), CFSG.Open.IsElemAbelian 3 H → Nat.card H = 9 → FieldBonus X 3 H

theorem tfaaLie_of_models (h : TFAaModels) : TFAaLie := by
  intro L _ _ hF hq hK hZ hm hw H hH hcard
  obtain ⟨d, ⟨e⟩⟩ := hF
  have hZ' : Subgroup.center L = ⊥ := Subgroup.card_eq_one.1 hZ
  set e1 : L ≃* (TauCeti.CFSGIndex.lie d).Group := (mulEquivCenterQuotient hZ').symm.trans e
  have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv L e1.toEquiv
  obtain ⟨t, n, p, f, hmod⟩ := Tables.Multiplier.exists_lieModel d
  have hm' : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 1 := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e1]
    exact hm
  have hw' : CFSG.Open.GLATwoLocalRank 3 (TauCeti.CFSGIndex.lie d).Group = 1 := by
    rw [glaTwoLocalRank_congr (by norm_num) e1]
    exact hw
  refine fieldBonus_of_mulEquiv (by norm_num) e1 H
    (h _ t n p f hmod hm' hw' _ (isElemAbelian_map (MulAut.congr e1) hH) ?_)
  rw [Subgroup.card_map_of_injective (MulAut.congr e1).injective]
  exact hcard

end CFSG.HardMathSupport.Timmesfeld.Tables.Census

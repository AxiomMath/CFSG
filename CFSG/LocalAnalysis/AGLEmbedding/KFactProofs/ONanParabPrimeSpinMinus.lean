module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOneRels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.CurtisTits

section Minus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem rankOneNode_spinMinus_long {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    RankOneNode (minusDatum n hirr) k (Nat.card F) := by
  have hq : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  refine rankOneNode_of_equiv_sl2 hq ?_ (Or.inl rfl)
  exact (MulEquiv.subgroupCongr (rankOne_minusRootGroup_of_lt n hirr hk)).trans
    (MonoidHom.ofInjective (SpinFrame.longSL2_injective _ (succ_ne_of_lt n hk) true false)).symm

theorem rankOneNode_spinMinus_short {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    RankOneNode (minusDatum n hirr) k (Nat.card F) := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  exact rankOneNode_of_rankOneRels (shortRels n hirr k) (mem_minusRootGroup_single_iff hirr hk)
    (mem_minusRootGroup_neg_single_iff hirr hk) (shortRels_x_injective hirr k)
    SpinMinusClosed.card_shortField

include hirr in
theorem parabCore_spinMinus (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) (hq4 : 4 ≤ Nat.card F) :
    ParabCore Y (Nat.card F) := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  refine (borelQuotient_spinMinus hirr hn e).parabCore hq4 dvd_rfl fun i => ?_
  by_cases hk : i.val + 1 < n - 1
  · exact rankOneNode_spinMinus_long hirr hk
  · exact rankOneNode_spinMinus_short hirr hk

end Minus

theorem parabCore_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (hf : 2 ≤ f) : ParabCore Y (2 ^ f) := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [← hcard]
  exact parabCore_spinMinus hirr (by omega) e (by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.AGLEmbedding.ParabPrime

module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg

section Plus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem rankOneNode_spinPlus (hn : 3 ≤ n) (i : Fin n) :
    RankOneNode (plusDatum n F hn) i (Nat.card F) := by
  obtain ⟨φ, -, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
  exact rankOneNode_of_sl2 (by have := Finite.one_lt_card (α := F); omega)
    (SpinPlus.isParametrization (K := F) hn) hx hy (Or.inl rfl)

theorem parabCore_spinPlus (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) (hq4 : 4 ≤ Nat.card F) :
    ParabCore Y (Nat.card F) := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact (borelQuotient_spinPlus hn e).parabCore hq4 (sub_one_dvd_sq_sub_one _)
    (rankOneNode_spinPlus hn)

end Plus

theorem parabCore_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (hf : 2 ≤ f) : ParabCore Y (2 ^ f) := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [← hcard]
  exact parabCore_spinPlus (by omega) e (by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.AGLEmbedding.ParabPrime

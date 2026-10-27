module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg

variable {n : ℕ} {F : Type} [Field F]

theorem rankOneNode_sp [Finite F] [CharP F 2] (i : Fin n) :
    RankOneNode (rootDatum n F) i (Nat.card F) := by
  obtain ⟨φ, -, hx, hy⟩ := Sp.rankOne (F := F) i
  exact rankOneNode_of_sl2 (by have := Finite.one_lt_card (α := F); omega) Sp.isParametrization hx
    hy (Or.inl rfl)

theorem parabCore_sp [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSp n F)) (hq4 : 4 ≤ Nat.card F) : ParabCore Y (Nat.card F) :=
  (borelQuotient_sp e).parabCore hq4 (sub_one_dvd_sq_sub_one _) rankOneNode_sp

theorem parabCore_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) (hf : 2 ≤ f) : ParabCore Y (2 ^ f) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  rw [← hcard]
  exact parabCore_sp e (by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.AGLEmbedding.ParabPrime

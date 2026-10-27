module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.Steinberg

variable {m : ℕ} {F : Type} [Field F]

theorem rankOneNode_sl [Finite F] [CharP F 2] (i : Fin m) :
    RankOneNode (rootDatum m F) i (Nat.card F) := by
  obtain ⟨φ, -, hx, hy⟩ := SL.rankOne (F := F) i
  exact rankOneNode_of_sl2 (by have := Finite.one_lt_card (α := F); omega) SL.isParametrization hx
    hy (Or.inl rfl)

theorem parabCore_sl [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) (hq4 : 4 ≤ Nat.card F) :
    ParabCore Y (Nat.card F) :=
  (borelQuotient_sl e).parabCore hq4 (sub_one_dvd_sq_sub_one _) rankOneNode_sl

theorem parabCore_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL n 2 f) (hf : 2 ≤ f) :
    ParabCore Y (2 ^ f) := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hcard]
  exact parabCore_sl
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans
      e.symm) (by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)

end CFSG.AGLEmbedding.ParabPrime

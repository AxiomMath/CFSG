module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrStruct
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt CFSG.LieType.CurtisTits
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem four_le_card_of_two_le {F : Type} [Fintype F] {f : ℕ} (hcard : Nat.card F = 2 ^ f)
    (hf : 2 ≤ f) : 4 ≤ Nat.card F := by
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem parabStruct_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) (hf : 2 ≤ f) : ParabStruct Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (borelQuotient_sl
    ((projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm)).parabStruct
    (four_le_card_of_two_le hcard hf) rankOneNode_sl

theorem parabStruct_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) (hf : 2 ≤ f) : ParabStruct Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact (borelQuotient_sp e).parabStruct (four_le_card_of_two_le hcard hf) rankOneNode_sp

theorem parabStruct_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (hf : 2 ≤ f) : ParabStruct Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact (borelQuotient_spinPlus hn3 e).parabStruct (four_le_card_of_two_le hcard hf)
    (rankOneNode_spinPlus hn3)

theorem parabStruct_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (hf : 2 ≤ f) : ParabStruct Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hn4 : 4 ≤ n := by omega
  refine (borelQuotient_spinMinus hirr hn4 e).parabStruct
    (four_le_card_of_two_le hcard hf) fun i => ?_
  by_cases hk : i.val + 1 < n - 1
  · exact rankOneNode_spinMinus_long hirr hk
  · exact rankOneNode_spinMinus_short hirr hk

theorem parabStruct_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (hf : 2 ≤ f) : ParabStruct Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  exact (borelQuotient_su hcard (by omega) ζ hζ e).parabStruct hq4 (rankOneNode_su hcard)

end CFSG.AGLEmbedding.ParabAutIrr

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHPSylow
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg

theorem isElemAbelian_of_le_normalizer_fiveList {Y : Type} [Group Y] [Finite Y]
    (hc : CFSG.Open.StatedClassicalModel Y .PSp 3 2 1 ∨ CFSG.Open.StatedClassicalModel Y .PSp 4 2 1 ∨
      CFSG.Open.StatedClassicalModel Y .POmegaMinus 4 2 1 ∨
      CFSG.Open.StatedClassicalModel Y .PSU 4 2 1 ∨ CFSG.Open.StatedClassicalModel Y .PSU 5 2 1)
    (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    IsElemAbelian 3 V := by
  have hsp : ∀ {n : ℕ}, 1 ≤ n → CFSG.Open.StatedClassicalModel Y .PSp n 2 1 →
      IsElemAbelian 3 V := by
    intro n hn h
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
    have hK2 : Nat.card K = 2 := by simpa using hcard
    have := Fintype.ofFinite K
    have : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    exact isElemAbelian_of_le_normalizer_borel (borelQuotient_sp e) (by rw [hK2]; norm_num)
      ⟨⟨0, by show 0 < n; omega⟩⟩ T V hV hV3
  have hsu : ∀ {n : ℕ}, 4 ≤ n → CFSG.Open.StatedClassicalModel Y .PSU n 2 1 →
      IsElemAbelian 3 V := by
    intro n hn h
    obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := id h
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
    exact isElemAbelian_of_le_normalizer_borel (borelQuotient_su hcard (by omega) ζ hζ e)
      (by rw [hcard]; norm_num) ⟨⟨0, by show 0 < n / 2; omega⟩⟩ T V hV hV3
  rcases hc with h | h | h | h | h
  · exact hsp (by norm_num) h
  · exact hsp (by norm_num) h
  · obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
    have hF2 : Nat.card F = 2 := by simpa using hcard
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
    have : Finite (spinGroup (quadMinus 4 F b c)) :=
      finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
    exact isElemAbelian_of_le_normalizer_borel (borelQuotient_spinMinus hirr (by omega) e)
      (by rw [hF2]; norm_num) ⟨⟨0, by show 0 < 4 - 1; omega⟩⟩ T V hV hV3
  · exact hsu (by norm_num) h
  · exact hsu (by norm_num) h

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

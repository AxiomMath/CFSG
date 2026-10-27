module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNodeLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieNodeSylow
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.QuasithinUnique CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.Universal.Spin.OddCT

section Minus

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [CharP F 2] in
include hirr in
theorem card_minusTorus_four_dvd_three (hF : Nat.card F = 2) :
    Nat.card (⨆ k, minusTorus 4 hirr k : Subgroup (spinGroup (quadMinus 4 F b c))) ∣ 3 := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have := Fintype.ofFinite F
  have := Fintype.ofFinite (ShortField b c)
  set k₀ : Fin (4 - 1) := ⟨2, by omega⟩ with hk₀
  have hS : (shortTorusHom 4 hirr k₀).range = shortTorus 4 hirr k₀ := range_shortTorusHom 4 hirr k₀
  have hScard : Nat.card (shortTorus 4 hirr k₀) ∣ 3 := by
    rw [← hS]
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [Nat.card_units, SpinMinusClosed.card_shortField, hF]
    norm_num
  have hle : (⨆ k, minusTorus 4 hirr k : Subgroup (spinGroup (quadMinus 4 F b c))) ≤
      shortTorus 4 hirr k₀ := by
    refine iSup_le fun k => ?_
    by_cases hk : k.val + 1 < 4 - 1
    · rw [minusTorus_of_lt 4 hirr hk]
      rintro _ ⟨u, rfl⟩
      have hu : u = 1 := by
        have h := FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero
        rw [← Nat.card_eq_fintype_card, hF] at h
        exact Units.ext (by simpa using h)
      rw [hu, map_one]
      exact one_mem _
    · have : k = k₀ := Fin.ext (by simp only [hk₀]; omega)
      rw [minusTorus_of_not_lt 4 hirr hk, this]
  exact (Subgroup.card_dvd_of_le hle).trans hScard

theorem card_dvd_three_of_le_normalizer_pomegaMinus_four {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .POmegaMinus 4 2 1) (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    Nat.card V ∣ 3 := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have : Finite (spinGroup (quadMinus 4 F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hB := borelQuotient_spinMinus hirr (by omega) e
  exact (card_dvd_of_le_normalizer_borel hB ⟨⟨0, by show 0 < 4 - 1; omega⟩⟩ T V hV hV3).trans
    (card_minusTorus_four_dvd_three hirr hF2)

end Minus

theorem card_inf_threePrimeSub_of_model_pomegaMinus_four {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .POmegaMinus 4 2 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE : Nat.card E = 9) :
    Nat.card (E ⊓ threePrimeSub J : Subgroup Y) = 3 := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have : Finite (spinGroup (quadMinus 4 F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hB := borelQuotient_spinMinus hirr (by omega) e
  refine card_inf_threePrimeSub_of_oneNode hB (twoLevi_spinMinus hirr hB.ct hB.extras hF2)
    (fun _ _ h => h.elim) (fun i => hasOrderThree_spinMinus hirr i) (fun i => ?_) ?_
    (card_minusTorus_four_dvd_three hirr hF2) T J hNJ hJ hperf hEJ hE
  · by_cases hk : i.val + 1 < 4 - 1
    · exact Or.inr (dvd_of_eq (spinMinus_long_card hirr hF2 hk))
    · exact Or.inl (spinMinus_short_perfect hirr hF2 hk)
  · intro i j hij hc
    by_contra hno
    push Not at hno
    have hi' : i.val + 1 < 4 - 1 := by
      by_contra hk
      exact hno.1 (spinMinus_short_perfect hirr hF2 hk)
    have hj' : j.val + 1 < 4 - 1 := by
      by_contra hk
      exact hno.2 (spinMinus_short_perfect hirr hF2 hk)
    have hne := Fin.val_ne_of_ne hij
    have hc' : cartanB (minusDatum 4 hirr).rank i j = 0 := hc
    have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := by omega
    rcases hadj with hadj | hadj
    · rw [cartanB_of_succ hadj] at hc'
      omega
    · rw [cartanB_of_pred hadj] at hc'
      split_ifs at hc'

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

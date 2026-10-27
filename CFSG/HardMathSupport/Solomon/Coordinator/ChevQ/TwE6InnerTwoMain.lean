module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoPlane
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRankZero
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeD4

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false

theorem twThreeScope_ne_two {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h : TwThreeScope K σ) : q ≠ 2 := by
  obtain ⟨q', -, hKq, -, hgood, -⟩ := h
  have hqq : q'.card = q := Nat.pow_left_injective two_ne_zero (hKq.symm.trans hK)
  intro h2
  exact (E6ThreeF4Close.not_isTwoPow_of_seitzGoodIndex_twE6 hgood).1
    (isTwoPow_of_card_eq' (by rw [hqq, h2]; norm_num))

section Cases


theorem twE6InnerNRTwo_of_cases (hN1 : TwE6ToralNegTwo) (hI : TwE6InnerA2CaseTwo)
    (hII : TwE6InnerNoA2Two) : TwE6InnerNRTwo := by
  intro K _ _ σ q hK hσ hq hq2 E₀ hE₀ hc hN
  by_cases h24 : ∃ s ∈ E₀, s ≠ 1 ∧ twE6FixDim K σ s = 24
  · rcases hI K σ q hK hσ hq hq2 E₀ hE₀ hc hN h24 with hP | hT
    · exact Or.inl hP
    · exact Or.inr (hN1 K σ q hK hσ hq E₀ hE₀ hc hN hT)
  · exact Or.inr (hN1 K σ q hK hσ hq E₀ hE₀ hc hN
      (hII K σ q hK hσ hq hq2 E₀ hE₀ hc hN fun s hs hs1 h => h24 ⟨s, hs, hs1, h⟩))

end Cases

section Plane


theorem twE6_hyperGen_of_plane (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hKq : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hcard : Nat.card E₀ = 3 ^ 3) (P₀ : Subgroup (twistedE6RootGroup K σ)) (hP₀E : P₀ ≤ E₀)
    (hP₀c : Nat.card P₀ = 3 ^ 2) (hP₀24 : ∀ s ∈ P₀, s ≠ 1 → twE6FixDim K σ s = 24) :
    HyperGen 3 ⊤ E₀ := by
  have hinj : Function.Injective (MulAut.conj : twistedE6RootGroup K σ →* MulAut _) :=
    conj_injective_of_center_eq_bot' (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  refine hyperGen_top_of_seitzHyperGamma_conj (innerPlane_of_core K σ q hK3 hσ hKq h3 hq2 _
    (hE₀.map _) ?_ ?_ (P₀.map MulAut.conj) (Subgroup.map_mono hP₀E) ?_ ?_)
  · rw [Subgroup.card_map_of_injective hinj, hcard]
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rw [Subgroup.card_map_of_injective hinj, hP₀c]
  · rintro s ⟨t, ht, hts⟩ hs1
    rw [← hinj hts] at hs1 ⊢
    exact hP₀24 t ht hs1


theorem twE6InnerCubeGenAt_two_of_r2 (hNR : TwE6InnerNRTwo) : TwE6InnerCubeGenAt 2 := by
  intro K _ _ σ q hK hσ hq hs E₀ hE₀ hc hN
  have hq2 : q ≠ 2 := twThreeScope_ne_two hK hs
  rcases hNR K σ q hK hσ hq hq2 E₀ hE₀ hc hN with
    ⟨P₀, hP₀E, hP₀c, hP₀24⟩ | ⟨Fr, hFr, v, hv, g0, hg0C, hg0, hdiag⟩
  · have hK3 : ringChar K ≠ 3 := by
      refine ringChar_ne_three_of_not_dvd fun h3 => ?_
      rw [hK] at h3
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    exact twE6_hyperGen_of_plane K σ q hK3 hσ hK (by omega) hq2 E₀ hE₀ hc P₀ hP₀E hP₀c hP₀24
  · exact twE6_hyperGen_of_rankZero q K σ hK hσ hq hq2 E₀ hE₀ hc hN Fr hFr v hv g0 hg0C hg0 hdiag

theorem twE6InnerCubeGenAt_two_of_cases (hN1 : TwE6ToralNegTwo) (hI : TwE6InnerA2CaseTwo)
    (hII : TwE6InnerNoA2Two) : TwE6InnerCubeGenAt 2 :=
  twE6InnerCubeGenAt_two_of_r2 (twE6InnerNRTwo_of_cases hN1 hI hII)

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

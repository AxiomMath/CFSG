module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLData

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem bglu_data {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (hU : ∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSU 3 q F)))
    {b x : MulAut K} (hb : IsFieldAutThree b) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hx : IsInnDiagThree x) :
    ∃ (p f : ℕ) (F : Type) (_ : Field F) (hF : UnitaryFieldData p f F)
      (η : (K ⧸ Subgroup.center K) ≃* unitaryPSU hF 3) (σ : F ≃+* F) (A : unitaryIsom3 hF),
      orderOf σ = 3 ∧ 2 < p ^ f ∧
      MulAut.congr η (centerDescend K b) = psuField hF σ ∧
      MulAut.congr η (centerDescend K x) = psuConj hF A := by
  obtain ⟨F0, hF0, hfin0, q0, hcard0, ⟨e0⟩⟩ := hU
  have hpsu : IsPSUn 3 q0 (K ⧸ Subgroup.center K) := ⟨F0, hF0, hfin0, hcard0, ⟨e0⟩⟩
  rcases hb with h | hL3 | hU3
  · exact absurd h hb1
  · exfalso
    obtain ⟨K', _, _, θ, -, -, -, -, -⟩ := hL3
    exact l514c_not_psl_psu ⟨K', inferInstance, inferInstance, rfl, ⟨θ⟩⟩ hpsu
  obtain ⟨p, f, F, hFf, hF, e, σ₀, γ, -, he⟩ := fieldAutPSU3_data hU3
  have hq := two_lt_pow_of_quasisimple hK hF e
  have hτ3 : MulAut.congr e (centerDescend K b) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hb3, map_one, map_one]
  have hnot : MulAut.congr e (centerDescend K b) ∉ (psuConj hF).range := by
    intro hin
    have := eq_one_of_inndiag_of_field (goodPinned_psu hF hq) (goodPinned_psu hF hq) e e
      (τ := centerDescend K b) hin (φ := psuField hF σ₀) ⟨σ₀, rfl⟩ γ he
    exact hb1 (eq_one_of_centerDescend_eq_one hK this)
  obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq _ hτ3 hnot
  have hxin : MulAut.congr e (centerDescend K x) ∈ (psuConj hF).range := by
    rcases hx with hxL | hxU
    · exfalso
      obtain ⟨K', _, _, θ, -, -, -⟩ := hxL
      exact l514c_not_psl_psu ⟨K', inferInstance, inferInstance, rfl, ⟨θ⟩⟩ hpsu
    · obtain ⟨p', f', F', _, hF', e', hmem⟩ := AutL3.inndiagPSU3_data hK hxU
      have hq' := two_lt_pow_of_quasisimple hK hF' e'
      exact bgll_inndiag_transport (goodPinned_psu hF' hq') (goodPinned_psu hF hq) e' e hmem
  obtain ⟨A0, hA0⟩ := hxin
  set κ : MulAut (unitaryPSU hF 3) := psuConj hF H with hκ
  refine ⟨p, f, F, hFf, hF, e.trans κ.symm, σ, H⁻¹ * A0 * H, hσ, hq, ?_, ?_⟩
  · rw [congr_trans', congr_self, hH]
    change κ⁻¹ * (κ * psuField hF σ * κ⁻¹) * κ⁻¹⁻¹ = _
    group
  · rw [congr_trans', congr_self, ← hA0]
    change κ⁻¹ * psuConj hF A0 * κ⁻¹⁻¹ = _
    rw [map_mul, map_mul, map_inv, ← hκ]
    simp [inv_inv]

end CFSG.HardMathSupport.Solomon.Coordinator

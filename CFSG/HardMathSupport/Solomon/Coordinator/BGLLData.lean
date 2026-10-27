module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514CIso
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem bgll_inndiag_transport {Q M₁ M₂ : Type*} [Group Q] [Group M₁] [Group M₂]
    {P₁ : PinnedAut M₁} {P₂ : PinnedAut M₂} (g₁ : GoodPinned P₁) (g₂ : GoodPinned P₂)
    (e₁ : Q ≃* M₁) (e₂ : Q ≃* M₂) {τ : MulAut Q} (h₁ : MulAut.congr e₁ τ ∈ P₁.inndiag) :
    MulAut.congr e₂ τ ∈ P₂.inndiag :=
  (PinnedAut.mem_comap_inndiag P₂ e₂).1 (g₁.comap_inndiag_eq_comap g₂ e₁ e₂ ▸
    (PinnedAut.mem_comap_inndiag P₁ e₁).2 h₁)

theorem bgll_data {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (hL : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSL 3 F)))
    {b x : MulAut K} (hb : IsFieldAutThree b) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hx : IsInnDiagThree x) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (η : (K ⧸ Subgroup.center K) ≃* projectiveSL 3 F)
      (σ : F ≃+* F) (g : GL (Fin 3) F), orderOf σ = 3 ∧
      MulAut.congr η (centerDescend K b) = fieldAut 3 F σ ∧
      MulAut.congr η (centerDescend K x) = conjAut 3 F g := by
  obtain ⟨F0, hF0, hfin0, ⟨e0⟩⟩ := hL
  have hpsl : IsPSLn 3 (Nat.card F0) (K ⧸ Subgroup.center K) := ⟨F0, hF0, hfin0, rfl, ⟨e0⟩⟩
  rcases hb with h | hL3 | hU3
  · exact absurd h hb1
  swap
  · exfalso
    obtain ⟨K', _, _, q, θ, σ, φ, γ, hcard, -, -, -⟩ := hU3
    exact l514c_not_psl_psu hpsl ⟨K', inferInstance, inferInstance, hcard, ⟨θ⟩⟩
  obtain ⟨F, hFf, hFfin, e, σ₀, γ, he⟩ := fieldAutPSL3_data hL3
  have hτ3 : MulAut.congr e (centerDescend K b) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hb3, map_one, map_one]
  have hnot : MulAut.congr e (centerDescend K b) ∉ linearAutGroup 3 F := by
    intro hin
    have := eq_one_of_inndiag_of_field (goodPinned_psl F) (goodPinned_psl F) e e
      (τ := centerDescend K b) (by rw [stdPinnedPSL_inndiag]; exact hin)
      (φ := fieldAut 3 F σ₀) (by rw [stdPinnedPSL_field]; exact ⟨σ₀, rfl⟩) γ he
    exact hb1 (eq_one_of_centerDescend_eq_one hK this)
  obtain ⟨σ, hσ, H, hH⟩ := linear_order_three_field_descent le_rfl _ hτ3 hnot
  have hxin : MulAut.congr e (centerDescend K x) ∈ linearAutGroup 3 F := by
    rcases hx with hxL | hxU
    · obtain ⟨F', _, _, e', hmem⟩ := AutL3.inndiagPSL3_data hxL
      have := bgll_inndiag_transport (goodPinned_psl F') (goodPinned_psl F) e' e hmem
      rwa [stdPinnedPSL_inndiag] at this
    · exfalso
      obtain ⟨K', _, _, q, θ, φ, hcard, -, -⟩ := hxU
      exact l514c_not_psl_psu hpsl ⟨K', inferInstance, inferInstance, hcard, ⟨θ⟩⟩
  obtain ⟨g0, hg0⟩ := mem_linearAutGroup_iff.1 hxin
  set κ : MulAut (projectiveSL 3 F) := conjAut 3 F H with hκ
  refine ⟨F, hFf, hFfin, e.trans κ.symm, σ, H⁻¹ * g0 * H, hσ, ?_, ?_⟩
  · rw [congr_trans', congr_self]
    rw [hH]
    change κ⁻¹ * (κ * fieldAut 3 F σ * κ⁻¹) * κ⁻¹⁻¹ = _
    group
  · rw [congr_trans', congr_self, ← hg0]
    change κ⁻¹ * conjAut 3 F g0 * κ⁻¹⁻¹ = _
    rw [map_mul, map_mul, map_inv, ← hκ]
    simp [inv_inv]

end CFSG.HardMathSupport.Solomon.Coordinator

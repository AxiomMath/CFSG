module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAltCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import Certificates.Certificate5007

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem core_commutator_le_of_localAbelianCore_of_oddOuterInner (hLB : FooteLBalanceInput)
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (hout : OddOuterInner (Y ⧸ Open.fusionZStar Y))
    (hAC : ∀ i : MulAut (Y ⧸ Open.fusionZStar Y), orderOf i = 2 →
      ∀ x y : ↥(pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut (Y ⧸ Open.fusionZStar Y))))),
        x * y = y * x) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : Y.IsSubnormal := by
    obtain ⟨-, -, h, -, -⟩ := hY
    exact h
  have hOK := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  obtain ⟨hWN, hcent⟩ := hLB K a ha Y hY
  set W := oddCoreOfCentralizer a
  have hWW := commutator_self_le W
  by_cases hswap : conjugate Y a ≠ Y
  · exact ((commutator_mono hWW le_rfl).trans (hcent (Or.inl hswap))).trans hOK
  have haN := mem_normalizer_of_conjugate_eq (not_not.mp hswap)
  set ψ := Y.normalizerMonoidHom
  set ᾱ := zStarAut Y (ψ ⟨a, haN⟩) with hᾱ
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  by_cases hα1 : ᾱ = 1
  ·
    refine ((commutator_mono hWW le_rfl).trans (hcent (Or.inr fun x hx => ?_))).trans hOK
    have hc := commutator_mem_oddCore_of_zStarAut_eq_one hY haN hα1 hx
    have hc' := Walter.conj_mem_map_of_characteristic (D := pPrimeCore 2 ↥Y)
      (le_normalizer (inv_mem hx)) hc
    rw [show x⁻¹ * ⁅a, x⁆ * x⁻¹⁻¹ = x⁻¹ * a⁻¹ * x * a by
      rw [commutatorElement_def, hainv]; group] at hc'
    exact hc'
  have hord : orderOf ᾱ = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rw [hᾱ, ← map_pow, ← map_pow, sq]
    have : (⟨a, haN⟩ : normalizer (Y : Set K)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
    rw [this, map_one, map_one]
  have hcomm := hAC ᾱ hord
  have hker : ⁅W, W⁆ ≤ ((zStarAut Y).comp ψ).ker.map (normalizer (Y : Set K)).subtype := by
    rw [commutator_le]
    intro w₁ hw₁ w₂ hw₂
    refine ⟨⁅(⟨w₁, hWN hw₁⟩ : normalizer (Y : Set K)), ⟨w₂, hWN hw₂⟩⁆, ?_,
      by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    obtain ⟨x₁, hx₁, e₁⟩ := zStarAut_mem_oddCore_centralizer hY ha haN hWN hout hw₁
    obtain ⟨x₂, hx₂, e₂⟩ := zStarAut_mem_oddCore_centralizer hY ha haN hWN hout hw₂
    show zStarAut Y (ψ ⟨w₁, hWN hw₁⟩) * zStarAut Y (ψ ⟨w₂, hWN hw₂⟩) =
      zStarAut Y (ψ ⟨w₂, hWN hw₂⟩) * zStarAut Y (ψ ⟨w₁, hWN hw₁⟩)
    rw [← e₁, ← e₂]
    have h₁ := hcomm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
    have h₂ : x₁ * x₂ = x₂ * x₁ := by
      have := congrArg Subtype.val h₁
      simpa using this
    have h₃ := congrArg Subtype.val h₂
    simpa using h₃
  rw [commutator_le]
  intro g hg y hy
  obtain ⟨n, hn, rfl⟩ := hker hg
  exact hOK (commutator_mem_oddCore_of_zStarAut_eq_one hY n.2 (by simpa using hn) hy)

@[expose] def FooteCoreResidualInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SectionRank.IsKGroupCat K → ∀ a : K, orderOf a = 2 →
    ∀ Y : Subgroup K, IsPComponent 2 Y →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) →
    (¬ ∃ n : ℕ, Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* alternatingGroup (Fin n))) →
    ¬ (OddOuterInner (Y ⧸ Open.fusionZStar Y) ∧ UBalanced (Y ⧸ Open.fusionZStar Y)) →
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K

theorem kGroupFooteCoreInput_of_residual (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hres : FooteCoreResidualInput) : KGroupFooteCoreInput := by
  intro K _ _ hK a ha Y hY
  by_cases hL2 : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f
  · exact Or.inl hL2
  right
  by_cases hb : OddOuterInner (Y ⧸ Open.fusionZStar Y) ∧ UBalanced (Y ⧸ Open.fusionZStar Y)
  · exact (commutator_mono (commutator_self_le _) le_rfl).trans
      (core_commutator_le_of_balanced_of_oddOuterInner footeLBalanceInput_holds hU hK ha hY hb.1
        hb.2)
  by_cases halt : ∃ n : ℕ, Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨e⟩⟩ := halt
    obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
    have := hsimple
    have h5 := AltCore.five_le_of_simple hna e
    by_cases h6 : n = 6
    · subst h6
      exact absurd ⟨3, 2, Nat.prime_three, by norm_num, by norm_num,
        CFSG.GH74.E2.lieModel_psl_two_nine_of_alt_six ⟨e⟩⟩ hL2
    · exact core_commutator_le_of_localAbelianCore_of_oddOuterInner footeLBalanceInput_holds ha
        hY (AltCore.oddOuterInner_alternating h5 h6 e) fun i hi =>
          AltCore.commute_of_mem_oddCore_mulAut h5 h6 e i (by rw [← sq, ← hi, pow_orderOf_eq_one])
  · exact hres K hK a ha Y hY hL2 halt hb

theorem footeCoreHypothesis_of_residual (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hres : FooteCoreResidualInput) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X) :
    FooteCoreHypothesis X :=
  footeCoreHypothesis_of_kGroupInput (kGroupFooteCoreInput_of_residual hU hres) hna hK

end CFSG.ComponentClassification.FooteLit

module

public import CFSG.LocalAnalysis.Gross82.OrderThree
import CFSG.LocalAnalysis.Gross82.OrderThreeArith
import CFSG.LocalAnalysis.Gross82.OrderThreeTools
import CFSG.LocalAnalysis.Gross82.ExceptionalFieldOrder
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7f

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBT CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7f
open CFSG.LocalAnalysis.Gross82.OrderThree

section


private theorem exists_field_model_E6 {K : Type} [Group K] {n ℓ f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel K .E6 n ℓ f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_θ : K ≃* adjointGroup Tag.E6 F),
      Nat.card F = ℓ ^ f := by
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    exact ⟨F, hF, hFin,
      e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot), hFcard⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

private theorem field_descent_E6 {F : Type} [Field F] [Finite F] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hFcard : Nat.card F = ℓ ^ f)
    (x : MulAut (adjointGroup Tag.E6 F)) (hx3 : x ^ 3 = 1)
    (hmem : x ∉ e6Inndiag F) :
    ∃ d : ℕ, f = 3 * d ∧
      Nat.card (fixedSubgroup x) ∣ lieOrderNumerator .E6 0 (ℓ ^ d) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP F ℓ := finite_field_prime_power_characteristic hℓ hf hFcard
  obtain ⟨σ, hσ3, h3f, ψ, hψ⟩ :=
    exists_conj_entrywise_of_not_mem_e6Inndiag hℓ hf F hFcard Nat.prime_three
      (by norm_num) hx3 hmem
  have hq₀ : Nat.card (fixSubfield σ) = ℓ ^ (f / 3) := by
    rw [(card_fixSubfield hℓ hf hFcard σ).2, hσ3]
  refine ⟨f / 3, (Nat.mul_div_cancel' h3f).symm, ?_⟩
  rw [← card_fixedSubgroup_conj ψ x, hψ,
    (card_fixedSubgroup_entrywiseAdjointAut (τ := Tag.E6) σ)]
  exact card_entrywiseFixedGroup_E6_dvd σ hq₀

private theorem false_of_not_inner_E6 (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .E6 n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .E6 n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .E6 n (ℓ ^ f)) {α : MulAut K} (hα3 : α ^ 3 = 1)
    {P : Sylow 3 K} (hfix : ∀ x ∈ (P : Subgroup K), α x = x) (hαin : α ∉ inner K) : False := by
  obtain ⟨hℓ, hf, hn⟩ := id hadm
  subst hn
  obtain ⟨F, hF, hFin, θ, hFcard⟩ := exists_field_model_E6 hmodel
  letI := hF
  letI := hFin
  have h3q : 3 ∣ Nat.card F - 1 := by
    rw [hFcard]
    exact h3.trans (Nat.gcd_dvd_right 3 (ℓ ^ f - 1))
  have hβp : (MulAut.congr θ α) ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.E6 F) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  obtain ⟨P', hfix'⟩ := exists_sylow_fix_congr θ P hfix
  by_cases hmem : MulAut.congr θ α ∈ e6Inndiag F
  · exact hβout (e6InndiagSylowThree_holds F h3q P' (MulAut.congr θ α) hmem
      ⟨1, by simpa using hβp⟩ hfix')
  · obtain ⟨d, hfd, hdvd⟩ := field_descent_E6 hℓ hf hFcard _ hβp hmem
    have hC : Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .E6 0 (ℓ ^ d) := by
      rw [← card_fixedSubgroup_congr θ α]
      exact hdvd
    have hs : ℓ ^ f = (ℓ ^ d) ^ 3 := by rw [hfd, pow_mul']
    have hd1 : d ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hfd
      omega
    have hs2 : 2 ≤ ℓ ^ d := hℓ.two_le.trans (Nat.le_self_pow hd1 ℓ)
    have ha : lieOrderNumerator .E6 0 (ℓ ^ d) ≠ 0 :=
      CFSG.AGLEmbedding.OuterSylow.lieOrderNumerator_ne_zero (by decide)
        (CFSG.AGLEmbedding.OuterSylow.one_le_lieSylowExponent hadm) hs2
    exact false_of_card_fixedSubgroup_dvd hLie hadm hmodel P hfix hs ha hC
      (ExceptionalFieldOrder.padicValNat_three_lieOrder_e6_cube_lt hs2)

theorem grossThreeInnerOrderThree_E6 (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .E6 n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .E6 n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .E6 n (ℓ ^ f)) : GrossThreeInnerOrderThree K := by
  intro α hα P hfix
  by_contra hαin
  exact false_of_not_inner_E6 hLie hadm hmodel h3 hα hfix hαin

end

end CFSG.LocalAnalysis.Gross82

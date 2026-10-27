module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.ExcOuter
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2

section Residual


@[expose] def Up34C2OutDiag_E6 : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = 2 ^ f →
    ∀ ψ ∈ e6Inndiag K,
      ψ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K) →
        ¬ Up34Pumpup (adjointGroup Tag.E6 K) ψ

end Residual

namespace Up34Chev2

section Field


theorem noL34Layer_entrywise_e6 {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hcard : Nat.card (fixSubfield σ) = 2 ^ d) :
    NoL34Layer (entrywiseAdjointAut Tag.E6 σ) := by
  haveI : Finite ↥(fixSubfield σ) := Subtype.finite
  have hM : ChevalleyExceptionalModel ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) .E6 2 d :=
    ⟨⟨Nat.prime_two, hd, rfl⟩, untwisted_adjointGroup hcard⟩
  obtain ⟨hnt, hsimp⟩ := CFSG.LieType.Simplicity.fam_e6_simplicity _ 2 d hM
  have hZ : Subgroup.center ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) = ⊥ :=
    center_adjointGroup_eq_bot
  exact noL34Layer_entrywise_exc (t := .E6) (by decide) σ
    (Or.inr (Or.inl ⟨rfl, by decide, hM⟩)) hsimp hZ

theorem noL34Layer_of_not_mem_e6Inndiag {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {x : MulAut (adjointGroup Tag.E6 K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ e6Inndiag K) : NoL34Layer x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨σ, hσo, hpf, δ, hδ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag Nat.prime_two hf K hK
    Nat.prime_three (by norm_num) hx3 hxo
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) (by norm_num)
  have hcard : Nat.card (fixSubfield σ) = 2 ^ (f / 3) := by
    have := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hf hK σ).2
    rwa [hσo] at this
  have h1 : NoL34Layer (δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹) :=
    noL34Layer_conj δ⁻¹ (noL34Layer_entrywise_e6 hd σ hcard)
  have h2 : δ⁻¹ * entrywiseAdjointAut Tag.E6 σ * δ⁻¹⁻¹ = x := by
    rw [← hδ]
    group
  rwa [h2] at h1

end Field

end Up34Chev2

section Family


theorem up34C2Out_e6_of_diag (hD : Up34C2OutDiag_E6) : Up34Chev2Out FamE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | E6 q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_E6 q hv e
    have hU : UntwistedChevalleyModel S .E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨F, hFf, hFin, hFcard, ⟨θ⟩⟩ := exists_equiv_adjointGroup_of_untwisted hU
    rw [hq2] at hFcard
    have hβ3 : MulAut.congr θ α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
    have hβinn : MulAut.congr θ α ∉
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.E6 F) :=
      fun hin => hα ((congr_mem_inner_iff_of_equiv θ α).mp hin)
    by_cases hdiag : MulAut.congr θ α ∈ e6Inndiag F
    · exact hD q.exponent F q.exponent_pos hFcard _ hdiag hβinn (hp.of_congr θ)
    · have h1 := noL34Layer_of_not_mem_e6Inndiag q.exponent_pos hFcard hβ3 hdiag
      exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr θ h1)
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6

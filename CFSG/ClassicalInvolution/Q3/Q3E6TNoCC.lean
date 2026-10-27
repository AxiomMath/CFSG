module

public import CFSG.ClassicalInvolution.Q3.Q3WASTSign
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups


section Spin

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}
  {𝔉 : Set (Subgroup (spinGroup Q))}

theorem exists_overlap_of_linear3 (S : ModelFacts.SpinCtx3 3 1 Q 𝔉) {R₁ R₂ : Subgroup (spinGroup Q)}
    (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) :
    ∃ i₁ i₂ : V ≃ₗ[GaloisField 3 1] V, IsFundamental Q (R₁.map (spinAction Q)) i₁ ∧
      IsFundamental Q (R₂.map (spinAction Q)) i₂ ∧ i₁ * i₂ = i₂ * i₁ ∧
      i₂ ∈ Subgroup.normalizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) ∧
      i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) ∧
      HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) := by
  have hodd := S.odd_card
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv : ∀ {R : Subgroup (spinGroup Q)}, R ∈ 𝔉 → ∀ {i : V ≃ₗ[GaloisField 3 1] V},
      IsFundamental Q (R.map (spinAction Q)) i →
        ∃ c ∈ R, orderOf c = 2 ∧ spinAction Q c = i := by
    intro R hR i hI
    obtain ⟨c, hcR, hc⟩ := hI.mem
    have hcc : c * c = 1 := S.inj R hR (c * c) (R.mul_mem hcR hcR)
      (by rw [map_mul, hc]; exact hI.mul_self)
    have hc1 : c ≠ 1 := fun h => hI.ne_one hodd (by rw [← hc, h, map_one])
    exact ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1, hc⟩
  obtain ⟨c₁, hc₁, ho₁, e₁⟩ := hinv h₁ hI₁
  obtain ⟨c₂, hc₂, ho₂, e₂⟩ := hinv h₂ hI₂
  have hc : c₁ * c₂ = c₂ * c₁ := standardPair_involutions_commute h2 hW hc₁ hc₂ ho₁ ho₂
  have hcπ : i₁ * i₂ = i₂ * i₁ := by rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  have hnc : ¬ Commutes R₁ R₂ := not_commutes_of_linearBlockStandardPair hW
  have hL : R₁.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    ne_of_linearBlockStandardPair hW (S.eq_of_map_eq h₁ h₂ h)
  have hcent : i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hcen => hnc (S.commutes_of_map h₁
      ((IsFundamental.commute_iff hodd hI₁ hI₂ hcπ hL).mpr hcen))
  have hN := S.mem_normalizer ho₁ ho₂ hc hI₁ hI₂ e₁ e₂ hcπ
  obtain ⟨-, hdich⟩ := lemma_6_10_dichotomy S.card_eq S.card_eq' hodd hI₁ hI₂ hcπ hN hcent
  rcases hdich with ⟨hs, -⟩ | ⟨-, huni⟩
  · exact ⟨i₁, i₂, hI₁, hI₂, hcπ, hN, hcent, hs⟩
  · exact (Q3W.false_of_linear_of_unitary3 ⟨W, hW⟩
      (S.unitary_of_map h₁ h₂ ⟨_, huni⟩)).elim

theorem false_of_commutes_linear_pair_spin3 (S : ModelFacts.SpinCtx3 3 1 Q 𝔉)
    (hfam : ∀ v : Fin 5 → Bool → V, ¬ IsHypFam Q v) {R₁ R₂ R₃ : Subgroup (spinGroup Q)}
    (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂)
    (h31 : Commutes R₃ R₁) (h32 : Commutes R₃ R₂) : False := by
  obtain ⟨i₁, i₂, hI₁, hI₂, hc, hN, hC, hs⟩ := exists_overlap_of_linear3 S h₁ h₂ hlin
  obtain ⟨i₃, hI₃⟩ := S.map R₃ h₃
  have hcomm : ∀ {A B : Subgroup (spinGroup Q)}, Commutes A B →
      Commutes (A.map (spinAction Q)) (B.map (spinAction Q)) := by
    rintro A B hAB _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAB a ha b hb]
  exact false_of_commutes_linear_pair S.odd_card hfam hI₁ hI₂ ⟨i₃, hI₃⟩ hc hN hC hs
    (hcomm h31) (hcomm h32)

end Spin

theorem noCommonCommutant3_pOmegaMinus_five
    {R₁ R₂ R₃ : Subgroup (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (h₃ : R₃ ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂)
    (h31 : Commutes R₃ R₁) (h32 : Commutes R₃ R₂) : False := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have S := ModelFacts.spinCtx3_pOmegaMinus hadm (by norm_num : 3 ^ 1 = 3)
  have hL := fun {R : Subgroup (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D) =>
    ModelFacts.fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _ hR
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd S.odd_card
  exact false_of_commutes_linear_pair_spin3 S
    (fun v => Q3W.EX.false_of_isHypFam_quadMinus3 (m := 4) h2
      (CFSG.LieType.Universal.minusCoeffs_irr 3 1) (by rw [Q3W.card_gf3]; norm_num) v)
    (hL h₁) (hL h₂) (hL h₃) hlin h31 h32

end CFSG.ClassicalInvolution.Q3.Q3E6T

module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHG2
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3U

open CFSG CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance.Q27 CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem g2d4_model_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {k e : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t k p e)
    (hef : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) :
    Group.IsPerfect (modelUniv t k p e Fact.out).K ∧
      Subgroup.center (modelUniv t k p e Fact.out).K = ⊥ ∧
      InvolutionOddCoreTrivial (modelUniv t k p e Fact.out).K ∧
      InvolutionCentralizersGenerate (modelUniv t k p e Fact.out).K := by
  rcases ht with rfl | rfl
  · have hef' : e = f := hef.resolve_right fun h => nomatch h.1
    subst hef'
    have hk : k = 0 := hadm.2.2.1
    subst hk
    refine ⟨⟨(ModelFacts.isQuasisimple_modelUniv .G2 0 p e Fact.out hfund hadm).1⟩,
      CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inl rfl) 0
        hadm.2.1,
      thm5IH_g2_oddCoreTrivial hp2 hadm, ?_⟩
    intro u₁ u₂ h₁ h₂ h₁1 h₂1 hne hcomm
    have h := g2CentralizersGenerate_of_nonToral g2NonToralGenerate_all hp2 hq hadm u₁ u₂ h₁ h₂
      h₁1 h₂1 hne hcomm
    rw [h]
    simp
  · have hk : k = 0 := hadm.2.2
    subst hk
    exact ⟨⟨(ModelFacts.isQuasisimple_modelUniv .trialityD4 0 p e Fact.out hfund hadm).1⟩,
      CFSG.ClassicalInvolution.RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 (Or.inr rfl) 0
        hadm.2.1,
      td4OddCoreAll_proved e hadm hp2, td4GenerateAll_proved e hadm hp2⟩

theorem alphaOf_inducedImage_eq_bot_of_g2d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag}
    {k e : ℕ} (ht : t = .G2 ∨ t = .trialityD4) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (hef : e = f ∨ (t = .trialityD4 ∧ 3 * e = f))
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K)
    {A : Subgroup H} (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1) (hAL : A ≤ ψ.range) :
    alphaOf (inducedImage ψ.range A) = ⊥ := by
  obtain ⟨hperf, hZ, hO, hG⟩ := g2d4_model_facts hp2 hq ht hfund hadm hef
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have : Finite (modelUniv t k p e Fact.out).K := Finite.of_injective ψ hψinj
  have hfaith : ∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a := by
    intro a ha ha1 hcomm
    obtain ⟨s, rfl⟩ := hAL ha
    apply ha1
    have hs : s ∈ Subgroup.center (modelUniv t k p e Fact.out).K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hψinj
      rw [map_mul, map_mul]
      exact (hcomm (ψ g) ⟨g, rfl⟩).symm
    rw [hZ] at hs
    rw [Subgroup.mem_bot.mp hs, map_one]
  exact thm5IH_alphaOf_inducedImage_eq_bot ψ hker hZ hO hG hA4 hA2 hAL hfaith

end CFSG.ClassicalInvolution.Asc77.T3CII.T3U

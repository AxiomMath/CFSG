module

public import CFSG.ClassicalInvolution.Q3.Q3NGCent
public import CFSG.ClassicalInvolution.SmallCases.G2SModel
public import CFSG.ClassicalInvolution.SmallCases.G2SRank3
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactLie
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2GenMax
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19G (FG0Model)


@[expose] def GenFact3 (c : CompData) : Prop :=
  ∀ r r' : c.G, r * r = 1 → r' * r' = 1 → r ≠ 1 → r' ≠ 1 → r ≠ r' → r * r' = r' * r →
    Subgroup.centralizer ({r} : Set c.G) ⊔ Subgroup.centralizer ({r'} : Set c.G) = ⊤

structure G2D4Facts3 (c : CompData) : Prop where
  center_bot : Subgroup.center c.G = ⊥
  simple : IsSimpleGroup c.G
  fg0 : ∀ R ∈ c.fund, FG0Model R
  exists_fund : ∀ u : c.G, u * u = 1 → u ≠ 1 → ∃ R ∈ c.fund, IsUniqueInvolution R u
  inv_conj : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∀ r ∈ R, ∀ r' ∈ R', r * r = 1 → r' * r' = 1 →
    r ≠ 1 → r' ≠ 1 → (∀ y ∈ R, r * y = y * r) → (∀ y ∈ R', r' * y = y * r') →
      ∃ g : c.G, g * r * g⁻¹ = r'
  rank3 : ∀ R ∈ c.fund, ∀ r ∈ R, (∀ y ∈ R, r * y = y * r) → r * r = 1 → r ≠ 1 →
    ∃ w w' : c.G, w * w = 1 ∧ w' * w' = 1 ∧ w ≠ 1 ∧ w' ≠ 1 ∧ w ≠ w' ∧ r * w = w * r ∧
      r * w' = w' * r ∧ w * w' = w' * w ∧ w ≠ r ∧ w' ≠ r ∧ w * w' ≠ r
  shared : ∀ R ∈ c.fund, ∀ y₁ y₂ : c.G, y₁ * y₁ = 1 → y₂ * y₂ = 1 → y₁ ≠ 1 → y₂ ≠ 1 →
    (∀ r ∈ R, r * y₁ = y₁ * r) → (∀ r ∈ R, r * y₂ = y₂ * r) → y₁ = y₂
  gen : GenFact3 c

theorem G2D4Facts3.of_model {t : StatedLieTag} {n : ℕ} (ht : t = .G2 ∨ t = .trialityD4)
    (hadm : StatedLieAdmissible t n 3 1) (hgen : GenFact3 (CompData.model t n)) :
    G2D4Facts3 (CompData.model t n) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he : 1 ≤ 1 := le_rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hgen⟩
  · exact G2D4.center_modelUniv_g2d4_eq_bot hp2 ht n he
  · exact Asc77.T3Typed.isSimpleGroup_model_of_g2d4 hp2 hadm ht
  · intro R hR
    exact NDB.G2S.fg0Model_of_tag hp2 he ht hR
  · intro u hu hu1
    rcases ht with rfl | rfl
    · obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact Asc77.T3Typed.exists_fund_of_involution_g2 hp2 hadm hu hu1
    · have hk : n = 0 := hadm.2.2
      subst hk
      obtain ⟨R, hR, -, hRu⟩ := G2D4Models.exists_perfect_fund_of_involution hp2 hadm hu hu1
      exact ⟨R, hR, hRu⟩
  · intro R hR R' hR' r hr r' hr' hr2 hr'2 hr1 hr'1 hrc hr'c
    exact Balance.Bootstrap.twoClassInvolutionsConj 3 t n 1 hp2 ht hadm R hR R' hR' r hr r' hr'
      hr2 hr'2 hr1 hr'1 hrc hr'c
  · intro R hR r hr hrc hr2 hr1
    exact NDB.G2S.exists_rank_three_model hp2 hadm ht hR hr hrc hr2 hr1
  · intro R hR y₁ y₂ h₁ h₂ hy₁ hy₂ c₁ c₂
    exact eq_of_involutions_centralizing3 ht hadm (MonoidHom.id (CompData.model t n).G)
      Function.injective_id hR ⟨y₁, rfl⟩ ⟨y₂, rfl⟩ h₁ h₂ hy₁ hy₂ c₁ c₂

end CFSG.ClassicalInvolution.Q3.Q3W.EX

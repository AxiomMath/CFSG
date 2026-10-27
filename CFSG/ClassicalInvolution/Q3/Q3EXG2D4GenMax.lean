module

public import CFSG.ClassicalInvolution.Q3.Q3EXG2D4Model
public import CFSG.ClassicalInvolution.RouteD.G2D4TD4NonToral

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem genFact3_of_coatom {c : CompData}
    (hex : ∀ u : c.G, u * u = 1 → u ≠ 1 → ∃ R ∈ c.fund, IsUniqueInvolution R u)
    (hsh : ∀ R ∈ c.fund, ∀ y₁ y₂ : c.G, y₁ * y₁ = 1 → y₂ * y₂ = 1 → y₁ ≠ 1 → y₂ ≠ 1 →
      (∀ r ∈ R, r * y₁ = y₁ * r) → (∀ r ∈ R, r * y₂ = y₂ * r) → y₁ = y₂)
    (hmax : ∀ r : c.G, r * r = 1 → r ≠ 1 →
      IsCoatom (Subgroup.centralizer ({r} : Set c.G))) :
    GenFact3 c := by
  intro r r' hr hr' hr1 hr1' hne hc
  by_contra hntop
  have h1 : Subgroup.centralizer ({r} : Set c.G) ⊔ Subgroup.centralizer ({r'} : Set c.G) =
      Subgroup.centralizer ({r} : Set c.G) := by
    by_contra h
    exact hntop ((hmax r hr hr1).2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h)))
  have h2 : Subgroup.centralizer ({r'} : Set c.G) ≤ Subgroup.centralizer ({r} : Set c.G) :=
    h1 ▸ le_sup_right
  have h3 : Subgroup.centralizer ({r'} : Set c.G) = Subgroup.centralizer ({r} : Set c.G) := by
    by_contra h
    exact (hmax r hr hr1).1 ((hmax r' hr' hr1').2 _ (lt_of_le_of_ne h2 h))
  obtain ⟨R, hR, hRu⟩ := hex r hr hr1
  have hRr' : ∀ x ∈ R, x * r' = r' * x := by
    intro x hx
    have hxr : x ∈ Subgroup.centralizer ({r} : Set c.G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hRu.commute_of_mem hx).symm
    rw [← h3] at hxr
    exact Subgroup.mem_centralizer_singleton_iff.mp hxr
  exact hne (hsh R hR r r' hr hr' hr1 hr1' (fun y hy => (hRu.commute_of_mem hy).symm) hRr')

theorem genFact3_g2_of_coatom {n : ℕ} (hadm : StatedLieAdmissible .G2 n 3 1)
    (hmax : ∀ r : (CompData.model .G2 n).G, r * r = 1 → r ≠ 1 →
      IsCoatom (Subgroup.centralizer ({r} : Set (CompData.model .G2 n).G))) :
    GenFact3 (CompData.model .G2 n) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨hk, -⟩ := hadm.2.2
  subst hk
  refine genFact3_of_coatom ?_ ?_ hmax
  · intro u hu hu1
    exact Asc77.T3Typed.exists_fund_of_involution_g2 hp2 hadm hu hu1
  · intro R hR y₁ y₂ h₁ h₂ hy₁ hy₂ c₁ c₂
    exact eq_of_involutions_centralizing3 (Or.inl rfl) hadm
      (MonoidHom.id (CompData.model .G2 0).G) Function.injective_id hR ⟨y₁, rfl⟩ ⟨y₂, rfl⟩
      h₁ h₂ hy₁ hy₂ c₁ c₂

theorem genFact3_td4 {n : ℕ} (hadm : StatedLieAdmissible .trialityD4 n 3 1) :
    GenFact3 (CompData.model .trialityD4 n) := by
  have hn : n = 0 := hadm.2.2
  subst hn
  intro r r' hr hr' hr1 hr1' hne hc
  exact G2D4Models.sup_centralizer_eq_top_model_td4 (by norm_num) hadm hr hr' hr1 hr1' hne hc

end CFSG.ClassicalInvolution.Q3.Q3W.EX

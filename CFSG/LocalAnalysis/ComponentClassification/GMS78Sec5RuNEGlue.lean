module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEFpf
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEPi7b
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmGlueP

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm

theorem pi7bRels_cases :
    ∀ r ∈ pi7bRels,
    ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) ∧ pi7Word r = 1) ∨
      ((∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))) ∧ pi7Word r = 1) ∨
        r = ruW7Word := by
  have h : ∀ r ∈ pi7bRels, (∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) ∨
      (∀ p ∈ r, p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7))) ∨ r = ruW7Word := by
    decide +kernel
  intro r hr
  rcases h r hr with h₁ | h₂ | h₃
  · exact Or.inl ⟨h₁, pi7Word_eq_one_of_mem_pi7bRels hr⟩
  · exact Or.inr (Or.inl ⟨h₂, pi7Word_eq_one_of_mem_pi7bRels hr⟩)
  · exact Or.inr (Or.inr h₃)

theorem ruB0_le_ruM12 : ruB0 ≤ ruM12 := letterSub_mono (by decide)

theorem ruLetterImg_w_pow_seven
    {G : Type} [Group G] {z : G}
    {A : Subgroup G} {f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G))}
    {f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G))} (hf₁ : IsNormCz f₁ A)
    (hag : RuEdgeAgree f₁ f₂ (MonoidHom.id _)) :
    (ruLetterImg f₁ f₂ 5 * ruLetterImg f₁ f₂ 0 * ruLetterImg f₁ f₂ 2 *
      ruLetterImg f₁ f₂ 6) ^ 7 = 1 :=
  w_pow_seven hf₁ f₂ fun m _ _ hB => hag ⟨m, ruB0_le_ruM12 hB⟩

end CFSG.ComponentClassification.GMS78.RuNE

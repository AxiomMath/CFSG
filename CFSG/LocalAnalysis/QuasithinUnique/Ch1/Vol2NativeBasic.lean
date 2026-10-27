
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public import CFSG.Quasithin.Background.A3Structure37

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem a37_of_core {G : Type} [Group G] [Finite G] (h36 : A36CoreStatementCat G) :
    A37Statement G := by
  intro L₁ h₁ L₂ h₂ hne
  have hS₁ := cComp_normal_span h₁
  have hS₂ := cComp_normal_span h₂
  have hn₁ : cCompSpan (⊤ : Subgroup G) ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₁.1).mp hS₁.2
  have hn₂ : cCompSpan (⊤ : Subgroup G) ≤ Subgroup.normalizer (L₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₂.1).mp hS₂.2
  have hL₂N : L₂ ≤ Subgroup.normalizer (L₁ : Set G) := (le_cCompSpan h₂).trans hn₁
  have : Group.IsPerfect ↥L₁ := A36A.isPerfect_of_mem_cComp h₁
  have : Group.IsPerfect ↥L₂ := A36A.isPerfect_of_mem_cComp h₂
  obtain ⟨hconc, hcom₁, hextra⟩ := h36 L₁ h₁
  obtain ⟨-, hcom₂, -⟩ := h36 L₂ h₂
  have hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype := by
    have h := A37.commutator_le_oddCoreOf h₁ h₂ hne (A37.quasisimple_quotient_oddCore hcom₁)
      (A37.quasisimple_quotient_oddCore hcom₂) hL₂N
    rwa [A37.oddCoreOf, ← hcom₁.1] at h
  rcases hconc with hcomp | h3 | h4
  · exact A37.commutator_eq_bot_of_quasisimple hcomp.1 hcom₁ hc
  · exact A37.commutator_eq_bot_of_extra hL₂N hc (A37.fitting_ne_top hcom₁)
      (hextra (Or.inl h3))
  · exact A37.commutator_eq_bot_of_extra hL₂N hc (A37.fitting_ne_top hcom₁)
      (hextra (Or.inr h4))

theorem a37_of_a36Cat {G : Type} [Group G] [Finite G] (h36 : A36StatementCat G) :
    A37Statement G :=
  a37_of_core fun L hL => (h36 L hL).core

theorem a37ForSQTKCat_of_core (h36 : A36CoreForSQTKCat) : A37ForSQTKCat := fun Q _ hQ => by
  have := hQ.finite
  exact a37_of_core (h36 Q hQ)

theorem a37ForSQTKCat_of_a36 (h36 : A36ForSQTKCat) : A37ForSQTKCat :=
  a37ForSQTKCat_of_core h36.core

section Ambient

variable {G : Type} [Group G] [Finite G]

end Ambient

end CFSG.QuasithinUnique.Vol2Native

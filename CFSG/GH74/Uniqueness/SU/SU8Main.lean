module

public import CFSG.GH74.Uniqueness.SU.SU8Lem205
public import CFSG.GH74.Uniqueness.SU.SU0SUS

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.Bender CFSG.GH74.Uniqueness.SU.SU8.Setup

@[expose] def NoUnitaryStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    center ↥(hbarImage (centralizer ({z} : Set G)) L) = ⊥ →
      ¬ ∃ e, BenderType ↥(hbarImage (centralizer ({z} : Set G)) L) 2 3 e

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S L A : Subgroup G}

omit [Finite G] in
theorem Out203.benderLinear (o : Out203 z S L A)
    (hU : ¬ ∃ e, BenderType ↥(hbarImage (Hz z) L) 2 3 e) :
    BenderType ↥(hbarImage (Hz z) L) 2 1 1 := by
  obtain ⟨i, e, h⟩ := o.bender
  rcases h.cases' with ⟨hi, he, -⟩ | ⟨hi, -, a, ha, hn⟩ | ⟨hi, he, -⟩
  · subst hi he
    exact h
  · omega
  · subst hi
    exact absurd ⟨e, h⟩ hU

theorem isL24_of_benderLinear {K : Type} [Group K] (h : BenderType K 2 1 1) : IsL24 K := by
  generalize hn : 2 = n at h
  cases h with
  | linear m hm e =>
    subst hn
    exact CFSG.GH74.GLS.lieModel_psl_two_two_two_of_mulEquiv e

end Main

theorem prop201_of
    (h202 : Lemma202Stmt) (hU : NoUnitaryStmt) : Prop201Stmt := by
  intro G _ _ z S L A hyp
  have hZ := h202 G z S L A hyp
  have o := out203 hyp hZ
  have h := o.benderLinear (hU G z S L A hyp hZ)
  obtain ⟨e⟩ := L205.lemma205_of_lin hyp hZ h
  refine ⟨⟨↥(hbarImage (centralizer ({z} : Set G)) L), inferInstance, isL24_of_benderLinear h,
    ⟨e⟩⟩, o.order, fun hO => ⟨↥(hbarImage (centralizer ({z} : Set G)) L), inferInstance,
    isL24_of_benderLinear h, ⟨?_⟩⟩⟩
  have hbot : (⊥ : Subgroup ↥(centralizer ({z} : Set G))) =
      pPrimeCore 2 ↥(centralizer ({z} : Set G)) := hO.symm
  exact ((QuotientGroup.quotientBot (G := ↥(centralizer ({z} : Set G)))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot)).trans e

end CFSG.GH74.Uniqueness.SU.SU8

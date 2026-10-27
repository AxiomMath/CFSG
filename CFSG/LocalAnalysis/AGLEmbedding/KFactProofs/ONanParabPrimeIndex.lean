module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeMult
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank

structure ParabInputs : Prop where
  psu_four : ∀ {Y : Type} [Group Y] [Finite Y] {n f : ℕ},
    StatedClassicalModel Y .PSU n 2 f → 2 ≤ f → ParabCore Y (2 ^ f)
  psl_two : ∀ {Y : Type} [Group Y] [Finite Y] {n : ℕ},
    StatedClassicalModel Y .PSL n 2 1 → ParabCore Y 2
  psu_two : ∀ {Y : Type} [Group Y] [Finite Y] {n : ℕ},
    StatedClassicalModel Y .PSU n 2 1 → ParabCore Y 2
  psp_two : ∀ {Y : Type} [Group Y] [Finite Y] {n : ℕ},
    StatedClassicalModel Y .PSp n 2 1 → ParabCore Y 2
  pomegaPlus_two : ∀ {Y : Type} [Group Y] [Finite Y] {n : ℕ},
    StatedClassicalModel Y .POmegaPlus n 2 1 → ParabCore Y 2
  pomegaMinus_two : ∀ {Y : Type} [Group Y] [Finite Y] {n : ℕ},
    StatedClassicalModel Y .POmegaMinus n 2 1 → ParabCore Y 2

@[expose] def ParabData (Y : Type) [Group Y] : Prop :=
  ∃ q : ℕ, ParabCore (Y ⧸ Subgroup.center Y) q ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (Subgroup.center Y) → p ∣ q ^ 2 - 1

section Classical

variable {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}

theorem parabCore_of_classicalModel_four (I : ParabInputs)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hf : 2 ≤ f)
    (h : StatedClassicalModel X t n 2 f) : ParabCore X (2 ^ f) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact parabCore_of_model_psl h hf
  · exact I.psu_four h hf
  · exact parabCore_of_model_psp h hf
  · exact parabCore_of_model_pomegaPlus h hf
  · exact parabCore_of_model_pomegaMinus h hf

theorem parabCore_of_classicalModel_two (I : ParabInputs)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : StatedClassicalModel X t n 2 1) : ParabCore X 2 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact I.psl_two h
  · exact I.psu_two h
  · exact I.psp_two h
  · exact I.pomegaPlus_two h
  · exact I.pomegaMinus_two h

theorem parabCore_of_classicalModel (I : ParabInputs)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hf : 1 ≤ f)
    (h : StatedClassicalModel X t n 2 f) : ParabCore X (2 ^ f) := by
  rcases Nat.lt_or_ge 1 f with hf2 | hf1
  · exact parabCore_of_classicalModel_four I ht hf2 h
  · obtain rfl : f = 1 := by omega
    simpa using parabCore_of_classicalModel_two I ht h

theorem parabData_of_classicalModel (I : ParabInputs) (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : StatedClassicalModel (Y ⧸ Subgroup.center Y) t n 2 f) : ParabData Y := by
  have hf : 1 ≤ f := h.1.2.1
  refine ⟨2 ^ f, parabCore_of_classicalModel I ht hf h, fun p hp hp5 hpZ => ?_⟩
  exact dvd_sq_sub_one_of_dvd_card_center hGA hY (MulEquiv.refl _)
    (by rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp) hf ⟨h.1, Or.inl h⟩ hp hp5 hpZ

end Classical

end CFSG.AGLEmbedding.ParabPrime

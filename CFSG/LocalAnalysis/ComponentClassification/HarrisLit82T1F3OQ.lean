module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQExc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQRee
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQLin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQUni
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQOrth
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint
open scoped MatrixGroups

namespace F3FG

theorem lieModel_classical {S : Type} [Group S] {τ : StatedLieTag} {n p f : ℕ}
    (ht : τ ∈ classicalTags) (h : LieModel S τ n p f) : StatedClassicalModel S τ n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem lieModel_exceptional {S : Type} [Group S] {τ : StatedLieTag} {n p f : ℕ}
    (ht : τ ∈ chevalleyExceptionalTags) (h : LieModel S τ n p f) :
    ChevalleyExceptionalModel S τ p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem lieModel_reeTits {S : Type} [Group S] {τ : StatedLieTag} {n p f : ℕ}
    (ht : τ ∈ reeTitsTags) (h : LieModel S τ n p f) : ReeTitsModel S τ p f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h ht).2

theorem false_of_lieModel_twistedB2 {S : Type} [Group S] {n p f : ℕ} (hp : p ≠ 2)
    (h : LieModel S .twistedB2 n p f) : False := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact hp h.1

theorem OutNoA4.of_quasisimple {X S : Type} [Group X] [Group S] (hX : IsQuasisimple X)
    (e : X ⧸ center X ≃* S) (h : OutNoA4 S) : OutNoA4 X := by
  have : Group.IsPerfect X := hX.1
  exact OutNoA4.of_centerQuotient (OutNoA4.of_mulEquiv e.symm h)

section Certificates


theorem outNoA4_of_lieModel_three {S : Type} [Group S] [Finite S] {τ : StatedLieTag} {n f : ℕ}
    (hm : LieModel S τ n 3 f) (hPSL : ∀ f : ℕ, ¬ LieModel S .PSL 2 3 f)
    (hD4 : ∀ f : ℕ, ¬ LieModel S .POmegaPlus 4 3 f)
    (hres : ¬((τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ 3 ∣ f)) :
    OutNoA4 S := by
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  cases τ with
  | PSL =>
    have hn : 2 ≤ n := (lieModel_classical (by decide) hm).1.2.2.1
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · exact (hPSL f hm).elim
    · exact outNoA4_of_lieModel_PSL h3 hm
  | PSU => exact outNoA4_of_statedClassicalModel_PSU (lieModel_classical (by decide) hm)
  | PSp => exact outNoA4_of_statedClassicalModel_PSp h32 (lieModel_classical (by decide) hm)
  | POmegaOdd =>
    exact outNoA4_of_statedClassicalModel_orth (.inl rfl) h32 (fun h => by cases h.1)
      (fun h3 => hres ⟨.inl rfl, h3⟩) (lieModel_classical (by decide) hm)
  | POmegaPlus =>
    exact outNoA4_of_statedClassicalModel_orth (.inr (.inl rfl)) h32
      (fun h => hD4 f (h.2 ▸ hm)) (fun h3 => hres ⟨.inr (.inl rfl), h3⟩)
      (lieModel_classical (by decide) hm)
  | POmegaMinus =>
    exact outNoA4_of_statedClassicalModel_orth (.inr (.inr rfl)) h32 (fun h => by cases h.1)
      (fun h3 => hres ⟨.inr (.inr rfl), h3⟩) (lieModel_classical (by decide) hm)
  | G2 => exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | F4 => exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | E6 => exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | E7 => exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | E8 => exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | twistedE6 =>
    exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | trialityD4 =>
    exact outNoA4_of_chevalleyExceptionalModel (lieModel_exceptional (by decide) hm) h32
  | twistedG2 => exact outNoA4_of_reeTitsModel_twistedG2 (lieModel_reeTits (by decide) hm)
  | twistedB2 => exact (false_of_lieModel_twistedB2 h32 hm).elim
  | twistedF4 => exact absurd (lieModel_reeTits (by decide) hm).1.2.2.2.1 h32
  | Tits => exact absurd (lieModel_reeTits (by decide) hm).1.2.2.2.1 h32

theorem harris82OutQuatThree_of_orth
    (hO : Harris82OutQuatThreeOrth) : Harris82OutQuatThree := by
  intro S _ hS X _ _ hX hXS R φ hφ
  obtain ⟨e⟩ := hXS
  have : Finite S := Finite.of_equiv _ e.toEquiv
  rcases hS with ⟨⟨τ, n, f, hm⟩, hPSL, hD4⟩ | ⟨⟨eM⟩⟩
  · by_cases hres : (τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ 3 ∣ f
    · exact hO S τ n f hres.1 hres.2 hm hPSL hD4 X hX ⟨e⟩ R φ hφ
    · exact OutNoA4.of_quasisimple hX e (outNoA4_of_lieModel_three hm hPSL hD4 hres) R φ hφ
  · exact OutNoA4.of_quasisimple hX e (outNoA4_of_isSporadic_m11 ⟨eM⟩) R φ hφ

end Certificates

end F3FG

end CFSG.ComponentClassification.HarrisLit.T1

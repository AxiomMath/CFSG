module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A02

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool

open CFSG
open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL

section Tool

variable {X : Type} [Group X] [Finite X] {Λ : Set (Subgroup X)}

theorem orth_ne_g2d4 {d : ℕ} {ε : Bool} {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}
    (h : IsOrthTag d ε tag k) : tag ≠ .G2 ∧ tag ≠ .trialityD4 := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ |
    ⟨-, -, -, rfl, -⟩ <;> exact ⟨by decide, by decide⟩

theorem exists_model (hΛ : Q3T7M.HM Λ) (hgen : omegaGen Λ = ⊤) (D : OmegaLieU 3 1 Λ)
    (hc : D.card = 1) (i : Fin D.card) {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}
    (hcis : CompIs 3 1 (D.kind i) tag k) :
    ∃ e : ℕ, Nonempty (Q3T8.Asc77.Ih8Model Λ tag k e) := by
  obtain ⟨e, he, hft, hadm, hkind⟩ := hcis
  exact ⟨e, ⟨Q3T7.toIh8ModelSect D hΛ hgen hc i hft hadm he hkind⟩⟩

theorem smallRows_of_disconnected {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e d : ℕ}
    {ε : Bool} (hΛ : Q3T7M.HM Λ) (M : Q3T8.Asc77.Ih8Model Λ tag k e) (hne : Λ.Nonempty)
    (hdisc : ¬ DConnected Λ) (hort : IsOrthTag d ε tag k) :
    (tag = .PSp ∧ k = 2) ∨ (tag = .PSL ∧ k = 4) ∨ (tag = .PSU ∧ k = 4) ∨
      (tag = .POmegaOdd ∧ k = 3) ∨ (tag = .POmegaPlus ∧ k = 4) ∨ (tag = .POmegaMinus ∧ k = 4) := by
  obtain ⟨hG2, hD4⟩ := orth_ne_g2d4 hort
  rcases Uniform.tag_casesU (by norm_num) M.isFundTag M.admissible hG2 hD4 with hconn | hsmall
  · exact absurd (Uniform.dConnected_of_connectedU M hΛ hne hG2 hD4 hconn) hdisc
  rcases hort with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, hn⟩ |
    ⟨-, -, -, rfl, hn⟩ | ⟨-, -, -, rfl, hn⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · simp [Asc77.SmallModel] at hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hsmall⟩)))
  · simp [Asc77.SmallModel] at hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hsmall⟩))))
  · simp [Asc77.SmallModel] at hsmall
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hsmall⟩))))

theorem dimOfTwinFrame (hΛ : Q3T7M.HM Λ) (hgen : omegaGen Λ = ⊤) (D : OmegaLieU 3 1 Λ)
    (hc : D.card = 1) (i : Fin D.card) {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k d : ℕ}
    {ε : Bool} (hort : IsOrthTag d ε tag k) (hcis : CompIs 3 1 (D.kind i) tag k)
    (hdisc : ¬ DConnected Λ) {A A' B : Subgroup X} {z u₁ u₂ τ ε₀ : X}
    (h : TwinFrame Λ A A' B z u₁ u₂ τ ε₀) : d = 6 ∧ ε = false := by
  obtain ⟨e, ⟨M⟩⟩ := exists_model hΛ hgen D hc i hcis
  have := Q3T8.Asc77.twinFrame_tag_of_model Q3T8.Asc77.twinSquareFact3_proved hΛ M hdisc h
  rcases this with ⟨-, -, h3⟩ | ⟨rfl, rfl, -⟩
  · norm_num at h3
  · rcases hort with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h6, hε, -, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ |
      ⟨-, -, -, h, -⟩ <;> first | exact absurd h (by decide) | exact ⟨h6, hε⟩

theorem dimOfE4Frame (hΛ : Q3T7M.HM Λ) (hgen : omegaGen Λ = ⊤) (D : OmegaLieU 3 1 Λ)
    (hc : D.card = 1) (i : Fin D.card) {tag : CFSG.Assembly.LowTwoRank.StatedLieTag} {k d : ℕ}
    {ε : Bool} (hort : IsOrthTag d ε tag k) (hcis : CompIs 3 1 (D.kind i) tag k)
    (hdisc : ¬ DConnected Λ) {A A' : Subgroup X} {z a₀ b₀ w : X} (hA : A ∈ Λ) (hA' : A' ∈ Λ)
    (hne : A ≠ A') (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z) (ha₀ : a₀ ∈ A)
    (hb₀ : b₀ ∈ A') (ha₀sq : a₀ * a₀ = z) (hb₀sq : b₀ * b₀ = z)
    (hw : w = a₀ * b₀ ∨ w = a₀⁻¹ * b₀) (hF : ∀ L ∈ Λ, ∃ m ∈ L, w * m ≠ m * w) :
    d = 5 ∨ (d = 6 ∧ ε = true) := by
  obtain ⟨e, ⟨M⟩⟩ := exists_model hΛ hgen D hc i hcis
  have hsix := smallRows_of_disconnected hΛ M ⟨A, hA⟩ hdisc hort
  have := Q3T8.Asc77.T7L.e4Tag_of_model Q3T8.Asc77.twinCentralFact3_proved hΛ M hsix hA hA' hne
    hzA hzA' ha₀ hb₀ ha₀sq hb₀sq hw hF
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, h⟩
  · rcases hort with ⟨h5, -, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ |
      ⟨-, -, -, h, -⟩ <;> first | exact Or.inl h5 | exact absurd h (by decide)
  · rcases hort with ⟨-, h, -⟩ | ⟨h6, hε, -, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, -, h, -⟩ |
      ⟨-, -, -, h, -⟩ <;> first | exact Or.inr ⟨h6, hε⟩ | exact absurd h (by decide)
  · norm_num at h

end Tool

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimTool

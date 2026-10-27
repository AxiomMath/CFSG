module

public import CFSG.Blueprint.SourceClassicalTransportSymplectic
public import CFSG.Blueprint.SourceClassicalTransportUnitary
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverFiveModel

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_coe glCongr_symm_coe glCongr_statedScalars glCongr_statedSU statedProjCongr)

export CFSG.Adapters.RankTwoModelTransports (glCongr_statedSL glCongr_statedSp)

section FieldChange

variable {K L : Type} [Field K] [Field L] (φ : K ≃+* L)

theorem glCongr_matrixIsometry {ι : Type} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι K) :
    (matrixIsometry G).map (glCongr (ι := ι) φ).toMonoidHom = matrixIsometry (G.map φ) := by
  ext B
  rw [Subgroup.mem_map_equiv, mem_matrixIsometry, mem_matrixIsometry, glCongr_symm_coe]
  constructor
  · intro h
    have := congrArg (fun M : Matrix ι ι K => M.map φ) h
    simp only [Matrix.map_mul, transpose_map, Matrix.map_map] at this
    rwa [show (⇑φ ∘ ⇑φ.symm) = id from funext φ.apply_symm_apply, Matrix.map_id] at this
  · intro h
    have := congrArg (fun M : Matrix ι ι L => M.map φ.symm) h
    simp only [Matrix.map_mul, transpose_map, Matrix.map_map] at this
    rwa [show (⇑φ.symm ∘ ⇑φ) = id from funext φ.symm_apply_apply, Matrix.map_id] at this

theorem statedQuadPlus_map (n : ℕ) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n L (φ ∘ v) = φ (StatedQuadPlus n K v) := by
  simp only [StatedQuadPlus, Function.comp_apply, map_sum, map_mul]

theorem statedQuadOdd_map (n : ℕ) (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n L (φ ∘ v) = φ (StatedQuadOdd n K v) := by
  simp only [StatedQuadOdd, Function.comp_apply, map_add, map_sum, map_mul, map_pow]

theorem irreducible_quadratic_map {b c : K} (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ s : L, s ^ 2 + φ b * s + φ c ≠ 0 := by
  intro s hs
  apply h (φ.symm s)
  apply φ.injective
  rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, hs, map_zero]

end FieldChange

noncomputable def ringEquivOfNatCard {K L : Type} [Field K] [Field L] [Finite K] [Finite L]
    (h : Nat.card K = Nat.card L) : K ≃+* L := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  exact FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h)

theorem nonempty_mulEquiv_of_statedClassicalModel {X Y : Type} [Group X] [Group Y]
    {t : StatedLieTag} {n p f : ℕ} (hX : StatedClassicalModel X t n p f)
    (hY : StatedClassicalModel Y t n p f) : Nonempty (X ≃* Y) := by
  cases t
  case PSL =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSL φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case PSU =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSU φ n (p ^ f))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case PSp =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSp φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaOdd =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ)
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
        (statedQuadOdd_map φ n)) (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaPlus =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ)
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
        (statedQuadPlus_map φ n)) (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaMinus =>
    obtain ⟨hadm, K₁, _, _, hc₁, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, b₂, c₂, hirr₂, ⟨e₂⟩⟩ := hY
    have hn : 1 ≤ n := by have := hadm.2.2; omega
    let φ := ringEquivOfNatCard (hc₁.trans hc₂.symm)
    obtain ⟨e₃⟩ := nonempty_statedOmegaMinus_equiv hn (irreducible_quadratic_map φ hirr₁) hirr₂
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ)
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
        (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.statedQuadMinus_comp φ rfl
          rfl)) (glCongr_statedScalars φ)).trans (e₃.trans e₂.symm))⟩
  all_goals exact hX.2.elim

theorem even_native_classical_source_model_transport (X : Type) [Group X] (t : StatedLieTag)
    (n p f : ℕ) :
    (StatedClassicalModel X t n p f ↔ SourceClassicalModel X t n p f) ∧
    (∀ (Y : Type) [Group Y], SourceClassicalModel X t n p f → SourceClassicalModel Y t n p f →
      Nonempty (X ≃* Y)) ∧
    (∀ (Y : Type) [Group Y], SourceClassicalModel X t n p f → StatedClassicalModel Y t n p f →
      Nonempty (X ≃* Y)) := by
  have hiff : ∀ (Z : Type) [Group Z],
      StatedClassicalModel Z t n p f ↔ SourceClassicalModel Z t n p f := by
    intro Z _
    cases t
    case PSL => exact ⟨sourceClassicalModel_of_stated_PSL, stated_of_sourceClassicalModel_PSL⟩
    case PSU => exact ⟨sourceClassicalModel_of_stated_PSU, stated_of_sourceClassicalModel_PSU⟩
    case PSp => exact ⟨sourceClassicalModel_of_stated_PSp, stated_of_sourceClassicalModel_PSp⟩
    case POmegaOdd =>
      exact ⟨sourceClassicalModel_of_stated_POmegaOdd, stated_of_sourceClassicalModel_POmegaOdd⟩
    case POmegaPlus =>
      exact ⟨sourceClassicalModel_of_stated_POmegaPlus, stated_of_sourceClassicalModel_POmegaPlus⟩
    case POmegaMinus =>
      exact ⟨sourceClassicalModel_of_stated_POmegaMinus,
        stated_of_sourceClassicalModel_POmegaMinus⟩
    all_goals
      refine ⟨fun h => h.2.elim, fun h => ?_⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨⟩⟩ := h
  refine ⟨hiff X, fun Y _ hX hY => ?_, fun Y _ hX hY => ?_⟩
  · exact nonempty_mulEquiv_of_statedClassicalModel ((hiff X).mpr hX) ((hiff Y).mpr hY)
  · exact nonempty_mulEquiv_of_statedClassicalModel ((hiff X).mpr hX) hY

end CFSG.Blueprint.EvenSource

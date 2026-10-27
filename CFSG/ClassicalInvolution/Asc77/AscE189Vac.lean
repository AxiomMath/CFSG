module

public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p : ℕ} [Fact p.Prime]

theorem modelTwinClass_two_of_swap (t : StatedLieTag) (n e : ℕ)
    (hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {F₁ : Subgroup (ModelGrp p e t n)} (hF₁ : F₁ ∈ modelFund p e t n)
    {t₁ : ModelGrp p e t n} (h3 : conjSub t₁ F₁ ≠ F₁) (h4 : Commutes F₁ (conjSub t₁ F₁))
    (h5 : ∀ S : Subgroup (ModelGrp p e t n), (∃ y, S = conjSub y F₁) →
      ((S = F₁ ∨ Commutes S F₁) ↔ (S = conjSub t₁ F₁ ∨ Commutes S (conjSub t₁ F₁)))) :
    ModelTwinClass p t n e 2 := by
  have hsc := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass t n p e Fact.out hfund
    hadm hG2 hD4
  refine ⟨![F₁, conjSub t₁ F₁], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hF₁
    · exact conjSub_mem_fundamentalSubgroups hF₁ t₁
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa using hij) h3.symm
    · exact absurd (by simpa using hij) h3
    · rfl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h4
    · exact fun x hx y hy => (h4 y hy x hx).symm
    · exact absurd rfl hij
  · intro i j S hS
    obtain ⟨y, hy⟩ := hsc F₁ hF₁ S hS
    have h6 := h5 S ⟨y, hy⟩
    fin_cases i <;> fin_cases j
    · exact Iff.rfl
    · exact h6
    · exact h6.symm
    · exact Iff.rfl

theorem e189ModelAt_of_noTwinRow (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) (t : StatedLieTag)
    (n : ℕ) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hnA1 : ¬ (t = .PSL ∧ n = 2)) (hrow : ¬ ShapeTable 2 t n)
    (hD : ¬ (t = .POmegaPlus ∧ n = 4)) : E189ModelAt p e t n := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 h2 h3 h4 h5
  exfalso
  have hT := modelTwinClass_two_of_swap t n e (by cases t <;> trivial) hadm hG2 hD4 hF₁ h3 h4 h5
  rcases mfTwin (p := p) (f := e) hp2 hq t n 2 hfund hG2 hD4 hadm hnA1 le_rfl hT with
    h | ⟨ht, hn, -⟩
  · exact hrow h
  · exact hD ⟨ht, hn⟩

theorem e189ModelAt_PSL_two {e : ℕ} (hadm : StatedLieAdmissible .PSL 2 p e) :
    E189ModelAt p e .PSL 2 := by
  intro N hN F₁ hF₁ z₁ hz₁ g h1 h2 h3 h4 h5
  exfalso
  apply h3
  have : F₁ = ⊤ :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e Fact.out hadm F₁ hF₁
  rw [this]
  exact conjSub_eq_self_of_mem (Subgroup.mem_top _)

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.GH74.GLS.IVK.Statements.Sec4d
public import CFSG.GH74.GLS.IVK.Statements.Sec9b
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abCh6
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47 CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
open scoped MatrixGroups

theorem finite_of_lieModel_G2 {M : Type} [Group M] {p f : ℕ}
    (h : LieModel M .G2 0 p f) : Finite M := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := untwisted_of_lieModel_G2 h
  have : Finite (ModGL Tag.G2 F) := finite_modGL
  exact Finite.of_equiv _ e.symm.toEquiv

theorem finite_of_lieModel_D4 {M : Type} [Group M] {p f : ℕ}
    (h : LieModel M .trialityD4 0 p f) : Finite M := by
  obtain ⟨F, _, _, _, σ, _, ⟨e⟩⟩ := twisted_of_lieModel_D4 h
  have : Finite (ModGL TwistTag.D4.tag F) := finite_modGL
  exact Finite.of_equiv _ e.symm.toEquiv

theorem exists_shape_of_isInvolutionCentralizerOfModel
    (h47 : IVK.IVK_4_7ab) {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .G2 ∨ t = .trialityD4) (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (h : IVK.IsInvolutionCentralizerOfModel X t p f) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂),
      ((t = .G2 ∧ Nat.card F₁ = p ^ f ∧ Nat.card F₂ = p ^ f) ∨
        (t = .trialityD4 ∧ Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f)) ∧
      Nonempty (Shape X F₁ F₂) := by
  obtain ⟨M, _, z', hM, hz', ⟨φ⟩⟩ := h
  rcases ht with rfl | rfl
  · have := finite_of_lieModel_G2 hM
    obtain ⟨K₁, K₂, F, hF, hFin, t', hcard, hcomm, -, -, hinter, hRem⟩ :=
      h47.1 M p f hp hp2 h5 hM z' hz'
    obtain ⟨S⟩ := Ch6Rem.exists_shape hRem hcomm hinter hz'
    exact ⟨F, F, hF, hF, hFin, hFin, Or.inl ⟨rfl, hcard, hcard⟩,
      ⟨S.mapEquiv ((MulEquiv.subgroupCongr hRem.gen).trans φ.symm)⟩⟩
  · have := finite_of_lieModel_D4 hM
    obtain ⟨K₁, K₂, F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, t', hcard₁, hcard₂, hcomm, -, -, hinter, hRem⟩ :=
      h47.2 M p f hp hp2 h5 hM z' hz'
    obtain ⟨S⟩ := Ch6Rem.exists_shape hRem hcomm hinter hz'
    exact ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, Or.inr ⟨rfl, hcard₁, hcard₂⟩,
      ⟨S.mapEquiv ((MulEquiv.subgroupCongr hRem.gen).trans φ.symm)⟩⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94

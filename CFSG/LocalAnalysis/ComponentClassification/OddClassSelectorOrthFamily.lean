module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrth

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem statedClassicalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) (h1 : t ∉ chevalleyExceptionalTags) (h2 : t ∉ reeTitsTags)
    (h3 : t ≠ .twistedB2) : StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by revert h1 h2 h3; cases t <;> decide)

theorem orth_family_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWs : IsSimpleGroup W) (hWnab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hstd : CFSG.IsStandardSubgroup L) (hs : SmallSource L) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hW : (∃ n, 3 ≤ n ∧ LieModel W .POmegaOdd n p f) ∨
      (∃ n, 4 ≤ n ∧ LieModel W .POmegaPlus n p f) ∨
      (∃ n, 5 ≤ n ∧ LieModel W .POmegaMinus n p f)) : False := by
  classical
  have hLCW := LocalAnalysis.ComponentInitial.isComponentOf_of_le hL (le_inf hLW hL.1)
    inf_le_right
  rcases hW with ⟨n, hn, hM⟩ | ⟨n, hn, hM⟩ | ⟨n, hn, hM⟩
  · have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
      (by simp [reeTitsTags]) (by decide)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_odd h K hK e
    exact orth_socle_false hWs hWnab hCW ha hLCW hstd hs hp hp2 hf hK (by omega) hnd
      (fun h8 => by omega)
      (odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl) h K hK e)
      (coordinateOddWitnessEquiv K e)
  · have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
      (by simp [reeTitsTags]) (by decide)
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus h K hK e
    refine orth_socle_false hWs hWnab hCW ha hLCW hstd hs hp hp2 hf hK (by omega) hnd
      (fun h8 => ?_)
      (odd_orthogonal_involution_semilinear_representation .POmegaPlus (Or.inr (Or.inl rfl)) h
        K hK e)
      (coordinatePlusWitnessEquiv K e)
    obtain ⟨U, hU, hUQ⟩ := exists_totallySingular_coordinateQuadPlus n hnd
    exact ⟨U, by omega, hUQ⟩
  · have h := statedClassicalModel_of_lieModel hM (by simp [chevalleyExceptionalTags])
      (by simp [reeTitsTags]) (by decide)
    have hn1 : 1 ≤ n := by omega
    obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
    obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    exact orth_socle_false hWs hWnab hCW ha hLCW hstd hs hp hp2 hf hK (by omega) hnd
      (fun h8 => by omega)
      (odd_orthogonal_involution_semilinear_representation .POmegaMinus (Or.inr (Or.inr rfl))
        h hn1 K hK b c hirr e)
      (coordinateMinusWitnessEquiv K hn1 b c e)

end CFSG.ComponentClassification.OddClassSelector

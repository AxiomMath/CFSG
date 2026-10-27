module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOModel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafExc

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
  (odd_orthogonal_involutions_conjugate_into_semilinear_image)
open Orth516

theorem Orth516.false_of_iso_model
    {S : Type} [Group S] {σ : MulAut S} {P J : Subgroup S} {t : S} (hC : LeafConf σ P t J)
    (hPq : IsQuasisimple P) {p f : ℕ} (hf : 1 ≤ f) (hPm : L4U4Type P p f)
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hFc : Nat.card F = p ^ e) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) F}
    (hRs : (R : Matrix (Fin d) (Fin d) F)ᵀ = R) (hker : OKer (oQ R))
    (θ : S ≃* StatedProj (matrixDerived (oQ R)))
    (hconj : ∀ α : MulAut (StatedProj (matrixDerived (oQ R))), α * α = 1 →
      ∃ (β : MulAut (StatedProj (matrixDerived (oQ R)))) (g : similarityPairs (oQ R)),
        β⁻¹ * α * β = oκ _ g) : False := by
  set α := MulAut.congr θ σ with hαdef
  have hα2 : α * α = 1 := by rw [hαdef, ← map_mul, hC.sq, map_one]
  obtain ⟨β, g, hg⟩ := hconj α hα2
  set θ' := θ.trans β.symm with hθ'
  have hcongr : MulAut.congr θ' σ = oκ _ g := by
    rw [← hg]
    ext y
    change β.symm (θ (σ (θ.symm (β y)))) = β⁻¹ (α (β y))
    rw [hαdef]
    rfl
  have h' := hC.map θ'
  rw [hcongr] at h'
  have hPq' : IsQuasisimple (P.map θ'.toMonoidHom) :=
    LocalCores.isQuasisimple_of_mulEquiv (P.equivMapOfInjective θ'.toMonoidHom θ'.injective) hPq
  have hPm' : L4U4Type (P.map θ'.toMonoidHom) p f :=
    hPm.of_mulEquiv (P.equivMapOfInjective θ'.toMonoidHom θ'.injective).symm
  exact false_of_model_conf hF hp he hFc hd hRs hker h' hPq' hf hPm'

theorem cf516OrthRow :
    CF516OrthRow := by
  intro S _ _ τ n r e hr hr2 hτ hadm hm hs hna _ σ P hP p f hp hp2 hf hPm t ht ht2 J hJC hJ hJm
    hσJ hσO JB hJB _ hJBs
  have : IsSimpleGroup S := hs
  have hQ : FixedTwoComponentsQuasisimple S :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna ⟨τ, n, r, e, hr, hr2, hadm, hm⟩
  have hC := leafConf_of_leaf hQ hna hP ht ht2 hJC hJ hp2 hJm hσJ hσO hJB hJBs
  obtain ⟨hct, hJc, -, hJm'⟩ := Pump516.leaf_J_data hQ hna ht2 hJC hJ hJm
  have hfam : GLS3OddFamilyInput τ := by
    rcases hτ with rfl | rfl | rfl
    · exact gls3OddFamilyInput_POmegaOdd oddOmegaOddLinearInput_holds oddOmegaOddFieldInput_holds
    · exact gls3OddFamilyInput_POmegaPlus oddOmegaPlusLinearInput_holds
        oddOmegaPlusFieldInput_holds
    · exact gls3OddFamilyInput_POmegaMinus oddOmegaMinusLinearInput_holds
        oddOmegaMinusFieldInput_holds
  have hrp : r = p := by
    rcases hfam S n r e hr hr2 hadm hm _ hct _ hJc with ⟨τ', n', f', -, h⟩ | ⟨-, -, hnot, -⟩
    · exact Pump516.char_eq_of_psl_two_sq hp hp2 hf hr2 hJm' h
    · exact absurd ⟨t, rfl⟩ hnot
  subst hrp
  have hσ1 : σ ≠ 1 := hP.ne_one
  obtain ⟨hσ2', hPF, hPp, -⟩ := hP
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => hσ2' y
  obtain ⟨hPc, -, ⟨eP⟩⟩ := Pump516.fixed_component_data hQ hσ2 hσ1 hPF hPp
    (Pump516.isSimpleGroup_of_l4u4 hPm)
  have hPq : IsQuasisimple P :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hPF) hPc.1
  have hPm' : L4U4Type P r f := by
    have h1 : L4U4Type ↥(P.subgroupOf (fixedSubgroup σ)) r f := by
      rcases hPm with ⟨h3, h⟩ | ⟨h1, h⟩
      · exact Or.inl ⟨h3, Pump516.lieModel_center_of_fixed eP h⟩
      · exact Or.inr ⟨h1, Pump516.lieModel_center_of_fixed eP h⟩
    exact h1.of_mulEquiv (subgroupOfEquivOfLe hPF).symm
  have hfield : ∀ (F : Type) [Field F] [Finite F], Nat.card F = r ^ e → ringChar F ≠ 2 := by
    intro F _ _ hFc
    have : Fintype F := Fintype.ofFinite F
    have : Fact r.Prime := ⟨hr⟩
    have : CharP F r := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    rw [ringChar.eq F r]
    exact hr2
  rcases hτ with rfl | rfl | rfl
  ·
    rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, he, hn, -⟩, F, _, _, hFc, ⟨ε⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
      (regular_coordinateQuadOdd n F h2 hn).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinateOdd hmod F hFc ε).transport 1 1 hS₁
    have hconj := X10Orth.exists_conj_kappa hS₁ fun α hα =>
      odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaOdd (Or.inl rfl) hmod F
        hFc ε α hα
    exact false_of_iso_model hC hPq hf hPm' hF hr he hFc (by omega) hRs hker
      ((coordinateOddWitnessEquiv F ε).trans (oTransport 1 1 hS₁)) hconj
  ·
    rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, he, hn⟩, F, _, _, hFc, ⟨ε⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
      (regular_coordinateQuadPlus n F (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinatePlus hmod F hFc ε).transport 1 1 hS₁
    have hconj := X10Orth.exists_conj_kappa hS₁ fun α hα =>
      (odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaPlus
        (Or.inr (Or.inl rfl)) hmod F hFc ε).1 α hα
    exact false_of_iso_model hC hPq hf hPm' hF hr he hFc (by omega) hRs hker
      ((coordinatePlusWitnessEquiv F ε).trans (oTransport 1 1 hS₁)) hconj
  ·
    rcases hm with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, he, hn⟩, F, _, _, hFc, b, c, hirr, ⟨ε⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hn1 : 1 ≤ n := by omega
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
      (regular_coordinateQuadMinus n F b c hn hirr).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinateMinus hmod F hFc b c hirr ε).transport 1 1 hS₁
    have hconj := X10Orth.exists_conj_kappa hS₁ fun α hα =>
      odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaMinus
        (Or.inr (Or.inr rfl)) hmod hn1 F hFc b c hirr ε α hα
    exact false_of_iso_model hC hPq hf hPm' hF hr he hFc (by omega) hRs hker
      ((coordinateMinusWitnessEquiv F hn1 b c ε).trans (oTransport 1 1 hS₁)) hconj

end CFSG.ComponentClassification.GSThmB

module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthModel
import CFSG.LieType.SeitzGeneration.OuterOrthThreeGates
import CFSG.LieType.SeitzGeneration.OuterOrthThreeSubfield
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThreeAux.SympPrimeSubfieldOdd
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLift
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (FieldCoreAt isQuasisimple_of_simple_nonabelian fieldCoreAt_of_conj)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)

section Fixed

theorem fixedData_odd_three {n ℓ f : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n ℓ (f / 3))
    (hpℓ : 3 ≠ ℓ) (hpf : 3 ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / 3))
    (g : similarityPairs (coordinateQuadOdd n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    FixedData 3 (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : 3 * e / 3 = e := Nat.mul_div_cancel_left e (by norm_num)
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * 3) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaOdd (Or.inl rfl) n ℓ e
      3 hadm Nat.prime_three (by norm_num) hpℓ K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, hord, hfixiff, hJN, hJn, hquot, -, -, hfixJ, -⟩ := hconc
  have := hsimple
  exact ⟨hord, _, _, hfixiff, hJN, hJn, @hquot, isQuasisimple_of_simple_nonabelian
    (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), hfixJ⟩

theorem fixedData_plus_three {n ℓ f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n ℓ (f / 3))
    (hpℓ : 3 ≠ ℓ) (hpf : 3 ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / 3))
    (g : similarityPairs (coordinateQuadPlus n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    FixedData 3 (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : 3 * e / 3 = e := Nat.mul_div_cancel_left e (by norm_num)
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * 3) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ e 3 hadm Nat.prime_three (by norm_num) hpℓ K
      (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, hord, hfixiff, hJN, hJn, hquot, -, -, hfixJ, -⟩ := hconc
  have := hsimple
  exact ⟨hord, _, _, hfixiff, hJN, hJn, @hquot, isQuasisimple_of_simple_nonabelian
    (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), hfixJ⟩

theorem fixedData_minus_three {n ℓ f : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n ℓ (f / 3))
    (hpℓ : 3 ≠ ℓ) (hpf : 3 ∣ f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / 3))
    (b c' : semilinearFixedSubfield σ)
    (hirr : ∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c' ≠ 0)
    (g : similarityPairs (coordinateQuadMinus n K hn (b : K) (c' : K))) (hl : g.val.left = 1)
    (hr : g.val.right = σ) :
    FixedData 3 (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : 3 * e / 3 = e := Nat.mul_div_cancel_left e (by norm_num)
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * 3) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ e 3 hadm Nat.prime_three (by norm_num) hpℓ hn K
      (semilinearFixedSubfield σ) hcard hK' σ hσ hσk b c' hirr
  have hg : g = fieldPair (coordinateQuadMinus n K hn (b : K) (c' : K)) σ
      (coordinateQuadMinus_fieldAut (semilinearFixedSubfield σ) n hn hσk b c') :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, hord, hfixiff, hJN, hJn, hquot, -, -, hfixJ, -⟩ := hconc
  have := hsimple
  exact ⟨hord, _, _, hfixiff, hJN, hJn, @hquot, isQuasisimple_of_simple_nonabelian
    (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), hfixJ⟩

end Fixed

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem mem_inner_of_mem_D_three [Finite (matrixProjectiveDerived Q)] (hg : OrthogonalGates Q f)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ 3 = 1) : β ∈ innerAut (matrixProjectiveDerived Q) := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    ComponentClassification.OuterAutomorphisms.inner_normal _
  exact KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk Nat.prime_three
    (by norm_num) hβD hβp

theorem exists_inner_of_top_three [Finite (matrixProjectiveDerived Q)] (hg : OrthogonalGates Q f)
    (htop : matrixProjectiveImage Q = ⊤)
    (hinj : Function.Injective (MulAut.conj : matrixProjectiveDerived Q →*
      MulAut (matrixProjectiveDerived Q))) :
    ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)), IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      ¬ A ≤ innerAut (matrixProjectiveDerived Q) →
      ∃ y ∈ A, y ∈ innerAut (matrixProjectiveDerived Q) ∧ y ≠ 1 := by
  intro A hA hAc _
  have hel : CFSG.IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
  obtain ⟨g, hg1, hgA⟩ := exists_conj_mem_of_plane_of_top hg htop Nat.prime_three (by norm_num) A
    hel hAc
  exact ⟨MulAut.conj g, hgA, ⟨g, rfl⟩, fun h1 => hg1 (hinj (h1.trans (map_one _).symm))⟩

end Gates

section Model

theorem outerFields_matrix_odd_three {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hpℓ : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadOdd n K))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadOdd n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)))) :
    OuterFields 3 (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd (Or.inl rfl)
    n ℓ f h K hK e
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := h.1
  have h2K : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  have htop := matrixProjectiveImage_eq_top_odd K n hn3 h2K
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadOdd n K))
    (linearConjugationHom (coordinateQuadOdd n K)).range
    (fun β _ => htop ▸ Subgroup.mem_top β)
    (fun β hβD hβp => mem_inner_of_mem_D_three hg hβD hβp)
    (exists_inner_of_top_three hg htop hinj) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f 3 h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp hp2 hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_odd_three hCM.1 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r) hy hy1 hyp
    hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerFields_matrix_plus_three {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hn4 : n ≠ 4) (hpℓ : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadPlus n K))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))) :
    OuterFields 3 (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  obtain ⟨hℓ, hf, hn4'⟩ := h.1
  have htop := matrixProjectiveImage_eq_top_plus K n (by omega)
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadPlus n K))
    (linearConjugationHom (coordinateQuadPlus n K)).range
    (fun β _ => htop ▸ Subgroup.mem_top β)
    (fun β hβD hβp => mem_inner_of_mem_D_three hg hβD hβp)
    (exists_inner_of_top_three hg htop hinj) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f 3 h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp hp2 hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_plus_three hCM.1 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r) hy hy1 hyp
    hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerFields_matrix_minus_three {G : Type} [Group G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn : 1 ≤ n) (hpℓ : 3 ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    [Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))) :
    OuterFields 3 (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  obtain ⟨hℓ, hf, hn4⟩ := h.1
  have htop := matrixProjectiveImage_eq_top_minus K n hn4 b c hirr
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (linearConjugationHom (coordinateQuadMinus n K hn b c)).range
    (fun β _ => htop ▸ Subgroup.mem_top β)
    (fun β hβD hβp => mem_inner_of_mem_D_three hg hβD hβp)
    (exists_inner_of_top_three hg htop hinj) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f 3 h hp hp2 hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp hp2 hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_minus_three hCM.1 hpℓ hpf hn K hK U.val.right hord' hcard' b' c' hirr' g' hg'l
      hg'r) hy hy1 hyp hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

end Model

section Symplectic

open CFSG.HardMathSupport.Timmesfeld.CrossChar (fixSub mem_fixSub)
open CFSG.RankThree.CASymplecticSubfield (subfieldFixedGroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)

theorem fieldCoreAt_fieldAut_sp_two_exc {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f)
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hexc : ℓ ^ (f / p) = 2)
    (hk : ∃ k ∈ subfieldFixedGroup K 2 σ, orderOf k = p) :
    FieldCoreAt p (fieldAut 2 K σ) := by
  classical
  obtain ⟨-, -, -, -, -, hJfix, -, -, hS6, hfixing, hzp, hzcard, -, hlast⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) hℓ hp hp2 hpℓ hf
      (le_refl 2) hK σ hσ
  obtain ⟨⟨e⟩, ⟨eT⟩, -⟩ := hS6 ⟨rfl, hexc⟩
  obtain ⟨-, hp35, -, -⟩ := hlast ⟨rfl, hexc⟩ hk
  set H₀ := subfieldFixedGroup K 2 σ with hH₀
  set T : Subgroup (StatedProj (StatedSp 2 K)) := ⁅H₀, H₀⁆ with hT
  have hδp : orderOf (fieldAut 2 K σ) = p := by rw [← Nat.card_zpowers, hzcard]
  have hTH : T ≤ H₀ :=
    Subgroup.commutator_le.2 fun a ha b hb =>
      H₀.mul_mem (H₀.mul_mem (H₀.mul_mem ha hb) (H₀.inv_mem ha)) (H₀.inv_mem hb)
  have hTF : T ≤ fixSub (fieldAut 2 K σ) := fun t ht => (hJfix t).1 (hTH ht)
  have hTn : ∀ f ∈ fixSub (fieldAut 2 K σ), ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    intro f hf t ht
    have hfH : f ∈ H₀ := (hJfix f).2 hf
    have hle : H₀.map (MulAut.conj f).toMonoidHom ≤ H₀ := by
      rintro _ ⟨a, ha, rfl⟩
      exact H₀.mul_mem (H₀.mul_mem hfH ha) (H₀.inv_mem hfH)
    have h1 : T.map (MulAut.conj f).toMonoidHom ≤ T := by
      rw [hT, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    exact h1 (Subgroup.mem_map_of_mem _ ht)
  have hAq : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    refine isQuasisimple_of_simple_nonabelian fun hc => ?_
    have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ :=
      eq_top_iff.2 fun a _ => Subgroup.mem_center_iff.2 fun b => hc b a
    rw [alternatingGroup.center_eq_bot (by simp)] at hcen
    exact bot_ne_top hcen
  have hTq : CFSG.IsQuasisimple T := CFSG.LocalCores.isQuasisimple_of_mulEquiv eT.symm hAq
  have hTcard : Nat.card T = 360 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hTp : ¬ Nat.Coprime p (Nat.card T) := by
    rw [hTcard]
    rcases hp35 with rfl | rfl <;> decide
  refine ⟨T, hTF, hTn, hTq, hTp, ?_⟩
  intro g hgp hgx hgT
  have hgH : ∀ h ∈ H₀, g h ∈ H₀ := by
    intro h hh
    rw [hJfix] at hh ⊢
    calc fieldAut 2 K σ (g h) = (fieldAut 2 K σ * g) h := rfl
      _ = (g * fieldAut 2 K σ) h := by rw [hgx]
      _ = g (fieldAut 2 K σ h) := rfl
      _ = g h := by rw [hh]
  have h2 : (commutator ↥H₀).map e.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
      ← commutator_def, alternatingGroup.commutator_perm_eq (by rw [Nat.card_fin]; norm_num)]
  have hgid : ∀ h ∈ H₀, g h = h := by
    intro h hh
    have hhfix : h ∈ fixSub (fieldAut 2 K σ) := (hJfix h).1 hh
    set c : StatedProj (StatedSp 2 K) := h⁻¹ * g h with hc
    have hcH : c ∈ H₀ := H₀.mul_mem (H₀.inv_mem hh) (hgH h hh)
    have hcomm : ∀ t ∈ T, c * t = t * c := by
      intro t ht
      have key : g h * t * (g h)⁻¹ = h * t * h⁻¹ := by
        have := hgT _ (hTn h hhfix t ht)
        rwa [map_mul, map_mul, map_inv, hgT t ht] at this
      calc c * t = h⁻¹ * (g h * t * (g h)⁻¹) * g h := by rw [hc]; group
        _ = h⁻¹ * (h * t * h⁻¹) * g h := by rw [key]
        _ = t * c := by rw [hc]; group
    have hcent : e ⟨c, hcH⟩ ∈
        Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← h2] at ha
      obtain ⟨u, hu, rfl⟩ := ha
      have huT : (u : StatedProj (StatedSp 2 K)) ∈ T := by
        rw [hT, ← Subgroup.map_subtype_commutator]
        exact Subgroup.mem_map_of_mem _ hu
      have hu' := hcomm _ huT
      change e u * e ⟨c, hcH⟩ = e ⟨c, hcH⟩ * e u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hu'.symm
    rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (by simp), Subgroup.mem_bot] at hcent
    have hc1 : c = 1 := congrArg Subtype.val (e.injective (hcent.trans (map_one e).symm))
    rw [hc] at hc1
    exact (inv_mul_eq_one.1 hc1).symm
  have hgfix : g ∈ fixingSubgroup (MulAut (StatedProj (StatedSp 2 K)))
      (H₀ : Set (StatedProj (StatedSp 2 K))) :=
    (mem_fixingSubgroup_iff _).2 fun u hu => hgid u hu
  rw [hfixing, hzp] at hgfix
  have hdvd : orderOf g ∣ p := hδp ▸ orderOf_dvd_of_mem_zpowers hgfix
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hgp.symm hdvd)

theorem outerFields_psp_odd {ℓ f r p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) :
    OuterFields p (StatedProj (StatedSp r K)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have O := CFSG.RankThree.PartOne.KCSpComm.spOuter hℓ hf hr hK
  have hcyc : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : NeZero r := ⟨by omega⟩
  intro D hD hDc hDin
  have hEel : CFSG.IsElementaryAbelian p D :=
    { toIsMulCommutative := hD.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hD.2 x x.2) }
  have hcap := CFSG.RankThree.PartOne.KCSpComm.card_inf_inner_eq_prime O hr hp hp2 hcyc
    (A := D) hDc hDin
  obtain ⟨y, hyD, hy1⟩ : ∃ y ∈ D ⊓ innerAut (StatedProj (StatedSp r K)), y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : D ⊓ innerAut (StatedProj (StatedSp r K)) = ⊥ :=
      eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
    have hcap' : Nat.card ↥(D ⊓ innerAut (StatedProj (StatedSp r K))) = p := hcap
    rw [hbot, Subgroup.card_bot] at hcap'
    exact hp.one_lt.ne hcap'
  obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
  obtain ⟨hpf, σ, hσ, h, -, hxh⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.noninner_element_data O hp hp2 (A := D) hxD hxin
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun ⟨_, h2⟩ => by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h3 : 3 ≤ f := hp3.trans (Nat.le_of_dvd (by omega) hpf)
    have h8 : 2 ^ 3 ≤ ℓ ^ f :=
      (Nat.pow_le_pow_right (by norm_num) h3).trans (Nat.pow_le_pow_left hℓ.two_le f)
    omega
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective hℓ hf hK hr hrq
  have hcomm : y * x = x * y := congrArg Subtype.val
    (hD.1.is_comm.comm ⟨y, hyD.1⟩ ⟨x, hxD⟩)
  have hyp : y ^ p = 1 := hD.2 y hyD.1
  obtain ⟨-, -, -, -, -, hJfix, -, hJs, -, hfixing, hzp, hzcard, -, -⟩ :=
    symplectic_prime_subfield_fixed_group_and_full_centralizer_odd (K := K) hℓ hp hp2 hpℓ hf hr
      hK σ hσ
  have hδp : orderOf (fieldAut r K σ) = p := by
    rw [← Nat.card_zpowers, hzcard]
  refine ⟨x, hxD, hxin, ?_⟩
  by_cases hex : r = 2 ∧ ℓ ^ (f / p) = 2
  · obtain ⟨rfl, hexc⟩ := hex
    obtain ⟨k, hkδ, hkord⟩ :=
      exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyD.2 hy1 hyp hcomm
    have hδ : FieldCoreAt p (fieldAut 2 K σ) :=
      fieldCoreAt_fieldAut_sp_two_exc hℓ hp hp2 hpℓ hf hK σ hσ hexc ⟨k, (hJfix k).2 hkδ, hkord⟩
    exact fieldCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)
  · obtain ⟨hJsimple, hJnc⟩ := hJs hex
    have hJq : CFSG.IsQuasisimple (subfieldFixedGroup K r σ) :=
      isQuasisimple_of_simple_nonabelian (fun hc => by
        obtain ⟨a, b, hab⟩ := hJnc
        exact hab (hc a b))
    refine fieldCoreAt_of_canonical_conj hp hinj hδp hJq hJfix ?_ hxh hyD.2 hy1 hyp hcomm
    intro β hβ
    have hβmem : β ∈ fixingSubgroup (MulAut (StatedProj (StatedSp r K)))
        ((subfieldFixedGroup K r σ : Subgroup (StatedProj (StatedSp r K))) :
          Set (StatedProj (StatedSp r K))) :=
      (mem_fixingSubgroup_iff _).2 fun u hu => hβ u hu
    rw [hfixing, hzp] at hβmem
    exact hβmem

end Symplectic

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

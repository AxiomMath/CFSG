module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterInnerPrime
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.OrthOuterThree
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessTransport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Layer
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne FOC CFSG.RankThree.PartOne.KCOrthogonalD4
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.HardMathSupport.Lang.Proving
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem fieldCoreAt_of_descent_of_dvd {P P' : Type*} [Group P] [Finite P] [Group P'] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    {a : MulAut P} (hap : a ^ p = 1) (haH : a ∉ innerAut P) (hpdvd : p ∣ Nat.card P)
    {Θ : P ≃* P'} {δ : MulAut P'} (hΘ : MulAut.congr Θ a = δ) (hF : FixedData p δ) :
    FieldCoreAt p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy, hy1, hyp, hcomm⟩ := exists_innerAut_orderOf_prime_commute hp hinj hap hpdvd
  exact fieldCoreAt_of_descent hp hp2 hinj Θ hΘ hF hy hy1 hyp hcomm

theorem fieldCoreAt_pomegaOdd_of_mem_image {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadOdd n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range)
    (hap : orderOf a = p) (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    FieldCoreAt p a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_odd h K hK e
  have hd : 0 < 2 * n + 1 := by
    have := h.1.2.2.1
    omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadOdd n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd
    (Or.inl rfl) n ℓ f p h hp hp2 K hK e a haE haD hap
  have hpne : p ≠ 2 := hp2
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hFD : FixedData p (matrixProjectiveConjugationHom (coordinateQuadOdd n K) g') := by
    by_cases h3 : p = 3
    · subst h3
      exact fixedData_odd_three hCM.1 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r
    · exact fixedData_odd hCM.1 hp (by have h2 := hp.two_le; omega) hpℓ hpf K hK U.val.right
        hord' hcard' g' hg'l hg'r
  refine fieldCoreAt_of_descent_of_dvd hp hp2 hinj (a := a) (Θ := Θ)
    (by rw [← hap]; exact pow_orderOf_eq_one a) haH hpdvd ?_ hFD
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem fieldCoreAt_pomegaPlus_of_mem_image {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadPlus n K))
    (haD : a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range)
    (hap : orderOf a = p) (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    FieldCoreAt p a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus h K hK e
  have hn4 : 4 ≤ n := h.1.2.2
  have hd : 0 < 2 * n := by omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadPlus n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hFD : FixedData p (matrixProjectiveConjugationHom (coordinateQuadPlus n K) g') := by
    by_cases h3 : p = 3
    · subst h3
      exact fixedData_plus_three hCM.1 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r
    · exact fixedData_plus hCM.1 hp (by have h2 := hp.two_le; omega) hpℓ hpf K hK U.val.right
        hord' hcard' g' hg'l hg'r
  refine fieldCoreAt_of_descent_of_dvd hp hp2 hinj (a := a) (Θ := Θ)
    (by rw [← hap]; exact pow_orderOf_eq_one a) haH hpdvd ?_ hFD
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem fieldCoreAt_pomegaMinus_of_mem_image {n ℓ f p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))}
    (haE : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (haD : a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range)
    (hap : orderOf a = p)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :
    FieldCoreAt p a := by
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have hd : 0 < 2 * n := by omega
  have hinj : Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :=
    conj_injective_matrixProjectiveDerived _ hd hnd hT
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp2 hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hFD : FixedData p (matrixProjectiveConjugationHom
      (coordinateQuadMinus n K hn (b' : K) (c' : K)) g') := by
    by_cases h3 : p = 3
    · subst h3
      exact fixedData_minus_three hCM.1 hpℓ hpf hn K hK U.val.right hord' hcard' b' c' hirr' g'
        hg'l hg'r
    · exact fixedData_minus hCM.1 hp (by have h2 := hp.two_le; omega) hpℓ hpf hn K hK U.val.right
        hord' hcard' b' c'
        hirr' g' hg'l hg'r
  refine fieldCoreAt_of_descent_of_dvd hp hp2 hinj (a := a) (Θ := Θ)
    (by rw [← hap]; exact pow_orderOf_eq_one a) haH hpdvd ?_ hFD
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem pomegaOdd_mem_image_not_linear {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    a ∈ matrixProjectiveImage (coordinateQuadOdd n K) ∧
      a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := h.1
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd (Or.inl rfl)
    n ℓ f h K hK e
  refine ⟨?_, ?_⟩
  · by_cases h3 : 3 < p
    · exact FOC.mem_E_of_pow_eq_one hg hp h3 hap
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      have h2K : ringChar K ≠ 2 := by
        rw [ringChar_eq_of_card_eq hℓ hf hK]
        exact hℓ2
      exact (matrixProjectiveImage_eq_top_odd K n hn3 h2K) ▸ Subgroup.mem_top a
  · intro hD
    by_cases h3 : 3 < p
    · exact haH (FOC.mem_inner_of_mem_D hg hp h3 hD hap)
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      exact haH (mem_inner_of_mem_D_three hg hD hap)

theorem fieldCoreAt_pomegaOdd_of_outer {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadOdd n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K))) :
    FieldCoreAt p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨haE, haD⟩ := pomegaOdd_mem_image_not_linear h hp hp2 hpℓ hK e hap haH
  have ha1 : a ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact fieldCoreAt_pomegaOdd_of_mem_image h hp hp2 hpℓ hK e haE haD
    (orderOf_eq_prime hap ha1) haH hpdvd

theorem pomegaPlus_mem_image_not_linear {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f)
    (hn : 5 ≤ n ∨ 3 < p) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    a ∈ matrixProjectiveImage (coordinateQuadPlus n K) ∧
      a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  refine ⟨?_, ?_⟩
  · by_cases h3 : 3 < p
    · exact FOC.mem_E_of_pow_eq_one hg hp h3 hap
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      have hn5 : 5 ≤ n := by
        rcases hn with h | h
        · exact h
        · omega
      exact (matrixProjectiveImage_eq_top_plus K n hn5) ▸ Subgroup.mem_top a
  · intro hD
    by_cases h3 : 3 < p
    · exact haH (FOC.mem_inner_of_mem_D hg hp h3 hD hap)
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      exact haH (mem_inner_of_mem_D_three hg hD hap)

theorem fieldCoreAt_pomegaPlus_of_outer {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] [Finite G] (h : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f)
    (hn : 5 ≤ n ∨ 3 < p) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    FieldCoreAt p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨haE, haD⟩ := pomegaPlus_mem_image_not_linear h hn hp hp2 hpℓ hK e hap haH
  have ha1 : a ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact fieldCoreAt_pomegaPlus_of_mem_image h hp hp2 hpℓ hK e haE haD
    (orderOf_eq_prime hap ha1) haH hpdvd

theorem pomegaMinus_mem_image_not_linear {n ℓ f p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :
    a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c) ∧
      a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hn4⟩ := h.1
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  refine ⟨?_, ?_⟩
  · by_cases h3 : 3 < p
    · exact FOC.mem_E_of_pow_eq_one hg hp h3 hap
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      exact (matrixProjectiveImage_eq_top_minus K n hn4 b c hirr) ▸ Subgroup.mem_top a
  · intro hD
    by_cases h3 : 3 < p
    · exact haH (FOC.mem_inner_of_mem_D hg hp h3 hD hap)
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        omega
      subst hp3
      exact haH (mem_inner_of_mem_D_three hg hD hap)

theorem fieldCoreAt_pomegaMinus_of_outer {n ℓ f p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    {a : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))} (hap : a ^ p = 1)
    (haH : a ∉ inner (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))
    (hpdvd : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :
    FieldCoreAt p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨haE, haD⟩ := pomegaMinus_mem_image_not_linear hn h hp hp2 hpℓ hK b c hirr e hap haH
  have ha1 : a ≠ 1 := fun h1 => haH (h1 ▸ one_mem _)
  exact fieldCoreAt_pomegaMinus_of_mem_image hn h hp hp2 hpℓ hK b c hirr e haE haD
    (orderOf_eq_prime hap ha1) haH hpdvd

theorem outerPLayerAt_pomegaOdd {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaOdd n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card G) :
    OuterPLayerAt p G := by
  have h' := h
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp (coordinateOddWitnessEquiv K e) ?_
  intro x hxp hxo
  have hpdvdM : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
    rw [← Nat.card_congr (coordinateOddWitnessEquiv K e).toEquiv]
    exact hpdvd
  exact fieldCoreAt_pomegaOdd_of_outer h' hp hp2 hpℓ hK e hxp
    (fun hmem => hxo (inner_le_innAutDerived _ hmem)) hpdvdM

theorem outerPLayerAt_pomegaPlus {n ℓ f p : ℕ} {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaPlus n ℓ f) (hn : 5 ≤ n ∨ 3 < p)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpdvd : p ∣ Nat.card G) :
    OuterPLayerAt p G := by
  have h' := h
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp (coordinatePlusWitnessEquiv K e) ?_
  intro x hxp hxo
  have hpdvdM : p ∣ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rw [← Nat.card_congr (coordinatePlusWitnessEquiv K e).toEquiv]
    exact hpdvd
  exact fieldCoreAt_pomegaPlus_of_outer h' hn hp hp2 hpℓ hK e hxp
    (fun hmem => hxo (inner_le_innAutDerived _ hmem)) hpdvdM

theorem outerPLayerAt_pomegaMinus {n ℓ f p : ℕ} (hn : 1 ≤ n) {G : Type} [Group G] [Finite G]
    {K : Type} [Field K] [Finite K] (h : CFSG.Open.StatedClassicalModel G .POmegaMinus n ℓ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    (hpdvd : p ∣ Nat.card G) : OuterPLayerAt p G := by
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp (coordinateMinusWitnessEquiv K hn b c e) ?_
  intro x hxp hxo
  have hpdvdM : p ∣ Nat.card
      (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
    rw [← Nat.card_congr (coordinateMinusWitnessEquiv K hn b c e).toEquiv]
    exact hpdvd
  exact fieldCoreAt_pomegaMinus_of_outer hn h hp hp2 hpℓ hK b c hirr e hxp
    (fun hmem => hxo (inner_le_innAutDerived _ hmem)) hpdvdM

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

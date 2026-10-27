module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase
public import CFSG.RankThree.PartOne.FOC.OrthOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalDescent CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Open (IsElemAbelian)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (FieldCoreAt isQuasisimple_of_simple_nonabelian)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

@[expose] def FixedData (p : ℕ) {P : Type*} [Group P] (δ : MulAut P) : Prop :=
  orderOf δ = p ∧ ∃ N J : Subgroup P, (∀ t, δ t = t ↔ t ∈ N) ∧ J ≤ N ∧
    (J.subgroupOf N).Normal ∧ (∀ [(J.subgroupOf N).Normal], IsPGroup 2 (↥N ⧸ J.subgroupOf N)) ∧
    CFSG.IsQuasisimple J ∧ fixingSubgroup (MulAut P) (J : Set P) = Subgroup.zpowers δ

theorem fieldCoreAt_of_fixedData {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {δ : MulAut P}
    (hF : FixedData p δ) {y : MulAut P} (hy : y ∈ innerAut P) (hy1 : y ≠ 1) (hyp : y ^ p = 1)
    (hcomm : y * δ = δ * y) : FieldCoreAt p δ := by
  obtain ⟨hδp, N, J, hN, hJN, hJn, hquot, hJq, hfix⟩ := hF
  exact fieldCoreAt_of_normal_simple_fixed hp hp2 hinj hδp hN hJN hJn hJq (@hquot hJn) hfix hy
    hy1 hyp hcomm

theorem fieldCoreAt_of_descent {P P' : Type*} [Group P] [Finite P] [Group P'] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hinj : Function.Injective (MulAut.conj : P →* MulAut P))
    (Θ : P ≃* P') {a : MulAut P} {δ : MulAut P'} (hΘ : MulAut.congr Θ a = δ)
    (hF : FixedData p δ) {y : MulAut P} (hy : y ∈ innerAut P) (hy1 : y ≠ 1) (hyp : y ^ p = 1)
    (hcomm : y * a = a * y) : FieldCoreAt p a := by
  have : Finite P' := Finite.of_equiv P Θ.toEquiv
  have hinj' := conj_injective_of_mulEquiv Θ hinj
  have h1 : FieldCoreAt p δ := by
    refine fieldCoreAt_of_fixedData hp hp2 hinj' hF (y := MulAut.congr Θ y)
      (congr_mem_innerAut Θ hy) ?_ ?_ ?_
    · intro h
      exact hy1 ((MulAut.congr Θ).injective (by rw [h, map_one]))
    · rw [← map_pow, hyp, map_one]
    · rw [← hΘ, ← map_mul, ← map_mul, hcomm]
  have h2 := FieldCoreAt.congr h1 Θ.symm
  rwa [← hΘ, congr_symm_congr] at h2

theorem outerFields_of_descent {P : Type*} [Group P] {p : ℕ} (hp : p.Prime)
    (E D : Subgroup (MulAut P)) (hE : ∀ β : MulAut P, β ^ p = 1 → β ∈ E)
    (hD : ∀ β ∈ D, β ^ p = 1 → β ∈ innerAut P)
    (hcap : ∀ A : Subgroup (MulAut P), IsElemAbelian p A → Nat.card A = p ^ 2 →
      ¬ A ≤ innerAut P → ∃ y ∈ A, y ∈ innerAut P ∧ y ≠ 1)
    (hdesc : ∀ a ∈ E, a ∉ D → orderOf a = p → ∀ y ∈ innerAut P, y ≠ 1 → y ^ p = 1 →
      y * a = a * y → FieldCoreAt p a) : OuterFields p P := by
  have : Fact p.Prime := ⟨hp⟩
  intro A hA hAc hAin
  obtain ⟨y, hyA, hyin, hy1⟩ := hcap A hA hAc hAin
  obtain ⟨x, hxA, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hAin
  have hxp : x ^ p = 1 := hA.2 x hxA
  have hx1 : x ≠ 1 := fun h => hxin (h ▸ one_mem _)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  refine ⟨x, hxA, hxin, hdesc x (hE x hxp) (fun hxD => hxin (hD x hxD hxp)) hord y hyin hy1
    (hA.2 y hyA) ?_⟩
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hyA⟩ ⟨x, hxA⟩)

section Fixed

theorem fixedData_odd {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (g : similarityPairs (coordinateQuadOdd n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    FixedData p (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaOdd (Or.inl rfl) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, hord, hfixiff, hJN, hJn, hquot, -, -, hfixJ, -⟩ := hconc
  have := hsimple
  exact ⟨hord, _, _, hfixiff, hJN, hJn, @hquot, isQuasisimple_of_simple_nonabelian
    (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), hfixJ⟩

theorem fixedData_plus {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (g : similarityPairs (coordinateQuadPlus n K)) (hl : g.val.left = 1) (hr : g.val.right = σ) :
    FixedData p (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk
  have hg : g = fieldPair (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) :=
    Subtype.ext (SemidirectProduct.ext hl hr)
  subst hg
  obtain ⟨⟨-, hsimple, hnab⟩, hord, hfixiff, hJN, hJn, hquot, -, -, hfixJ, -⟩ := hconc
  have := hsimple
  exact ⟨hord, _, _, hfixiff, hJN, hJn, @hquot, isQuasisimple_of_simple_nonabelian
    (fun hc => by
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc a b)), hfixJ⟩

theorem fixedData_minus {n ℓ f p : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n ℓ (f / p))
    (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ) (hpf : p ∣ f) (hn : 1 ≤ n) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hcard : Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p))
    (b c' : semilinearFixedSubfield σ)
    (hirr : ∀ s : semilinearFixedSubfield σ, s ^ 2 + b * s + c' ≠ 0)
    (g : similarityPairs (coordinateQuadMinus n K hn (b : K) (c' : K))) (hl : g.val.left = 1)
    (hr : g.val.right = σ) :
    FixedData p (matrixProjectiveConjugationHom _ g) := by
  obtain ⟨e, rfl⟩ := hpf
  have hdiv : p * e / p = e := Nat.mul_div_cancel_left e hp.pos
  rw [hdiv] at hadm hcard
  have hK' : Nat.card K = ℓ ^ (e * p) := by
    rw [mul_comm]
    exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have key := orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional
    .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ e p hadm hp hp3 hpℓ
  obtain ⟨-, hconc⟩ := key hn K (semilinearFixedSubfield σ) hcard hK' σ hσ hσk b c' hirr
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

section Model

theorem exists_inner_of_gates {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {f p : ℕ} (hg : OrthogonalGates Q f) (hp : p.Prime)
    (hp3 : 3 < p) [Finite (matrixProjectiveDerived Q)] :
    ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)), IsElemAbelian p A → Nat.card A = p ^ 2 →
      ¬ A ≤ innerAut (matrixProjectiveDerived Q) →
      ∃ y ∈ A, y ∈ innerAut (matrixProjectiveDerived Q) ∧ y ≠ 1 := by
  intro A hA hAc hAin
  have hel : CFSG.IsElementaryAbelian p A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2 hA
  obtain ⟨hcap, -⟩ := hg.2.2.2.2.2.2.2.1 p hp hp3 A hel hAc hAin
  by_contra hno
  push Not at hno
  have hbot : A ⊓ ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) =
      ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz.1 hz.2)
  rw [hbot, Subgroup.card_bot] at hcap
  exact hp.one_lt.ne hcap

theorem outerFields_matrix_odd {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadOdd n K))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadOdd n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)))) :
    OuterFields p (matrixProjectiveDerived (coordinateQuadOdd n K)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd (Or.inl rfl)
    n ℓ f h K hK e
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadOdd n K))
    (linearConjugationHom (coordinateQuadOdd n K)).range
    (fun β hβp => FOC.mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => FOC.mem_inner_of_mem_D hg hp hp3 hβD hβp)
    (exists_inner_of_gates hg hp hp3) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaOdd (Or.inl rfl)
    n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp (by omega) hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_odd hCM.1 hp hp3 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r) hy hy1 hyp
    hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerFields_matrix_plus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    [Finite (matrixProjectiveDerived (coordinateQuadPlus n K))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
        MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))) :
    OuterFields p (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f h K hK e
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadPlus n K))
    (linearConjugationHom (coordinateQuadPlus n K)).range
    (fun β hβp => FOC.mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => FOC.mem_inner_of_mem_D hg hp hp3 hβD hβp)
    (exists_inner_of_gates hg hp hp3) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p h hp hp3 hpℓ K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp (by omega) hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_plus hCM.1 hp hp3 hpℓ hpf K hK U.val.right hord' hcard' g' hg'l hg'r) hy hy1 hyp
    hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

theorem outerFields_matrix_minus {G : Type} [Group G] {n ℓ f p : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hn : 1 ≤ n) (hp : p.Prime) (hp3 : 3 < p)
    (hpℓ : p ≠ ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
    [Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))]
    (hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus n K hn b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)))) :
    OuterFields p (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c hirr e
  refine outerFields_of_descent hp (matrixProjectiveImage (coordinateQuadMinus n K hn b c))
    (linearConjugationHom (coordinateQuadMinus n K hn b c)).range
    (fun β hβp => FOC.mem_E_of_pow_eq_one hg hp hp3 hβp)
    (fun β hβD hβp => FOC.mem_inner_of_mem_D hg hp hp3 hβD hβp)
    (exists_inner_of_gates hg hp hp3) ?_
  intro a haE haD hap y hy hy1 hyp hcomm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p h hp hp3 hpℓ hn K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  refine fieldCoreAt_of_descent hp (by omega) hinj Θ (a := a)
    (δ := matrixProjectiveConjugationHom _ g') ?_
    (fixedData_minus hCM.1 hp hp3 hpℓ hpf hn K hK U.val.right hord' hcard' b' c' hirr' g' hg'l
      hg'r) hy hy1 hyp hcomm
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr Θ a) x = Θ (a (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

end Model

end CFSG.HardMathSupport.Timmesfeld.LocalTwo

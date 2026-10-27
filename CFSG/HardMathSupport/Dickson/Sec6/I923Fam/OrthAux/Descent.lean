module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Field
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)
open CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Dickson.Sec6.I923

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem noL2Layer_of_fieldDescent {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p) (U : similarityPairs Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hfield : NoL2Layer (fieldAutT Q' σ S.hQσ)) [Finite (matrixProjectiveDerived Q)] :
    NoL2Layer (matrixProjectiveConjugationHom Q U) := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ (matrixProjectiveConjugationHom Q U)) x =
        Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  exact noL2Layer_of_congr Θ (hcongr ▸ hfield)

end Field

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem mem_E_of_pow_eq_one_three (hg : OrthogonalGates Q f)
    (htop : projectivePointFamilyAut Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)} :
    β ∈ matrixProjectiveImage Q := by
  have h1 : β ∈ projectivePointFamilyAut Q := htop ▸ Subgroup.mem_top β
  rwa [hg.2.2.2.2.2.1] at h1

theorem mem_inner_of_mem_D_three' (hg : OrthogonalGates Q f)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ 3 = 1) : ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  exact mem_of_pow_eq_one_of_relIndex_eq_two_pow hk Nat.prime_three (by norm_num) hβD hβp

theorem noL2Layer_of_gates_outer {G : Type} [Group G] [Finite G]
    (e : G ≃* matrixProjectiveDerived Q) (hg : OrthogonalGates Q f)
    (β : MulAut G) (hβ : β ^ 3 = 1) (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hout : ∀ a : G, MulAut.conj a ≠ β)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = 3 → NoL2Layer a) : NoL2Layer β := by
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · exfalso
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_three' hg hD hβ'
    refine hout (e.symm t) ((MulAut.congr e).injective ?_)
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  · have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e β) = 3 := orderOf_eq_prime hβ' hne1
    exact noL2Layer_of_congr e (hdesc _ hE hD hord)

end Gates

section Odd

theorem noL2Layer_omega_odd_outer (hO : LieOrderFormulasInput) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {β : MulAut G} (hβ : β ^ 3 = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : NoL2Layer β := by
  obtain ⟨hℓ, -, hn3, hℓ2⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n ℓ f hG K hK e
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hG K hK e
  have h2 : (2 : K) ≠ 0 := by
    have hprime : (ringChar K).Prime := hchar ▸ hℓ
    rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hprime, hchar]
    exact hℓ2
  have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) n ℓ f hG) K hK).2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv G (coordinateOddWitnessEquiv K e).toEquiv
  refine noL2Layer_of_gates_outer (coordinateOddWitnessEquiv K e) hgates β hβ
    (mem_E_of_pow_eq_one_three hgates htop) hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  have S := subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' hn3 h2
  exact noL2Layer_of_fieldDescent S U Θ g' hg'l hg'r hΘ (noL2Layer_fieldAutT_odd hO hCM.1 hcard' S)

end Odd

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem noL2Layer_omega_plus_of_E (hO : LieOrderFormulasInput) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {β : MulAut G} (hβ : β ^ 3 = 1) (hout : ∀ a : G, MulAut.conj a ≠ β)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K)) : NoL2Layer β := by
  obtain ⟨-, -, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  refine noL2Layer_of_gates_outer (coordinatePlusWitnessEquiv K e) hgates β hβ hE hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' (by omega : 3 ≤ n)
  exact noL2Layer_of_fieldDescent S U Θ g' hg'l hg'r hΘ (noL2Layer_fieldAutT_plus hO hCM.1 hcard' S)

theorem noL2Layer_omega_plus_outer (hO : LieOrderFormulasInput) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (hn5 : 5 ≤ n) {β : MulAut G}
    (hβ : β ^ 3 = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) : NoL2Layer β := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
    (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 hn5
  exact noL2Layer_omega_plus_of_E hO hG K hK e hβ hout (mem_E_of_pow_eq_one_three hgates htop)

end Plus

section Minus

theorem noL2Layer_omega_minus_outer (hO : LieOrderFormulasInput) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {β : MulAut G} (hβ : β ^ 3 = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : NoL2Layer β := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n ℓ f hG)
      hn1 K hK b c hirr).2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  refine noL2Layer_of_gates_outer (coordinateMinusWitnessEquiv K hn1 b c e) hgates β hβ
    (mem_E_of_pow_eq_one_three hgates htop) hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f 3 hG Nat.prime_three (by norm_num) hn1 K hK b c hirr e a haE haD
    hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m (by norm_num)
  have hcard'' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ m := by
    rw [← hdiv]
    exact hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = ℓ ^ (m * 3) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1 hcard'' hK'
  rw [← hUκ]
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' hn4 hdeg b' c' hirr'
  exact noL2Layer_of_fieldDescent S U Θ g' hg'l hg'r hΘ
    (noL2Layer_fieldAutT_minus hO hn1 hCM.1 hcard' b' c' hirr' S)

end Minus

end CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux

module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Assembly.LowTwoRank
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

private theorem perfectInLayer_of_fix_eq_omega {S : Type*} [Group S] {β : MulAut S}
    {N J : Subgroup S} (hfix : fixSubgroup β = N) (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal)
    (hJq : CFSG.IsQuasisimple J) (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N)) :
    PerfectInLayer β := by
  subst hfix
  haveI := hJn
  exact perfectInLayer_of_normal_quasisimple hJN hJq hsol

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

private theorem perfectInLayer_fieldAutT_omega (S : SubfieldSetup k Q₀ Q σ p) :
    PerfectInLayer (fieldAutT Q σ S.hQσ) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k S.hext) :=
    CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k S.hext hd).symm
      (isQuasisimple_of_isSimpleGroup hsimp hnonab)
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  have hJn := subfieldDerivedImage_normal k S.hext
  haveI := hJn
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  exact perfectInLayer_of_fix_eq_omega hfix (subfieldDerivedImage_le k S.hext) hJn hJq
    inferInstance

private theorem perfectInLayer_of_fieldDescent_omega {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p) (U : similarityPairs Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    PerfectInLayer (matrixProjectiveConjugationHom Q U) := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ (matrixProjectiveConjugationHom Q U)) x =
        Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  exact perfectInLayer_of_congr Θ _ (hcongr ▸ perfectInLayer_fieldAutT_omega S)

end Field

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

private theorem mem_E_of_pow_eq_one_omega (hg : OrthogonalGates Q f) (hp : p.Prime)
    (h : 3 < p ∨ projectivePointFamilyAut Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)}
    (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
  rcases h with hp3 | htop
  · have hpg : IsPGroup p (Subgroup.zpowers β) := by
      intro g
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hβp, one_zpow]
      rfl
    have hK0 := hg.2.2.2.2.2.2.1 p hp hp3 _ hpg
    have h1 : β ∈ projectivePointFamilyAut Q := hg.2.2.2.2.1 (hK0 (Subgroup.mem_zpowers β))
    rw [hg.2.2.2.2.2.1] at h1
    exact h1
  · have h1 : β ∈ projectivePointFamilyAut Q := htop ▸ Subgroup.mem_top β
    rwa [hg.2.2.2.2.2.1] at h1

private theorem mem_inner_of_mem_D_omega (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ p = 1) : ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  exact mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hβD hβp

private theorem perfectInLayer_of_gates_omega {G : Type} [Group G]
    (e : G ≃* matrixProjectiveDerived Q) (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut G) (hβ : β ^ p = 1) (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hcen : Subgroup.center (matrixProjectiveDerived Q) = ⊥)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = p → PerfectInLayer a)
    (hinn : ∀ a : G, a ^ p = 1 → PerfectInLayer (MulAut.conj a)) : PerfectInLayer β := by
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hg hp hp2 hD hβ'
    have htp : t ^ p = 1 := by
      have hc : t ^ p ∈ Subgroup.center (matrixProjectiveDerived Q) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (matrixProjectiveDerived Q) => φ g)
          (show MulAut.conj (t ^ p) = 1 by rw [map_pow, ht]; exact hβ')
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * t ^ p = t ^ p * g * (t ^ p)⁻¹ * t ^ p := by rw [h1]
          _ = t ^ p * g := by group
      rw [hcen, Subgroup.mem_bot] at hc
      exact hc
    have hcongr : MulAut.congr e (MulAut.conj (e.symm t)) = MulAut.congr e β := by
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
    have hβc : β = MulAut.conj (e.symm t) := ((MulAut.congr e).injective hcongr).symm
    rw [hβc]
    exact hinn (e.symm t) (by rw [← map_pow, htp, map_one])
  · have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (MulAut.congr e β) = p := orderOf_eq_prime hβ' hne1
    exact perfectInLayer_of_congr e β (hdesc _ hE hD hord)

end Gates

section Odd

theorem perfectInLayer_omega_odd_of_mem_E {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) {β : MulAut G} (hβ : β ^ p = 1)
    (hβE : MulAut.congr (coordinateOddWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadOdd n K)) : PerfectInLayer β := by
  obtain ⟨hℓ, -, hn3, hℓ2⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n ℓ f hG K hK e
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_odd hG K hK e
  have h2 : (2 : K) ≠ 0 := by
    have hprime : (ringChar K).Prime := hchar ▸ hℓ
    rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hprime, hchar]
    exact hℓ2
  refine perfectInLayer_of_gates_omega (coordinateOddWitnessEquiv K e) hgates hp hp2 β hβ hβE
    (center_matrix_eq_bot (by omega : 0 < 2 * n + 1) hnd hT) ?_
    (fun a ha => perfectInLayer_conj_omega (Or.inl rfl) hG hp hp2 hpℓ a ha)
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f p hG hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact perfectInLayer_of_fieldDescent_omega
    (subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' hn3 h2) U Θ g'
    hg'l hg'r hΘ

private theorem perfectInLayer_omega_odd {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (β : MulAut G) (hβ : β ^ p = 1) : PerfectInLayer β := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n ℓ f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) n ℓ f hG) K hK).2
  exact perfectInLayer_omega_odd_of_mem_E hG hp hp2 hpℓ hK e hβ
    (mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) (by rw [← map_pow, hβ, map_one]))

end Odd

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem perfectInLayer_omega_plus_of_mem_E {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) {β : MulAut G} (hβ : β ^ p = 1)
    (hβE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K)) : PerfectInLayer β := by
  obtain ⟨-, -, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hG K hK e
  refine perfectInLayer_of_gates_omega (coordinatePlusWitnessEquiv K e) hgates hp hp2 β hβ hβE
    (center_matrix_eq_bot (by omega : 0 < 2 * n) hnd hT) ?_
    (fun a ha => perfectInLayer_conj_omega (Or.inr (Or.inl rfl)) hG hp hp2 hpℓ a ha)
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hG hp hp2 K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact perfectInLayer_of_fieldDescent_omega
    (subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' (by omega : 3 ≤ n))
    U Θ g' hg'l hg'r hΘ

private theorem perfectInLayer_omega_plus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hD4 : n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1) : PerfectInLayer β := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  have hEA : 3 < p ∨ projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · left
      have := hD4 h4
      have := hp.two_le
      omega
    · right
      exact (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 h5
  exact perfectInLayer_omega_plus_of_mem_E hG hp hp2 hpℓ hK e hβ
    (mem_E_of_pow_eq_one_omega hgates hp hEA (by rw [← map_pow, hβ, map_one]))

end Plus

section Minus

theorem perfectInLayer_omega_minus_of_mem_E {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) {β : MulAut G}
    (hβ : β ^ p = 1) (hβE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)) : PerfectInLayer β := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hG K hK b c hirr e
  refine perfectInLayer_of_gates_omega (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2 β hβ
    hβE (center_matrix_eq_bot (by omega : 0 < 2 * n) hnd hT) ?_
    (fun a ha => perfectInLayer_conj_omega (Or.inr (Or.inr rfl)) hG hp hp2 hpℓ a ha)
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hG hp hp2 hn1 K hK b c hirr e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  rw [hdiv] at hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = ℓ ^ (m * p) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1 hcard' hK'
  rw [← hUκ]
  exact perfectInLayer_of_fieldDescent_omega
    (subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' hn4 hdeg b' c'
      hirr')
    U Θ g' hg'l hg'r hΘ

private theorem perfectInLayer_omega_minus {G : Type} [Group G] {n ℓ f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (β : MulAut G) (hβ : β ^ p = 1) : PerfectInLayer β := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n ℓ f hG)
      hn1 K hK b c hirr).2
  exact perfectInLayer_omega_minus_of_mem_E hG hp hp2 hpℓ hn1 hK hirr e hβ
    (mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) (by rw [← map_pow, hβ, map_one]))

end Minus

theorem perfectInLayer_omega {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] [Finite G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hD4 : t = .POmegaPlus → n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1) :
    PerfectInLayer β := by
  rcases ht with rfl | rfl | rfl
  · exact perfectInLayer_omega_odd hG hp hp2 hpℓ β hβ
  · exact perfectInLayer_omega_plus hG hp hp2 hpℓ (hD4 rfl) β hβ
  · exact perfectInLayer_omega_minus hG hp hp2 hpℓ β hβ

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

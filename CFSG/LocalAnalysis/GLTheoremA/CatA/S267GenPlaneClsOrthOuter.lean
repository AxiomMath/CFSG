module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsSpOrth
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.RankThree.Classical2
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)

private theorem compNormal_of_fix_eq {S : Type} [Group S] [Finite S] {β : MulAut S}
    {M J : Subgroup S} (hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β = M)
    (hJM : J ≤ M) (hJn : (J.subgroupOf M).Normal)
    (hJq : CFSG.IsQuasisimple ↥J) (hsol : Group.IsSolvable (↥M ⧸ J.subgroupOf M)) :
    CompNormal β := by
  subst hfix
  haveI := hJn
  exact compNormal_of_normal_quasisimple hJM hJq hsol

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

private theorem compNormal_fieldAutT (S : SubfieldSetup k Q₀ Q σ p) (hd0 : 0 < d) :
    CompNormal (fieldAutT Q σ S.hQσ) := by
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd0 S.hnd₀ S.hT₀
  have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k S.hext) :=
    CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k S.hext hd0).symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hsimp
        hnonab)
  have hJn := subfieldDerivedImage_normal k S.hext
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  exact compNormal_of_fix_eq (Subgroup.ext fun t => fieldAutT_apply_iff S t)
    (subfieldDerivedImage_le k S.hext) hJn hJq inferInstance

end Field

section Descent

variable {K : Type} [Field K] [Finite K] {d : ℕ} {f : ℕ}

private theorem mem_inner_of_mem_D_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : QuadraticForm K (Fin d → K)} (hg : OrthogonalGates Q f)
    {β : MulAut (matrixProjectiveDerived Q)} (hβD : β ∈ (linearConjugationHom Q).range)
    (hβp : β ^ p = 1) : ∃ t : matrixProjectiveDerived Q, MulAut.conj t = β := by
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
    OuterAutomorphisms.inner_normal _
  exact mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hβD hβp

private theorem outer_order_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {Q : QuadraticForm K (Fin d → K)} (e : G ≃* matrixProjectiveDerived Q)
    (hg : OrthogonalGates Q f) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) :
    MulAut.congr e β ∉ (linearConjugationHom Q).range ∧ orderOf (MulAut.congr e β) = p := by
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hD : MulAut.congr e β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_odd hp hp2 hg hD hβ'
    refine hout (e.symm t) ((MulAut.congr e).injective ?_)
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  refine ⟨hD, ?_⟩
  have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hβ' hne1

private theorem mem_E_of_pow_eq_one_orth {p : ℕ} (hp : p.Prime) {Q : QuadraticForm K (Fin d → K)}
    (hg : OrthogonalGates Q f) (h : 3 < p ∨ projectivePointFamilyAut Q = ⊤)
    {β : MulAut (matrixProjectiveDerived Q)} (hβp : β ^ p = 1) : β ∈ matrixProjectiveImage Q := by
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

variable {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)} {σ : K ≃+* K} {p : ℕ}

private structure OmegaFieldConj (G : Type) [Group G] (β : MulAut G) (ℓ p : ℕ) : Prop where
  out : ∃ (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (d : ℕ)
    (Q₀ : QuadraticForm k (Fin d → k)) (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (S : SubfieldSetup k Q₀ Q σ p) (e : G ≃* matrixProjectiveDerived Q),
    7 ≤ d ∧ ringChar K = ℓ ∧ MulAut.congr e β = fieldAutT Q σ S.hQσ

private theorem congr_trans_eq_fieldAutT {G : Type} [Group G]
    {Q Q' : QuadraticForm K (Fin d → K)} (S : SubfieldSetup k Q₀ Q' σ p)
    (φ : G ≃* matrixProjectiveDerived Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (β : MulAut G) (U : similarityPairs Q)
    (hU : matrixProjectiveConjugationHom Q U = MulAut.congr φ β) (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    MulAut.congr (φ.trans Θ) β = fieldAutT Q' σ S.hQσ := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr (φ.trans Θ) β) x =
      Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := by
    rw [hU, MulAut.congr_apply, MulAut.congr_apply]
    rfl
  rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
  rfl

end Descent

section Odd

private theorem omegaFieldConj_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaOdd n ℓ f) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : OmegaFieldConj G β ℓ p := by
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
  obtain ⟨hD, hord⟩ := outer_order_prime hp hp2 (coordinateOddWitnessEquiv K e) hgates β hβ hout
  have hE := mem_E_of_pow_eq_one_orth hp hgates (Or.inr htop)
    (β := MulAut.congr (coordinateOddWitnessEquiv K e) β) (by rw [← map_pow, hβ, map_one])
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n ℓ f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord', -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by rw [hUr]; exact hord'
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have S := subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn3 h2
  exact ⟨⟨K, inferInstance, inferInstance, _, 2 * n + 1, _, _, U.val.right, S,
    (coordinateOddWitnessEquiv K e).trans Θ, by omega, hchar,
    congr_trans_eq_fieldAutT S _ Θ β U hUκ g' hg'l hg'r hΘ⟩⟩

end Odd

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

private theorem omegaFieldConj_plus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaPlus n ℓ f) (hD4 : n = 4 → p ≠ 3)
    (β : MulAut G) (hβ : β ^ p = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) :
    OmegaFieldConj G β ℓ p := by
  obtain ⟨-, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hG K hK e
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hG K hK e
  have hEA : 3 < p ∨ projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · left
      have := hD4 h4
      have := hp.two_le
      omega
    · right
      exact (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 h5
  obtain ⟨hD, hord⟩ := outer_order_prime hp hp2 (coordinatePlusWitnessEquiv K e) hgates β hβ hout
  have hE := mem_E_of_pow_eq_one_orth hp hgates hEA
    (β := MulAut.congr (coordinatePlusWitnessEquiv K e) β) (by rw [← map_pow, hβ, map_one])
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord', -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by rw [hUr]; exact hord'
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord''
    (by omega : 3 ≤ n)
  exact ⟨⟨K, inferInstance, inferInstance, _, 2 * n, _, _, U.val.right, S,
    (coordinatePlusWitnessEquiv K e).trans Θ, by omega, hchar,
    congr_trans_eq_fieldAutT S _ Θ β U hUκ g' hg'l hg'r hΘ⟩⟩

end Plus

section Minus

private theorem omegaFieldConj_minus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G .POmegaMinus n ℓ f) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : OmegaFieldConj G β ℓ p := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hG hn1 K hK b c hirr e
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hG K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n ℓ f hG)
      hn1 K hK b c hirr).2
  obtain ⟨hD, hord⟩ := outer_order_prime hp hp2 (coordinateMinusWitnessEquiv K hn1 b c e) hgates β
    hβ hout
  have hE := mem_E_of_pow_eq_one_orth hp hgates (Or.inr htop)
    (β := MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β)
    (by rw [← map_pow, hβ, map_one])
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord', hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord'' : orderOf U.val.right = p := by rw [hUr]; exact hord'
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
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg
    b' c' hirr'
  exact ⟨⟨K, inferInstance, inferInstance, _, 2 * n, _, _, U.val.right, S,
    (coordinateMinusWitnessEquiv K hn1 b c e).trans Θ, by omega, hchar,
    congr_trans_eq_fieldAutT S _ Θ β U hUκ g' hg'l hg'r hΘ⟩⟩

end Minus


theorem compNormal_omega_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f)
    (hD4 : t = .POmegaPlus → n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : CompNormal β := by
  have h : OmegaFieldConj G β ℓ p := by
    rcases ht with rfl | rfl | rfl
    · exact omegaFieldConj_odd hp hp2 hG β hβ hout
    · exact omegaFieldConj_plus hp hp2 hG (hD4 rfl) β hβ hout
    · exact omegaFieldConj_minus hp hp2 hG β hβ hout
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, -, he⟩ := h.out
  refine CompNormal.of_congr e ?_
  rw [he]
  exact compNormal_fieldAutT S (by omega)

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

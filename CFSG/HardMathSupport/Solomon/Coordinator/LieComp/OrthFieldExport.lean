module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFacts
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily
import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

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

private theorem eq_of_isComponentOf_of_normal_quasisimple {S : Type} [Group S] [Finite S]
    {β : MulAut S} {J : Subgroup S} (hJC : J ≤ fixSubgroup β)
    [(J.subgroupOf (fixSubgroup β)).Normal] (hJq : CFSG.IsQuasisimple J)
    (hsol : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)))
    {K' : Subgroup S} (hK' : CFSG.Open.IsComponentOf K' (fixSubgroup β)) : K' = J := by
  obtain ⟨-, h⟩ := component_mem_named_factors (ι := Unit) (fun _ => J)
    (fun _ => ⟨hJC, CFSG.Open.IsSubnormal.step hJC inferInstance (CFSG.Open.IsSubnormal.refl _),
      LieSemisimple.open_isQuasisimple hJq⟩)
    (fun P hPC hP => by
      rw [iSup_const]
      exact LieSemisimple.perfect_le_of_solvable_quotient hJC hsol hPC
        (Subgroup.isPerfect_iff.1 ⟨hP⟩))
    hK'
  exact h

private theorem layer_and_eq_of_fix_eq {S : Type} [Group S] [Finite S] {β : MulAut S}
    {N J : Subgroup S} (hfix : fixSubgroup β = N) (hJN : J ≤ N) (hJn : (J.subgroupOf N).Normal)
    (hJq : CFSG.IsQuasisimple J) (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N)) :
    PerfectInLayer β ∧
      ∀ K' : Subgroup S, CFSG.Open.IsComponentOf K' (fixSubgroup β) → K' = J := by
  subst hfix
  haveI := hJn
  exact ⟨LieSemisimple.perfectInLayer_of_normal_quasisimple hJN hJq hsol,
    fun K' hK' => eq_of_isComponentOf_of_normal_quasisimple hJN hJq hsol hK'⟩

private theorem layer_comps_of_congr {q : ℕ} {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (hl : PerfectInLayer (MulAut.congr e β))
    (hc : ∀ K : Subgroup G, CFSG.Open.IsComponentOf K (fixSubgroup (MulAut.congr e β)) →
      ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
        ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X) :
    PerfectInLayer β ∧ ∀ K : Subgroup S, CFSG.Open.IsComponentOf K (fixSubgroup β) →
      ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
        ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : ∀ {K : Subgroup S}, CFSG.Open.IsComponentOf K (fixSubgroup β) →
      CFSG.Open.IsComponentOf (K.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) :=
    fun hK => by
      rw [hfix]
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β hl, fun K hK => ?_⟩
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := hc _ (hmapc hK)
  let g : ↥(K.map (e : S →* G)) ≃* ↥K :=
    (K.equivMapOfInjective (e : S →* G) e.injective).symm
  refine ⟨X, inferInstance, inferInstance, hX, (g : _ →* ↥K).comp f, g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

private theorem exists_central_epi_omega (S : SubfieldSetup k Q₀ Q σ p) (hd0 : 0 < d) :
    CFSG.IsQuasisimple ↥(⊤ : Subgroup ↥(orthDerived Q₀)) ∧
    ∃ π : ↥(⊤ : Subgroup ↥(orthDerived Q₀)) →* ↥(subfieldDerivedImage k S.hext),
      Function.Surjective π ∧ π.ker ≤ Subgroup.center ↥(⊤ : Subgroup ↥(orthDerived Q₀)) := by
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  obtain ⟨hperf, hcenter, -, hsimple, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts S.hnd₀ S.hT₀
  have hq : CFSG.Open.IsQuasisimple ↥(orthDerived Q₀) := by
    refine ⟨hperf.commutator_eq_top, ?_⟩
    have := hsimple
    exact (QuotientGroup.quotientMulEquivOfEq hcenter).isSimpleGroup
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv
    (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(orthDerived Q₀)) ≃* _)
    ⟨hperf, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq⟩,
    ?_⟩
  let π₁ : ↥(orthDerived Q₀) →* ProjOrthDerived Q₀ := QuotientGroup.mk' _
  let π : ↥(orthDerived Q₀) →* ↥(subfieldDerivedImage k S.hext) :=
    ((inclEquiv k S.hext hd0).toMonoidHom.comp
      (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge Q₀ hd0).symm.toMonoidHom).comp π₁
  have hπ : Function.Surjective π :=
    (inclEquiv k S.hext hd0).surjective.comp
      ((CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge Q₀ hd0).symm.surjective.comp
        (QuotientGroup.mk'_surjective _))
  refine ⟨π.comp (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(orthDerived Q₀)) ≃* _).toMonoidHom,
    hπ.comp (Subgroup.topEquiv.surjective), fun x hx => ?_⟩
  have hx' : Subgroup.topEquiv x ∈ π.ker := hx
  have h1 : π₁ (Subgroup.topEquiv x) = 1 := by
    rw [MonoidHom.mem_ker] at hx'
    have h2 : (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge Q₀ hd0).symm
        (π₁ (Subgroup.topEquiv x)) = 1 :=
      (inclEquiv k S.hext hd0).injective (by rw [map_one]; exact hx')
    exact (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge Q₀ hd0).symm.injective
      (by rw [map_one]; exact h2)
  have h3 : Subgroup.topEquiv x ∈ Subgroup.center ↥(orthDerived Q₀) := by
    rw [hcenter]
    exact (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subgroup.topEquiv.injective
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 h3 _

private theorem fieldAutT_layer_and_eq (S : SubfieldSetup k Q₀ Q σ p) (hd0 : 0 < d) :
    PerfectInLayer (fieldAutT Q σ S.hQσ) ∧
      ∀ K' : Subgroup (matrixProjectiveDerived Q),
        CFSG.Open.IsComponentOf K' (fixSubgroup (fieldAutT Q σ S.hQσ)) →
          K' = subfieldDerivedImage k S.hext := by
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd0 S.hnd₀ S.hT₀
  have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k S.hext) :=
    CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k S.hext hd0).symm
      (LieSemisimple.isQuasisimple_of_isSimpleGroup hsimp hnonab)
  have hJn := subfieldDerivedImage_normal k S.hext
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  exact layer_and_eq_of_fix_eq (Subgroup.ext fun t => fieldAutT_apply_iff S t)
    (subfieldDerivedImage_le k S.hext) hJn hJq inferInstance

private theorem exists_lieFactorData_cover (hOm : OmegaFactorFacts)
    (S : SubfieldSetup k Q₀ Q σ p) (hd0 : 0 < d) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData (ringChar K) X ∧
      ∃ g : X →* ↥(subfieldDerivedImage k S.hext),
        Function.Surjective g ∧ g.ker ≤ Subgroup.center X := by
  obtain ⟨hqT, π, hπ, hπk⟩ := exists_central_epi_omega S hd0
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := hOm k (Fin d → k) Q₀ S.hnd₀ ⊤ inferInstance hqT
  refine ⟨X, inferInstance, inferInstance, ?_, π.comp f, hπ.comp hf, fun x hx => ?_⟩
  · have hX' := hX
    rwa [Algebra.ringChar_eq k K] at hX'
  · have h2 : f x ∈ Subgroup.center ↥(⊤ : Subgroup ↥(orthDerived Q₀)) := hπk hx
    have h3 : x ∈ (Subgroup.center ↥(⊤ : Subgroup ↥(orthDerived Q₀))).comap f := h2
    rwa [comap_center_of_surjective hX.perfect f hf hfk] at h3

private theorem not_nonempty_altSix (hOm6 : OmegaAltSixFacts) (S : SubfieldSetup k Q₀ Q σ p)
    (hd : 7 ≤ d) :
    ¬ Nonempty ((↥(subfieldDerivedImage k S.hext) ⧸
      Subgroup.center ↥(subfieldDerivedImage k S.hext)) ≃* alternatingGroup (Fin 6)) := by
  have hd0 : 0 < d := by omega
  rintro ⟨a⟩
  obtain ⟨hqT, π, hπ, hπk⟩ := exists_central_epi_omega S hd0
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hqT.1.commutator_eq_top π hπ hπk
  have := hOm6 k (Fin d → k) Q₀ S.hnd₀ ⊤ inferInstance hqT ⟨e.trans a⟩
  have h4 := this.2
  rw [Module.finrank_fin_fun] at h4
  omega

private theorem lieCompExport_fieldAutT (hOm : OmegaFactorFacts) (hOm6 : OmegaAltSixFacts)
    (S : SubfieldSetup k Q₀ Q σ p) (hd : 7 ≤ d) :
    LieCompExport (ringChar K) (fieldAutT Q σ S.hQσ) := by
  have hd0 : 0 < d := by omega
  obtain ⟨hl, hK⟩ := fieldAutT_layer_and_eq S hd0
  refine ⟨hl, fun K' hK' => ?_, fun ⟨K', hK', a⟩ => ?_⟩
  · obtain rfl := hK K' hK'
    exact exists_lieFactorData_cover hOm S hd0
  · obtain rfl := hK K' hK'
    exact (not_nonempty_altSix hOm6 S hd a).elim

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
    (φ : G ≃* matrixProjectiveDerived Q) (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
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

private theorem lieCompExport_of_omegaFieldConj (hOm : OmegaFactorFacts) (hOm6 : OmegaAltSixFacts)
    {G : Type} [Group G] {β : MulAut G} {ℓ p : ℕ} (h : OmegaFieldConj G β ℓ p) :
    LieCompExport ℓ β := by
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, hch, he⟩ := h.out
  have := lieCompExport_fieldAutT hOm hOm6 S hd
  rw [← he, hch] at this
  exact LieCompExport.of_congr e this

private theorem layer_comps_of_omegaFieldConj (hOm : OmegaFactorFacts) {G : Type} [Group G]
    {β : MulAut G} {ℓ p : ℕ} (h : OmegaFieldConj G β ℓ p) :
    PerfectInLayer β ∧ ∀ K : Subgroup G, CFSG.Open.IsComponentOf K (fixSubgroup β) →
      ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData ℓ X ∧
        ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, hch, he⟩ := h.out
  have hd0 : 0 < d := by omega
  obtain ⟨hl, hK⟩ := fieldAutT_layer_and_eq S hd0
  have hcov := exists_lieFactorData_cover hOm S hd0
  rw [hch] at hcov
  rw [← he] at hl hK
  refine layer_comps_of_congr e hl fun K' hK' => ?_
  obtain rfl := hK K' hK'
  exact hcov

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

theorem omega_outer_layer_comps (hOm : OmegaFactorFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f)
    (hD4 : t = .POmegaPlus → n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) :
    PerfectInLayer β ∧ ∀ K : Subgroup G, CFSG.Open.IsComponentOf K (fixSubgroup β) →
      ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData ℓ X ∧
        ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X := by
  refine layer_comps_of_omegaFieldConj hOm (p := p) ?_
  rcases ht with rfl | rfl | rfl
  · exact omegaFieldConj_odd hp hp2 hG β hβ hout
  · exact omegaFieldConj_plus hp hp2 hG (hD4 rfl) β hβ hout
  · exact omegaFieldConj_minus hp hp2 hG β hβ hout

theorem lieCompExport_omega_outer (hOm : OmegaFactorFacts) (hOm6 : OmegaAltSixFacts)
    {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] [Finite G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f)
    (hD4 : ¬(t = .POmegaPlus ∧ n = 4)) (β : MulAut G) (hβ : β ^ 3 = 1)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : LieCompExport ℓ β := by
  refine lieCompExport_of_omegaFieldConj hOm hOm6 (p := 3) ?_
  rcases ht with rfl | rfl | rfl
  · exact omegaFieldConj_odd Nat.prime_three (by norm_num) hG β hβ hout
  · exact omegaFieldConj_plus Nat.prime_three (by norm_num) hG
      (fun h => absurd ⟨rfl, h⟩ hD4) β hβ hout
  · exact omegaFieldConj_minus Nat.prime_three (by norm_num) hG β hβ hout

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

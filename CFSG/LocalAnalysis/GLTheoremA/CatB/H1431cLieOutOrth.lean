module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Matrix QuadraticMap
open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.RankThree.Classical.SteinbergBY
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.HardMathSupport.Lang.Proving
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalNoninner (mem_of_pow_eq_one_of_relIndex_eq_two_pow)
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal
  OuterAutomorphisms.congr_conj)
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open CFSG.HardMathSupport.Dickson.Sec6 (FamDHigh FamTwD blueprintLieModel_D
  blueprintLieModel_twistedD)
open CFSG.LocalAnalysis.GLTheoremA.I1431C2 (catalogIs_of_mulEquiv
  conj_ne_of_not_mem_innAutDerived)
open scoped commutatorElement

variable {T Pc : TauCeti.CFSGIndex → Prop} {tm tf tN : ℕ}

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem typeLayer_fieldAutT {G : Prop} (S : SubfieldSetup k Q₀ Q σ p)
    (hG : catalogIs (matrixProjectiveDerived Q₀) T → G) :
    TypeLayer T (fieldAutT Q σ S.hQσ) G := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have e := inclEquiv k S.hext hd
  have hJs : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := e.symm.isSimpleGroup
  have hJnab : ∃ a b : ↥(subfieldDerivedImage k S.hext), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  have hJn := subfieldDerivedImage_normal k S.hext
  haveI := hJn
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  exact typeLayer_of_fixed_normal_simple _ _ _ hfix (subfieldDerivedImage_le k S.hext)
    inferInstance hJs hJnab fun hT => hG (catalogIs_of_mulEquiv e.symm hT)

end Field

section Tags


variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ}

theorem typeLayer_fieldAutT_plus (hD : LieSOutType T tm tf tN) {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hk : Nat.card k = 2 ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p) :
    TypeLayer T (fieldAutT (coordinateQuadPlus n K) σ S.hQσ) False := by
  refine typeLayer_fieldAutT S fun hT => ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n 2 e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm⟩⟩
  exact absurd (hD.det hT hmodel).1 (by decide)

theorem typeLayer_fieldAutT_minus (hD : LieSOutType T tm tf tN) {n e : ℕ} (hn : 1 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n 2 e) (hk : Nat.card k = 2 ^ e)
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (S : SubfieldSetup k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) σ p) :
    TypeLayer T (fieldAutT (coordinateQuadMinus n K hn (b : K) (c : K)) σ S.hQσ) False := by
  refine typeLayer_fieldAutT S fun hT => ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadMinus n k hn b c)) .POmegaMinus n
      2 e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk, b, c,
      hirr, ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n k b c)
        (coe_quadMinus n k b c)).symm⟩⟩
  exact absurd (hD.det hT hmodel).1 (by decide)

end Tags

section Descent

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem typeLayer_of_fieldDescent {G : Prop} {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p) (U : similarityPairs Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hfield : TypeLayer T (fieldAutT Q' σ S.hQσ) G) [Finite (matrixProjectiveDerived Q)] :
    TypeLayer T (matrixProjectiveConjugationHom Q U) G := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ (matrixProjectiveConjugationHom Q U)) x =
        Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  haveI : Finite (matrixProjectiveDerived Q') := Finite.of_equiv _ Θ.toEquiv
  exact typeLayer_congr Θ (hcongr ▸ hfield)

end Descent

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem typeLayer_of_gates_outer {G : Prop} {H : Type} [Group H] [Finite H]
    (e : H ≃* matrixProjectiveDerived Q) (hg : OrthogonalGates Q f)
    (β : MulAut H) (hβ : β ^ 3 = 1) (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hout : ∀ a : H, MulAut.conj a ≠ β)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = 3 → TypeLayer T a G) : TypeLayer T β G := by
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · exfalso
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_three' hg hD hβ'
    refine hout (e.symm t) ((MulAut.congr e).injective ?_)
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  · have hne1 : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e β) = 3 := orderOf_eq_prime hβ' hne1
    haveI : Finite (matrixProjectiveDerived Q) := Finite.of_equiv H e.toEquiv
    exact typeLayer_congr e (hdesc _ hE hD hord)

end Gates

section Outer


open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem typeLayer_omega_plus_of_E (hD : LieSOutType T tm tf tN) {H : Type} [Group H] [Finite H]
    {n f : ℕ}
    (hG : StatedClassicalModel H .POmegaPlus n 2 f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    {β : MulAut H} (hβ : β ^ 3 = 1) (hout : ∀ a : H, MulAut.conj a ≠ β)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K)) : TypeLayer T β False := by
  obtain ⟨-, -, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates H .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv H (coordinatePlusWitnessEquiv K e).toEquiv
  refine typeLayer_of_gates_outer (coordinatePlusWitnessEquiv K e) hgates β hβ hE hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' H .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' (by omega : 3 ≤ n)
  exact typeLayer_of_fieldDescent S U Θ g' hg'l hg'r hΘ
    (typeLayer_fieldAutT_plus hD hCM.1 hcard' S)

theorem typeLayer_omega_plus_outer (hD : LieSOutType T tm tf tN) {H : Type} [Group H] [Finite H]
    {n f : ℕ}
    (hG : StatedClassicalModel H .POmegaPlus n 2 f) (hn5 : 5 ≤ n)
    {β : MulAut H} (hβ : β ^ 3 = 1) (hout : ∀ a : H, MulAut.conj a ≠ β) :
    TypeLayer T β False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates H .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
    (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 hn5
  exact typeLayer_omega_plus_of_E hD hG K hK e hβ hout (mem_E_of_pow_eq_one_three hgates htop)

theorem typeLayer_omega_minus_outer (hD : LieSOutType T tm tf tN) {H : Type} [Group H] [Finite H]
    {n f : ℕ}
    (hG : StatedClassicalModel H .POmegaMinus n 2 f) {β : MulAut H} (hβ : β ^ 3 = 1)
    (hout : ∀ a : H, MulAut.conj a ≠ β) : TypeLayer T β False := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates H .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant H .POmegaMinus (.inr rfl) n 2 f hG)
      hn1 K hK b c hirr).2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv H (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  refine typeLayer_of_gates_outer (coordinateMinusWitnessEquiv K hn1 b c e) hgates β hβ
    (mem_E_of_pow_eq_one_three hgates htop) hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' H .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f 3 hG Nat.prime_three (by norm_num) hn1 K hK b c hirr e a haE haD
    hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by
    rw [hUr]
    exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 3) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m (by norm_num)
  have hcard'' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ m := by
    rw [← hdiv]
    exact hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = 2 ^ (m * 3) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1 hcard'' hK'
  rw [← hUκ]
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' hn4 hdeg b' c' hirr'
  exact typeLayer_of_fieldDescent S U Θ g' hg'l hg'r hΘ
    (typeLayer_fieldAutT_minus hD hn1 hCM.1 hcard' b' c' hirr' S)

end Outer

section Family


theorem lieSOut_dHigh (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamDHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | D r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr5 : 5 ≤ r := hF
    have hm := blueprintLieModel_D r q hv e
    have hC : StatedClassicalModel S .POmegaPlus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [hq2] at hC
    exact hp.apply
      (typeLayer_omega_plus_outer hD hC hr5 hp.1 (conj_ne_of_not_mem_innAutDerived hα))
  | _ => exact hF.elim

theorem lieSOut_twD (hD : LieSOutType T tm tf tN) : TypeOuterAt T Pc FamTwD := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | twistedD r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_twistedD r q hv e
    have hC : StatedClassicalModel S .POmegaMinus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [hq2] at hC
    exact hp.apply
      (typeLayer_omega_minus_outer hD hC hp.1 (conj_ne_of_not_mem_innAutDerived hα))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end


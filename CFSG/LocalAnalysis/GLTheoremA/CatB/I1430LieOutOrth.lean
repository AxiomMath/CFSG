module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutDefs

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


section Tags

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ}

theorem typeLayer_fieldAutT_plusW (hD : LieSOutTypeW T tm tf tN) {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hk : Nat.card k = 2 ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p) :
    TypeLayer T (fieldAutT (coordinateQuadPlus n K) σ S.hQσ) False := by
  refine typeLayer_fieldAutT S fun hT => ?_
  have hmodel : LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n 2 e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k) (coe_quadPlus n k)).symm⟩⟩
  exact absurd (hD.det hT hmodel).1 (by decide)

theorem typeLayer_fieldAutT_minusW (hD : LieSOutTypeW T tm tf tN) {n e : ℕ} (hn : 1 ≤ n)
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

section Outer

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem typeLayer_omega_plus_of_EW (hD : LieSOutTypeW T tm tf tN) {H : Type} [Group H] [Finite H]
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
    (typeLayer_fieldAutT_plusW hD hCM.1 hcard' S)

theorem typeLayer_omega_plus_outerW (hD : LieSOutTypeW T tm tf tN) {H : Type} [Group H] [Finite H]
    {n f : ℕ}
    (hG : StatedClassicalModel H .POmegaPlus n 2 f) (hn5 : 5 ≤ n)
    {β : MulAut H} (hβ : β ^ 3 = 1) (hout : ∀ a : H, MulAut.conj a ≠ β) :
    TypeLayer T β False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates H .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
    (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 hn5
  exact typeLayer_omega_plus_of_EW hD hG K hK e hβ hout (mem_E_of_pow_eq_one_three hgates htop)

theorem typeLayer_omega_minus_outerW (hD : LieSOutTypeW T tm tf tN) {H : Type} [Group H] [Finite H]
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
    (typeLayer_fieldAutT_minusW hD hn1 hCM.1 hcard' b' c' hirr' S)

end Outer

section Family

theorem lieSOut_dHighW (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamDHigh := by
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
      (typeLayer_omega_plus_outerW hD hC hr5 hp.1 (conj_ne_of_not_mem_innAutDerived hα))
  | _ => exact hF.elim

theorem lieSOut_twDW (hD : LieSOutTypeW T tm tf tN) : TypeOuterAt T Pc FamTwD := by
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
      (typeLayer_omega_minus_outerW hD hC hp.1 (conj_ne_of_not_mem_innAutDerived hα))
  | _ => exact hF.elim

end Family

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

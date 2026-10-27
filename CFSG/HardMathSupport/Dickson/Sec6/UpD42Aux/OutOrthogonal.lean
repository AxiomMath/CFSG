module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodOrthogonal
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Chev2Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Matrix QuadraticMap
open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.Sec66T
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.RankThree.Classical.SteinbergBY CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.HardMathSupport.Lang.Proving
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification (OuterAutomorphisms.congr_conj)
open CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
  {σ : K ≃+* K} {p : ℕ}

theorem isD42Type_of_upD42Pumpup_fieldAutT (S : SubfieldSetup k Q₀ Q σ p)
    (hx : UpD42Pumpup (matrixProjectiveDerived Q) (fieldAutT Q σ S.hQσ)) :
    IsCatalogLieIso (matrixProjectiveDerived Q₀) IsD42Index := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hs, hnab⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  haveI := hs
  let e := inclEquiv k S.hext hd
  have hsJ : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) := e.symm.isSimpleGroup
  have hnabJ : ∃ a b : ↥(subfieldDerivedImage k S.hext), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e a, e b, fun he => hab ?_⟩
    exact e.injective (by simpa only [map_mul] using he)
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  haveI := subfieldDerivedImage_normal k S.hext
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  obtain ⟨-, -, I, hI, hD⟩ := hx
  rw [hfix] at hI
  exact IsCatalogLieIso.of_mulEquiv e.symm
    (isD42Type_of_component_of_normal_simple hI hD _
      (subfieldDerivedImage_le k S.hext) inferInstance hsJ hnabJ)

theorem rank_field_of_upD42Pumpup_fieldAutT_plus {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hk : Nat.card k = 2 ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p)
    (hx : UpD42Pumpup (matrixProjectiveDerived (coordinateQuadPlus n K))
      (fieldAutT (coordinateQuadPlus n K) σ S.hQσ)) : n = 4 ∧ e = 1 := by
  have hm : LieModel (matrixProjectiveDerived (coordinateQuadPlus n k)) .POmegaPlus n 2 e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk,
      ⟨(statedProjectiveReindexEquiv (plusIndexEquiv n) (quadPlus n k)
        (coe_quadPlus n k)).symm⟩⟩
  exact (classical_type_of_isD42 (by decide) hm
    (isD42Type_of_upD42Pumpup_fieldAutT S hx)).2

theorem not_upD42Pumpup_fieldAutT_plus {n e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hn : 5 ≤ n) (hk : Nat.card k = 2 ^ e)
    (S : SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p) :
    ¬ UpD42Pumpup (matrixProjectiveDerived (coordinateQuadPlus n K))
      (fieldAutT (coordinateQuadPlus n K) σ S.hQσ) := by
  intro hx
  have h := (rank_field_of_upD42Pumpup_fieldAutT_plus hadm hk S hx).1
  omega

theorem not_upD42Pumpup_fieldAutT_minus {n e : ℕ} (hn : 1 ≤ n)
    (hadm : StatedLieAdmissible .POmegaMinus n 2 e) (hk : Nat.card k = 2 ^ e)
    (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (S : SubfieldSetup k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) σ p) :
    ¬ UpD42Pumpup (matrixProjectiveDerived (coordinateQuadMinus n K hn (b : K) (c : K)))
      (fieldAutT (coordinateQuadMinus n K hn (b : K) (c : K)) σ S.hQσ) := by
  intro hx
  have hm : LieModel (matrixProjectiveDerived (coordinateQuadMinus n k hn b c))
      .POmegaMinus n 2 e :=
    (lieModel_classical_iff (by decide)).mpr ⟨hadm, ↥k, inferInstance, inferInstance, hk, b, c,
      hirr, ⟨(statedProjectiveReindexEquiv (minusIndexEquiv n hn) (quadMinus n k b c)
        (coe_quadMinus n k b c)).symm⟩⟩
  have ht := (classical_type_of_isD42 (by decide) hm
    (isD42Type_of_upD42Pumpup_fieldAutT S hx)).1
  cases ht

theorem UpD42Pumpup.orthogonal_fieldDescent {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p)
    (U : similarityPairs Q) (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hx : UpD42Pumpup (matrixProjectiveDerived Q) (matrixProjectiveConjugationHom Q U)) :
    UpD42Pumpup (matrixProjectiveDerived Q') (fieldAutT Q' σ S.hQσ) := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) =
      fieldAutT Q' σ S.hQσ := by
    ext x
    change Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) = _
    rw [hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  exact hcongr ▸ hx.congr Θ

theorem not_upD42Pumpup_of_orthogonal_fieldDescent {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p)
    (U : similarityPairs Q) (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q')
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x))
    (hfield : ¬ UpD42Pumpup (matrixProjectiveDerived Q') (fieldAutT Q' σ S.hQσ)) :
    ¬ UpD42Pumpup (matrixProjectiveDerived Q) (matrixProjectiveConjugationHom Q U) :=
  fun hx => hfield (hx.orthogonal_fieldDescent S U Θ g' hl hr hΘ)

end Field

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem not_upD42Pumpup_of_orthogonal_gates {G : Type} [Group G] [Finite G]
    (e : G ≃* matrixProjectiveDerived Q) (hg : OrthogonalGates Q f)
    (β : MulAut G) (hE : MulAut.congr e β ∈ matrixProjectiveImage Q)
    (hout : ∀ a : G, MulAut.conj a ≠ β)
    (hdesc : ∀ a ∈ matrixProjectiveImage Q, a ∉ (linearConjugationHom Q).range →
      orderOf a = 3 → ¬ UpD42Pumpup (matrixProjectiveDerived Q) a) :
    ¬ UpD42Pumpup G β := by
  intro hx
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hx.1, map_one]
  by_cases hD : MulAut.congr e β ∈ (linearConjugationHom Q).range
  · obtain ⟨t, ht⟩ := mem_inner_of_mem_D_three' hg hD hβ'
    refine hout (e.symm t) ((MulAut.congr e).injective ?_)
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  · have hne : MulAut.congr e β ≠ 1 := fun h => hD (h ▸ Subgroup.one_mem _)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e β) = 3 := orderOf_eq_prime hβ' hne
    exact hdesc _ hE hD hord (hx.congr e)

end Gates

theorem not_upD42Pumpup_omega_plus_outer {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n 2 f) (hn5 : 5 ≤ n) (β : MulAut G)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : ¬ UpD42Pumpup G β := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ :=
    (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 hn5
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G (coordinatePlusWitnessEquiv K e).toEquiv
  refine not_upD42Pumpup_of_orthogonal_gates (coordinatePlusWitnessEquiv K e) hgates β
    (mem_E_of_pow_eq_one_three hgates htop) hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f 3 hG Nat.prime_three (by norm_num) K hK e a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 3) := by
    rw [hUr]; exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  rw [← hUκ]
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' (by omega : 3 ≤ n)
  exact not_upD42Pumpup_of_orthogonal_fieldDescent S U Θ g' hg'l hg'r hΘ
    (not_upD42Pumpup_fieldAutT_plus hCM.1 hn5 hcard' S)

theorem not_upD42Pumpup_omega_minus_outer {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n 2 f) (β : MulAut G)
    (hout : ∀ a : G, MulAut.conj a ≠ β) : ¬ UpD42Pumpup G β := by
  obtain ⟨hℓ, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl)
      n 2 f hG) hn1 K hK b c hirr).2
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv G (coordinateMinusWitnessEquiv K hn1 b c e).toEquiv
  refine not_upD42Pumpup_of_orthogonal_gates (coordinateMinusWitnessEquiv K hn1 b c e)
    hgates β (mem_E_of_pow_eq_one_three hgates htop) hout ?_
  intro a haE haD hap
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f 3 hG Nat.prime_three (by norm_num) hn1 K hK b c hirr e
    a haE haD hap
  obtain ⟨g, hgE⟩ := haE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 3) := by
    rw [hUr]; exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by rw [hm]; exact Nat.mul_div_cancel_left m (by norm_num)
  have hcard'' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ m := by
    rw [← hdiv]; exact hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm; omega
    · exact h
  have hK' : Nat.card K = 2 ^ (m * 3) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1 hcard'' hK'
  rw [← hUκ]
  have S := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' hn4 hdeg b' c' hirr'
  exact not_upD42Pumpup_of_orthogonal_fieldDescent S U Θ g' hg'l hg'r hΘ
    (not_upD42Pumpup_fieldAutT_minus hn1 hCM.1 hcard' b' c' hirr' S)

theorem upD42Chev2Out_orthogonal_holds : UpD42Chev2Out isOrthogonalIdx := by
  intro S _ _ _ _ ⟨d, hv⟩ hd hc ⟨e⟩ α hout hx
  cases d with
  | B r q => exact (hd.2 hc).elim
  | D r q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr4 : 4 ≤ r := hr
    have hne : r ≠ 4 := hd
    have hm := blueprintLieModel_D r q hv e
    have hC : StatedClassicalModel S .POmegaPlus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [show q.p = 2 from hc] at hC
    exact (not_upD42Pumpup_omega_plus_outer hC (by omega) α (fun a h => hout ⟨a, h⟩) hx).elim
  | twistedD r q =>
    have hm := blueprintLieModel_twistedD r q hv e
    have hC : StatedClassicalModel S .POmegaMinus r q.p q.exponent :=
      (lieModel_classical_iff (by decide)).mp hm
    rw [show q.p = 2 from hc] at hC
    exact (not_upD42Pumpup_omega_minus_outer hC α (fun a h => hout ⟨a, h⟩) hx).elim
  | _ => exact hd.elim

end CFSG.HardMathSupport.Dickson.Sec6

end

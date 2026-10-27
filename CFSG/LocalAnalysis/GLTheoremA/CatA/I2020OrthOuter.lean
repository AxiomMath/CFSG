module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Transfer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020NotJType
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeSubfield
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Open.StatedAPI
open CFSG.ComponentClassification (OuterAutomorphisms.congr_conj)
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.RankThree.PartOne.KCOrthogonalDescent
open CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (mem_E_of_pow_eq_one_omega mem_inner_of_mem_D_omega perfect_le_of_solvable_quotient)
open CFSG.HardMathSupport.Lang.Proving
  (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.RankThree.Classical.SteinbergBY
open scoped commutatorElement

private theorem pComponent_eq_bot_or_eq_subfield {K : Type} [Field K] [Finite K] {d : ℕ}
    {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} {p : ℕ} (hp : p.Prime) (hext : IsExtension k Q₀ Q)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ)
    {J : Subgroup (matrixProjectiveDerived Q)}
    (hJ : GLAPComponent p (fixSubgroup (fieldAutT Q σ hQσ)) J) :
    J = ⊥ ∨ J = subfieldDerivedImage k hext := by
  obtain ⟨⟨-, hJs, -⟩, -, hfixiff, hJ₀N, hJ₀norm, hquot, -⟩ := hconc
  haveI := hJ₀norm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hquot.isNilpotent
  haveI : Group.IsSolvable
      (↥(subfieldFixedGroup k Q₀ Q) ⧸
        (subfieldDerivedImage k hext).subgroupOf (subfieldFixedGroup k Q₀ Q)) :=
    IsNilpotent.to_isSolvable
  have hfix : fixSubgroup (fieldAutT Q σ hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext hfixiff
  have hperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hLJ : J ≤ subfieldDerivedImage k hext := by
    have hJ' := hJ
    rw [hfix] at hJ'
    exact perfect_le_of_solvable_quotient hJ₀N inferInstance hJ'.1 hperf
  have hsn : IsSubnormal J (subfieldDerivedImage k hext) := by
    have h1 := hJ.2.1
    rw [hfix] at h1
    have h2 := h1.inf_of_le hJ₀N
    rwa [inf_eq_left.2 hLJ] at h2
  exact hsn.eq_bot_or_eq_of_isSimpleGroup hJs



private theorem false_of_pComponent_subfield {K : Type} [Field K] [Finite K] {d : ℕ}
    {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} {p q f : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : 0 < d) (hext : IsExtension k Q₀ Q)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ)
    {t : StatedLieTag} {n : ℕ} (htn : NotJTypeTag t n)
    (hmodel : StatedClassicalModel (matrixProjectiveDerived Q₀) t n q f)
    [Finite (matrixProjectiveDerived Q)]
    {J : Subgroup (matrixProjectiveDerived Q)}
    (hJ : GLAPComponent p (fixSubgroup (fieldAutT Q σ hQσ)) J) (hJT : JType p q J) : False := by
  have hcases := pComponent_eq_bot_or_eq_subfield hp hext hQσ hconc hJ
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hq' := isQuasisimple_pQuot_of_glaPComponent hp (hbot ▸ hJ)
    haveI : Subsingleton (PQuot p J) := by
      rw [hbot]
      change Subsingleton (↥(⊥ : Subgroup (matrixProjectiveDerived Q)) ⧸
        GLAPPrimeCore p ↥(⊥ : Subgroup (matrixProjectiveDerived Q)))
      infer_instance
    haveI : Subsingleton (PQuot p J ⧸ Subgroup.center (PQuot p J)) := inferInstance
    exact (not_subsingleton_iff_nontrivial.mpr hq'.2.toNontrivial) inferInstance
  have hJ₀ : J = subfieldDerivedImage k hext := hcases.resolve_left hJne
  rw [hJ₀] at hJ hJT
  obtain ⟨⟨-, hJs, hnonab⟩, -, hfixiff, hJ₀N, hJ₀norm, hquot, -⟩ := hconc
  haveI := hJ₀norm
  have hqJ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hcore : GLAPPrimeCore p ↥(subfieldDerivedImage k hext) = ⊥ := by
    rcases hJs.eq_bot_or_eq_top_of_normal
      (GLAPPrimeCore p ↥(subfieldDerivedImage k hext)) with h | h
    · exact h
    · exfalso
      haveI : Subsingleton (PQuot p (subfieldDerivedImage k hext)) := by
        change Subsingleton (↥(subfieldDerivedImage k hext) ⧸
          GLAPPrimeCore p ↥(subfieldDerivedImage k hext))
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton
          (PQuot p (subfieldDerivedImage k hext) ⧸
            Subgroup.center (PQuot p (subfieldDerivedImage k hext))) := inferInstance
      exact (not_subsingleton_iff_nontrivial.mpr hqJ.2.toNontrivial) inferInstance
  have hZ : Subgroup.center ↥(subfieldDerivedImage k hext) = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnonab
  have hmodel' : StatedClassicalModel (PSimple p (subfieldDerivedImage k hext)) t n q f :=
    statedClassicalModel_of_mulEquiv
      ((inclEquiv k hext hd).trans
        (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf
          (subfieldDerivedImage k hext) hcore hZ).symm) hmodel
  exact (not_jType_of_statedClassicalModel hq2 htn hmodel') hJT

private theorem false_of_fieldModel {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] {d : ℕ} {k : Subfield K} {Q₀ : QuadraticForm k (Fin d → k)}
    {Q : QuadraticForm K (Fin d → K)}
    {σ : K ≃+* K} {p q f : ℕ} (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hd : 0 < d)
    (hext : IsExtension k Q₀ Q) (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))
    (hconc : SubfieldConclusion k Q₀ Q σ p hext hQσ)
    {t : StatedLieTag} {n : ℕ} (htn : NotJTypeTag t n)
    (hmodel : StatedClassicalModel (matrixProjectiveDerived Q₀) t n q f)
    [Finite (matrixProjectiveDerived Q)]
    (Θ : X ≃* matrixProjectiveDerived Q) (β' : MulAut X)
    (hcongr : MulAut.congr Θ β' = fieldAutT Q σ hQσ)
    {J' : Subgroup X} (hJ' : GLAPComponent p (fixSubgroup β') J')
    (hJT' : JType p q J') : False := by
  have hJ''0 : GLAPComponent p ((fixSubgroup β').map Θ.toMonoidHom)
      (J'.map Θ.toMonoidHom) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp Θ hJ'
  have hfixΘ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr Θ β'
  have hJ'' : GLAPComponent p (fixSubgroup (fieldAutT Q σ hQσ)) (J'.map Θ.toMonoidHom) := by
    rw [← hcongr, hfixΘ]
    exact hJ''0
  have hJT'' : JType p q (J'.map Θ.toMonoidHom) := (jType_map_mulEquiv hp Θ).1 hJT'
  exact false_of_pComponent_subfield hp hq hq2 hd hext hQσ hconc htn hmodel hJ'' hJT''

private theorem orthOuter_odd (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (G : Type) [Group G] [Finite G] (f : ℕ)
    (hG : StatedClassicalModel G .POmegaOdd 3 q f)
    (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a)
    {J : Subgroup G} (hJ : GLAPComponent p (fixSubgroup β) J) (hJT : JType p q J) : False := by
  obtain ⟨-, hf, -, -⟩ := hG.1
  obtain ⟨K, hfieldK, hfinK, hK, ⟨e⟩⟩ := hG.2
  letI := hfieldK
  letI := hfinK
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) 3 q f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadOdd 3 K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) 3 q f hG) K hK).2
  let e' := coordinateOddWitnessEquiv K e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := Finite.of_equiv _ e'.toEquiv
  let β' : MulAut (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := MulAut.congr e' β
  have hβ' : β' ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE : β' ∈ matrixProjectiveImage (coordinateQuadOdd 3 K) :=
    mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) hβ'
  have hD : β' ∉ (linearConjugationHom (coordinateQuadOdd 3 K)).range := by
    intro hmem
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hgates hp hp2 hmem hβ'
    apply hnot (e'.symm t)
    have hcongr : MulAut.congr e' (MulAut.conj (e'.symm t)) = MulAut.congr e' β := by
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
    exact ((MulAut.congr e').injective hcongr).symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf β' = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  let J' : Subgroup (matrixProjectiveDerived (coordinateQuadOdd 3 K)) := J.map e'.toMonoidHom
  have hJ' : GLAPComponent p (fixSubgroup β') J' := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp e' hJ
    have hfix : fixSubgroup β' = (fixSubgroup β).map e'.toMonoidHom :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e' β
    rw [hfix]
    exact h1
  have hJT' : JType p q J' := (jType_map_mulEquiv hp e').1 hJT
  obtain ⟨hpf, hrest⟩ := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd
    (Or.inl rfl) 3 q f p hG hp hp2 K hK e β' hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hord1, hcard, U, c, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, hS₀, hmodel, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = q ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hKbig : Nat.card K = q ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hadm : StatedLieAdmissible .POmegaOdd 3 q (f / p) := ⟨hq, hfp, by omega, hq2⟩
  obtain ⟨-, hconc⟩ := (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
    .POmegaOdd (Or.inl rfl) 3 q (f / p) p) hadm hp hp2 (Ne.symm hqp)
    K (semilinearFixedSubfield U.val.right) hcard' hKbig U.val.right hord' hσk
  have hg' : g' = fieldPair (coordinateQuadOdd 3 K) U.val.right
      (coordinateQuadOdd_fieldAut 3 U.val.right) :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hcongr : MulAut.congr Θ β' = fieldAutT (coordinateQuadOdd 3 K) U.val.right
      (coordinateQuadOdd_fieldAut 3 U.val.right) := by
    rw [← hUκ]
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ
        (matrixProjectiveConjugationHom (coordinateQuadOdd 3 K) U)) x =
        Θ (matrixProjectiveConjugationHom (coordinateQuadOdd 3 K) U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  have hmodelSmall : StatedClassicalModel
      (matrixProjectiveDerived (coordinateQuadOdd 3 (semilinearFixedSubfield U.val.right)))
      .POmegaOdd 3 q (f / p) :=
    ⟨hadm, semilinearFixedSubfield U.val.right, inferInstance, inferInstance, hcard',
      ⟨(coordinateOddWitnessEquiv (n := 3) (semilinearFixedSubfield U.val.right)
        (MulEquiv.refl _)).symm⟩⟩
  exact false_of_fieldModel hp hq hq2 (by omega)
    (coordinateQuadOdd_isExtension (semilinearFixedSubfield U.val.right) 3)
    (coordinateQuadOdd_fieldAut 3 U.val.right) hconc
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) hmodelSmall Θ β' hcongr hJ' hJT'

theorem orthOuter_plus_of_mem_image (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (G : Type) [Group G] [Finite G] (f : ℕ)
    (hG : StatedClassicalModel G .POmegaPlus 4 q f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)))
    (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K))
    {J : Subgroup G} (hJ : GLAPComponent p (fixSubgroup β) J) (hJT : JType p q J) : False := by
  obtain ⟨-, hf, -⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 q f hG K hK e
  let e' := coordinatePlusWitnessEquiv K e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := Finite.of_equiv _ e'.toEquiv
  let β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := MulAut.congr e' β
  have hβ' : β' ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE' : β' ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := hE
  have hD : β' ∉ (linearConjugationHom (coordinateQuadPlus 4 K)).range := by
    intro hmem
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hgates hp hp2 hmem hβ'
    apply hnot (e'.symm t)
    have hcongr : MulAut.congr e' (MulAut.conj (e'.symm t)) = MulAut.congr e' β := by
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
    exact ((MulAut.congr e').injective hcongr).symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf β' = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  let J' : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := J.map e'.toMonoidHom
  have hJ' : GLAPComponent p (fixSubgroup β') J' := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp e' hJ
    have hfix : fixSubgroup β' = (fixSubgroup β).map e'.toMonoidHom :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e' β
    rw [hfix]
    exact h1
  have hJT' : JType p q J' := (jType_map_mulEquiv hp e').1 hJT
  obtain ⟨hpf, hrest⟩ := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 q f p hG hp hp2 K hK e β' hE' hD hord
  obtain ⟨g, hgE⟩ := hE'
  obtain ⟨hord1, hcard, U, c, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨ν, S₀, hS₀, hmodel, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = q ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hKbig : Nat.card K = q ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hadm : StatedLieAdmissible .POmegaPlus 4 q (f / p) := ⟨hq, hfp, by omega⟩
  obtain ⟨-, hconc⟩ := (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
    .POmegaPlus (Or.inr (Or.inl rfl)) 4 q (f / p) p) hadm hp hp2 (Ne.symm hqp)
    K (semilinearFixedSubfield U.val.right) hcard' hKbig U.val.right hord' hσk
  have hg' : g' = fieldPair (coordinateQuadPlus 4 K) U.val.right
      (coordinateQuadPlus_fieldAut 4 U.val.right) :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hcongr : MulAut.congr Θ β' = fieldAutT (coordinateQuadPlus 4 K) U.val.right
      (coordinateQuadPlus_fieldAut 4 U.val.right) := by
    rw [← hUκ]
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ
        (matrixProjectiveConjugationHom (coordinateQuadPlus 4 K) U)) x =
        Θ (matrixProjectiveConjugationHom (coordinateQuadPlus 4 K) U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  have hmodelSmall : StatedClassicalModel
      (matrixProjectiveDerived (coordinateQuadPlus 4 (semilinearFixedSubfield U.val.right)))
      .POmegaPlus 4 q (f / p) :=
    ⟨hadm, semilinearFixedSubfield U.val.right, inferInstance, inferInstance, hcard',
      ⟨(coordinatePlusWitnessEquiv (n := 4) (semilinearFixedSubfield U.val.right)
        (MulEquiv.refl _)).symm⟩⟩
  exact false_of_fieldModel hp hq hq2 (by omega)
    (coordinateQuadPlus_isExtension (semilinearFixedSubfield U.val.right) 4)
    (coordinateQuadPlus_fieldAut 4 U.val.right) hconc
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hmodelSmall Θ β' hcongr hJ' hJT'

private theorem orthOuter_plus (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (G : Type) [Group G] [Finite G] (f : ℕ)
    (hG : StatedClassicalModel G .POmegaPlus 4 q f) (hp3 : p ≠ 3)
    (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a)
    {J : Subgroup G} (hJ : GLAPComponent p (fixSubgroup β) J) (hJT : JType p q J) : False := by
  obtain ⟨K, hfieldK, hfinK, hK, ⟨e⟩⟩ := hG.2
  letI := hfieldK
  letI := hfinK
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 q f hG K hK e
  have hEA : 3 < p ∨ projectivePointFamilyAut (coordinateQuadPlus 4 K) = ⊤ := by
    left
    have h2 := hp.two_le
    omega
  let e' := coordinatePlusWitnessEquiv K e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := Finite.of_equiv _ e'.toEquiv
  let β' : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := MulAut.congr e' β
  have hβ' : β' ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE : β' ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) :=
    mem_E_of_pow_eq_one_omega hgates hp hEA hβ'
  exact orthOuter_plus_of_mem_image p q hp hp2 hq hq2 hqp G f hG K hK e β hβ hnot hE hJ hJT

private theorem orthOuter_minus (p q : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (G : Type) [Group G] [Finite G] (f : ℕ)
    (hG : StatedClassicalModel G .POmegaMinus 4 q f)
    (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a)
    {J : Subgroup G} (hJ : GLAPComponent p (fixSubgroup β) J) (hJT : JType p q J) : False := by
  obtain ⟨-, hf, -⟩ := hG.1
  obtain ⟨K, hfieldK, hfinK, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  letI := hfieldK
  letI := hfinK
  have hn1 : 1 ≤ 4 := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) 4 q f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus 4 K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus
      (.inr rfl) 4 q f hG) hn1 K hK b c hirr).2
  let e' := coordinateMinusWitnessEquiv K hn1 b c e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b c)) :=
    Finite.of_equiv _ e'.toEquiv
  let β' : MulAut (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b c)) :=
    MulAut.congr e' β
  have hβ' : β' ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE : β' ∈ matrixProjectiveImage (coordinateQuadMinus 4 K hn1 b c) :=
    mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) hβ'
  have hD : β' ∉ (linearConjugationHom (coordinateQuadMinus 4 K hn1 b c)).range := by
    intro hmem
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hgates hp hp2 hmem hβ'
    apply hnot (e'.symm t)
    have hcongr : MulAut.congr e' (MulAut.conj (e'.symm t)) = MulAut.congr e' β := by
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
    exact ((MulAut.congr e').injective hcongr).symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf β' = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  let J' : Subgroup (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b c)) :=
    J.map e'.toMonoidHom
  have hJ' : GLAPComponent p (fixSubgroup β') J' := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp e' hJ
    have hfix : fixSubgroup β' = (fixSubgroup β).map e'.toMonoidHom :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e' β
    rw [hfix]
    exact h1
  have hJT' : JType p q J' := (jType_map_mulEquiv hp e').1 hJT
  obtain ⟨hpf, hrest⟩ := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) 4 q f p hG hp hp2 hn1 K hK b c hirr e β' hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hord1, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ :=
    hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, hS₀, hmodel, hT'⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = q ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hKbig : Nat.card K = q ^ (f / p * p) := by
    rw [Nat.div_mul_cancel hpf]; exact hK
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  have hadm : StatedLieAdmissible .POmegaMinus 4 q (f / p) := ⟨hq, hfp, by omega⟩
  obtain ⟨-, hconc⟩ := (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd
    .POmegaMinus (Or.inr (Or.inr rfl)) 4 q (f / p) p) hadm hp hp2 (Ne.symm hqp)
    hn1 K (semilinearFixedSubfield U.val.right) hcard' hKbig U.val.right hord' hσk b' c' hirr'
  have hg' : g' = fieldPair (coordinateQuadMinus 4 K hn1 (b' : K) (c' : K)) U.val.right
      (coordinateQuadMinus_fieldAut (semilinearFixedSubfield U.val.right) 4 hn1 hσk b' c') :=
    Subtype.ext (SemidirectProduct.ext hg'l hg'r)
  have hcongr : MulAut.congr Θ β' =
      fieldAutT (coordinateQuadMinus 4 K hn1 (b' : K) (c' : K)) U.val.right
        (coordinateQuadMinus_fieldAut (semilinearFixedSubfield U.val.right) 4 hn1 hσk b' c') := by
    rw [← hUκ]
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ
        (matrixProjectiveConjugationHom (coordinateQuadMinus 4 K hn1 b c) U)) x =
        Θ (matrixProjectiveConjugationHom (coordinateQuadMinus 4 K hn1 b c) U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  have hmodelSmall : StatedClassicalModel
      (matrixProjectiveDerived
        (coordinateQuadMinus 4 (semilinearFixedSubfield U.val.right) hn1 b' c'))
      .POmegaMinus 4 q (f / p) :=
    ⟨hadm, semilinearFixedSubfield U.val.right, inferInstance, inferInstance, hcard',
      b', c', hirr',
      ⟨(coordinateMinusWitnessEquiv (n := 4) (semilinearFixedSubfield U.val.right) hn1 b' c'
        (MulEquiv.refl _)).symm⟩⟩
  exact false_of_fieldModel hp hq hq2 (by omega)
    (coordinateQuadMinus_isExtension (semilinearFixedSubfield U.val.right) 4 hn1 b' c')
    (coordinateQuadMinus_fieldAut (semilinearFixedSubfield U.val.right) 4 hn1 hσk b' c')
    hconc (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hmodelSmall Θ β' hcongr hJ' hJT'

theorem i2020OrthOuter : I2020OrthOuter := by
  intro p q hp hp2 hq hq2 hqp t n ht G _ _ f hG hD4 β hβ hnot
  rcases ht with ⟨rfl, rfl⟩ | ⟨(rfl | rfl), rfl⟩
  · intro J hJ hJT
    exact (orthOuter_odd p q hp hp2 hq hq2 hqp G f hG β hβ hnot hJ hJT).elim
  · intro J hJ hJT
    exact (orthOuter_plus p q hp hp2 hq hq2 hqp G f hG (hD4 rfl) β hβ hnot hJ hJT).elim
  · intro J hJ hJT
    exact (orthOuter_minus p q hp hp2 hq hq2 hqp G f hG β hβ hnot hJ hJT).elim

end CFSG.LocalAnalysis.GLTheoremA.I2020

end

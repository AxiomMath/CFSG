module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthTail
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsOrthKind
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem fieldKind_omegaPlus_data {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .D) (hr3 : labK.rank ≠ 3)
    (hfld : FieldKind S labK α) :
    4 ≤ labK.rank ∧ 1 ≤ labK.n ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ labK.n ∧
      IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank))) ∧
      (∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank)), a * b ≠ b * a) ∧
      ∃ (e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank)))
        (i f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank)))),
        i ∈ LargeEvenInnSet _ ∧
        f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K labK.rank))) ∧
        MulAut.congr e α = i * f ∧ i * f ∉ LargeEvenInnSet _ := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam, hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  have hm3 : 3 ≤ labK.rank := by
    have h := hlam
    simp only [LargeEvenInLambda2, ht] at h
    exact h.2
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  simp only [ht, hr3, ↓reduceIte] at hraw
  unfold LargeEvenRecipeOmegaPlus at hraw
  obtain ⟨K, hKf, hKfin, hcard, hs, hna, θ, -, ⟨i, hi, f, hf, hind⟩, hnot⟩ := hraw
  let e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K labK.rank)) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
  refine ⟨by omega, hlam.1, K, hKf, hKfin, hcard, hs, hna, e, i, f, hi, hf, ?_,
    fun h => hnot ⟨i * f, h, hind⟩⟩
  refine MulEquiv.ext fun r => ?_
  obtain ⟨s, rfl⟩ := e.surjective r
  rw [CFSG.RankThree.PartOne.AUTSL.congr_apply_apply']
  exact (hind s (α s) rfl).symm

namespace FOC

open CFSG.StandardType CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem congr_trans {A B C : Type*} [Group A] [Group B] [Group C] (e₁ : A ≃* B) (e₂ : B ≃* C)
    (β : MulAut A) : MulAut.congr (e₁.trans e₂) β = MulAut.congr e₂ (MulAut.congr e₁ β) :=
  MulEquiv.ext fun _ => rfl

theorem congr_symm_eq {R : Type*} [Group R] (u β : MulAut R) :
    MulAut.congr (MulEquiv.symm u) β = u⁻¹ * β * u :=
  MulEquiv.ext fun _ => rfl

theorem congr_derivedProjEquiv_conjAct {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q) :
    MulAut.congr (AUTSL.derivedProjEquiv Q hQ) (AUTSL.conjAct Q g) =
      matrixProjectiveConjugationHom Q g := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨A, rfl⟩ := (AUTSL.derivedProjEquiv Q hQ).surjective x
  rw [AUTSL.congr_apply_apply']
  exact (matrixProjectiveConjugation_mk Q g A).symm

theorem exists_congr_field_eq_fieldAutT {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {f' : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf' : f' ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) :
    ∃ σ : K ≃+* K, MulAut.congr ((RecipeFieldOmega.plusEquiv hm).trans
        (AUTSL.derivedProjEquiv (coordinateQuadPlus m K)
          ⟨_, AutOm.plusUnitVector_form_ne_zero hm⟩)) f' =
      fieldAutT (coordinateQuadPlus m K) σ (coordinateQuadPlus_fieldAut m σ) := by
  obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm hf'
  refine ⟨σ, ?_⟩
  rw [congr_trans, hσ, AutOm.fieldAutP_apply, congr_derivedProjEquiv_conjAct]
  rfl

theorem exists_congr_eq_fieldAutT {m p : ℕ} (hm3 : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] {S : Type} [Group S] {α : MulAut S}
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a)
    (e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
    {i f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hi : i ∈ LargeEvenInnSet _)
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hcongr : MulAut.congr e α = i * f) (hout : i * f ∉ LargeEvenInnSet _) (hα : α ^ p = 1) :
    ∃ (σ : K ≃+* K) (ψ : S ≃* matrixProjectiveDerived (coordinateQuadPlus m K)),
      orderOf σ = p ∧ MulAut.congr ψ α =
        fieldAutT (coordinateQuadPlus m K) σ (coordinateQuadPlus_fieldAut m σ) := by
  have hm : 1 ≤ m := by omega
  have hpow : (i * f) ^ p = 1 := by rw [← hcongr, ← map_pow, hα, map_one]
  obtain ⟨f', hf', u, ⟨r, rfl⟩, hord, heq⟩ :=
    RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := K) hm3 hp hp2 hs hna i hi f
      (Subgroup.subset_closure hf) hout hpow
  obtain ⟨σ, hfT⟩ := exists_congr_field_eq_fieldAutT hm hf'
  have h1 : MulAut.congr (e.trans (MulEquiv.symm (MulAut.conj r))) α = f' := by
    rw [congr_trans, hcongr, heq, congr_symm_eq]
    group
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus m K hm3
  refine ⟨σ, (e.trans (MulEquiv.symm (MulAut.conj r))).trans ((RecipeFieldOmega.plusEquiv hm).trans
    (AUTSL.derivedProjEquiv (coordinateQuadPlus m K) ⟨_, AutOm.plusUnitVector_form_ne_zero hm⟩)),
    ?_, ?_⟩
  · rw [← orderOf_fieldAutT _ σ (coordinateQuadPlus_fieldAut m σ) hnd hT
      (coordinate_plus_point_action_properties m K hm3), ← hfT, MulEquiv.orderOf_eq, hord]
  · rw [congr_trans, h1, hfT]

theorem statedClassicalModel_coordinatePlus {m a : ℕ} (hm4 : 4 ≤ m) (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ a) :
    StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus m K)) .POmegaPlus m 2 a :=
  ⟨⟨Nat.prime_two, ha, hm4⟩, K, inferInstance, inferInstance, hK,
    ⟨(statedProjectiveReindexEquiv (plusIndexEquiv m) (quadPlus m K) (coe_quadPlus m K)).symm⟩⟩

theorem exists_subfieldSetup_plus {m n p : ℕ} (hm3 : 3 ≤ m) (hn1 : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) {σ : K ≃+* K}
    (hσ : orderOf σ = p) :
    p ∣ n ∧ ∃ k : Subfield K, Nat.card k = 2 ^ (n / p) ∧
      SubfieldSetup k (coordinateQuadPlus m k) (coordinateQuadPlus m K) σ p := by
  obtain ⟨hpn, hk⟩ := card_semilinearFixedSubfield Nat.prime_two hn1 hK hσ
  exact ⟨hpn, semilinearFixedSubfield σ, hk,
    subfieldSetup_plus _ (fun _ => RingHom.mem_eqLocusField) hp hp2 hσ hm3⟩

end FOC

theorem omegaPlus_field_pComponent {m n p : ℕ} (hm4 : 4 ≤ m) (hn1 : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n) {S : Type} [Group S]
    [Finite S] {α : MulAut S}
    (hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a)
    (e : S ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
    {i f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hi : i ∈ LargeEvenInnSet _)
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))))
    (hcongr : MulAut.congr e α = i * f) (hout : i * f ∉ LargeEvenInnSet _) (hα : α ^ p = 1)
    {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup α) J) :
    p ∣ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaPlus m 2 (n / p) := by
  have hm3 : 3 ≤ m := by omega
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  obtain ⟨σ, ψ, hσ, hψ⟩ := FOC.exists_congr_eq_fieldAutT hm3 hp hp2 hs hna e hi hf hcongr hout hα
  obtain ⟨hpn, k, hk, SS⟩ := FOC.exists_subfieldSetup_plus hm3 hn1 hp hp2 hK hσ
  obtain ⟨eJ⟩ := pComponent_quotCenter_equiv SS ψ hψ hJ
  exact ⟨hpn, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm
    (FOC.statedClassicalModel_coordinatePlus hm4 (Nat.div_pos (Nat.le_of_dvd hn1 hpn) hp.pos) hk)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

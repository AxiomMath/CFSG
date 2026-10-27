module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthTail
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthOrth
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

namespace FOD

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.Classical.SteinbergBY CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_minus)

theorem orthFieldDatum_minus {S : Type} [Group S] {n ℓ f p : ℕ} (hn1 : 1 ≤ n)
    (hS : StatedClassicalModel S .POmegaMinus n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    p ∣ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (b c : k)
      (_ : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (σ : K ≃+* K)
      (SS : SubfieldSetup k (coordinateQuadMinus n k hn1 b c)
        (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ p)
      (φ : S ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))),
      Nat.card k = ℓ ^ (f / p) ∧ MulAut.congr φ β = fieldAutT _ σ SS.hQσ := by
  obtain ⟨hℓ, hf, hn4⟩ := hS.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hS.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hS hn1 K hK b c hirr e
  obtain ⟨hD, hord⟩ := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth.outer_order_prime
    (coordinateMinusWitnessEquiv K hn1 b c e) hgates hp hp2 hβ (fun ⟨a, ha⟩ => hout a ha)
  have hE : MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β ∈
      matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [matrixProjectiveImage_eq_top_minus K n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' S .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hS hp hp2 hn1 K hK b c hirr e _ hE hD hord
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
  obtain ⟨m, hm⟩ := id hpf
  have hdiv : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = ℓ ^ (m * p) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hℓ hm1
    (hdiv ▸ hcard') hK'
  have SS := subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord'' hn4 hdeg
    b' c' hirr'
  refine ⟨hpf, K, inferInstance, inferInstance, _, b', c', hirr', U.val.right, SS,
    (coordinateMinusWitnessEquiv K hn1 b c e).trans Θ, hcard', ?_⟩
  rw [← CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.matrixProjectiveConjugationHom_eq_fieldAutT
    SS g' hg'l hg'r]
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr ((coordinateMinusWitnessEquiv K hn1 b c e).trans Θ) β) x =
      Θ ((MulAut.congr (coordinateMinusWitnessEquiv K hn1 b c e) β) (Θ.symm x)) := rfl
  rw [h1, ← hUκ, hΘ, MulEquiv.apply_symm_apply]

end FOD

theorem fieldKind_omegaMinus_model {S : Type} [Group S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (ht : labK.tag = .twD) (hr2 : labK.rank ≠ 2)
    (hr3 : labK.rank ≠ 3) (hfld : FieldKind S labK α) :
    4 ≤ labK.rank ∧ StatedClassicalModel S .POmegaMinus labK.rank 2 labK.n ∧
      ∀ a : S, MulAut.conj a ≠ α := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam, hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  have hΛ : 1 ≤ labK.n ∧ 2 ≤ labK.rank := by
    have h := hlam
    simp only [LargeEvenInLambda2, ht] at h
    exact h
  have hm4 : 4 ≤ labK.rank := by omega
  unfold LargeEvenRawDatum at hraw
  simp only [ht, hr2, hr3, ↓reduceIte] at hraw
  unfold LargeEvenRecipeOmegaMinus at hraw
  obtain ⟨K, _, _, hcard, b, c, hirr, -, -, θ, -, -, hnot⟩ := hraw
  refine ⟨hm4, ?_, ?_⟩
  · exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans
        θ).symm
      (CFSG.StandardType.statedClassicalModel_omegaMinus labK.rank labK.n hcard b c hirr
        ⟨Nat.prime_two, hΛ.1, hm4⟩)
  · intro a ha
    refine hnot ⟨MulAut.conj (θ (QuotientGroup.mk a)), ⟨_, rfl⟩, fun l l' hll' => ?_⟩
    rw [hll', ← ha, MulAut.conj_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

theorem omegaMinus_outer_pComponent {S : Type} [Group S] [Finite S] {m n p : ℕ}
    (hS : StatedClassicalModel S .POmegaMinus m 2 n) (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut S}
    (hα : α ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ α) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup α) J) :
    p ∣ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaMinus m 2 (n / p) := by
  obtain ⟨-, hn1, hm4⟩ := hS.1
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hpn, K, _, _, k, b, c, hirr, σ, SS, φ, hk, hφ⟩ :=
    FOD.orthFieldDatum_minus hm1 hS hp hp2 hα hout
  obtain ⟨eJ⟩ := pComponent_quotCenter_equiv SS φ hφ hJ
  have hfp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn1 hpn) hp.pos
  have hmodelk : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus m k hm1 b c))
      .POmegaMinus m 2 (n / p) :=
    ⟨⟨Nat.prime_two, hfp, hm4⟩, k, inferInstance, inferInstance, hk, b, c, hirr,
      ⟨(statedProjectiveReindexEquiv (minusIndexEquiv m hm1) (quadMinus m k b c)
        (coe_quadMinus m k b c)).symm⟩⟩
  exact ⟨hpn, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hmodelk⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

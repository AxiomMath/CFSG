module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
  CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
  CFSG.HardMathSupport.Lang
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)


section Helper

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q' : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem fixSub_conjHom_eq [CharP K 2] (S : SubfieldSetup k Q₀ Q' σ p) (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ) :
    FP.fixSub (matrixProjectiveConjugationHom Q' g') = subfieldDerivedImage k S.hext := by
  rw [matrixProjectiveConjugationHom_eq_fieldAutT S g' hl hr]
  have h1 : fixedSubgroup (fieldAutT Q' σ S.hQσ) = subfieldFixedGroup k Q₀ Q' := by
    ext t
    exact fieldAutT_apply_iff S t
  refine h1.trans ?_
  exact le_antisymm (CFSG.RankThree.PartOne.FieldFix.subfieldFixedGroup_le_derivedImage
    S.hext S.hnd₀ S.hT₀ S.hnd) (subfieldDerivedImage_le k S.hext)

end Helper

theorem omegaMinus_fixed_equiv {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hcl : StatedClassicalModel G .POmegaMinus n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut G) (hαp : α ^ p = 1) (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    ∃ (f₀ : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (b' c' : k),
      (∀ s : k, s ^ 2 + b' * s + c' ≠ 0) ∧ f = p * f₀ ∧ Nat.card k = 2 ^ f₀ ∧
      Nonempty (↥(FP.fixSub α) ≃* StatedProj (StatedOmega (StatedQuadMinus n k b' c'))) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = 2 ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
  have e2 := fixSubEquiv Θ β _ hΘ'
  have e3 := fixSub_conjHom_eq hsetup g' hg'l hg'r
  have e4 : ↥(subfieldDerivedImage (semilinearFixedSubfield U.val.right) hsetup.hext) ≃*
      matrixProjectiveDerived (coordinateQuadMinus n (semilinearFixedSubfield U.val.right)
        (by omega) b' c') :=
    (MonoidHom.ofInjective (incl_injective _ hsetup.hext (by omega))).symm
  have e5 := coordinateMinusWitnessEquiv (semilinearFixedSubfield U.val.right) (by omega) b' c'
    (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadMinus n
      (semilinearFixedSubfield U.val.right) b' c'))))
  refine ⟨f / p, ↥(semilinearFixedSubfield U.val.right), inferInstance, inferInstance, b', c', hirr',
    (Nat.mul_div_cancel' hpf).symm, hcard', ⟨?_⟩⟩
  exact ((fixSubEquivCongr θ α).trans (e2.trans ((MulEquiv.subgroupCongr e3).trans e4))).trans
    e5.symm



theorem subBody_omegaMinus {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))))
    (hF : FQ.InnFree p F) :
    ∀ f ∈ F, orderOf f = p → p ∣ n ∧
      ∃ D : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))),
        SubfieldGrp f D ∧ LargeEvenRecipeOmegaMinus (l - 1) (2 ^ (n / p))
          (fun R' _ _ _ => Nonempty (↥D ≃* R')) := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  intro f hf hord
  have hcl := CFSG.StandardType.statedClassicalModel_omegaMinus l n hK b c hirr ⟨Nat.prime_two, hn, hl⟩
  haveI : Finite (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hαp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  obtain ⟨f₀, k, hkF, hkfin, b', c', hirr', hf0, hkcard, ⟨e⟩⟩ :=
    omegaMinus_fixed_equiv hcl hp hp2 f hαp (fun h => hF f hf hord h)
  have hdiv : n / p = f₀ := by rw [hf0, Nat.mul_div_cancel_left _ hp.pos]
  refine ⟨⟨f₀, by rw [hf0, mul_comm]⟩, FP.fixSub f, ⟨le_rfl, Subgroup.commutator_le_of_le le_rfl le_rfl,
    ?_⟩, k, hkF, hkfin, by rw [hdiv]; exact hkcard, b', c', hirr', ?_⟩
  · rw [Subgroup.relIndex_self]; exact odd_one
  · exact ⟨e.trans (CFSG.StandardType.omegaMinusProjEquiv l b' c').symm⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA

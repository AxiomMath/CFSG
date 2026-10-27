module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.FROmegaMinus
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthContract
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldOrthogonal
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Assembly CFSG.StandardType
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.ComponentClassification
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

section Pure

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem omega_nlWitness_of_fieldAutT {G : Type} [Group G] (k : Subfield K)
    {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} (σ : K ≃+* K)
    (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hext : IsExtension k Q₀ Q)
    (hσk : ∀ x, x ∈ k ↔ σ x = x) (hnd₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hd : 5 ≤ d) (hdq : d ≤ Nat.card k ^ (d - 4)) (e : G ≃* matrixProjectiveDerived Q)
    {α : MulAut G} (hα : MulAut.congr e α = fieldAutT Q σ hQσ) : NLWitness α := by
  have hd0 : 0 < d := by omega
  obtain ⟨hs, hna⟩ := matrix_simple_nonabelian hd0 hnd₀ hT₀
  have hsJ : IsSimpleGroup ↥(subfieldDerivedImage k hext) := by
    haveI := hs
    exact (inclEquiv k hext hd0).symm.isSimpleGroup
  have hnaJ : ∃ x y : ↥(subfieldDerivedImage k hext), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hna
    refine ⟨inclEquiv k hext hd0 a, inclEquiv k hext hd0 b, fun h => hab
      ((inclEquiv k hext hd0).injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hNL := CFSG.SignalizerFunctorTheorem.NonLocal.Orth.nonLocalized_orthogonalSubfield k hext
    hnd₀ hnd hT₀ hd hdq
  refine nlWitness_of_nonLocalized e hsJ hnaJ hNL ?_
  rintro _ ⟨t, ht, rfl⟩
  have h1 := fieldAutT_fixes_J k Q σ hQσ hext hσk ht
  show α (e.symm t) = e.symm t
  apply e.injective
  have h2 : e (α (e.symm t)) = (MulAut.congr e α) t := rfl
  rw [h2, hα, h1, MulEquiv.apply_symm_apply]

end Pure

section Outer

theorem omegaMinus_nlWitness_outer {G : Type} [Group G] {n f : ℕ}
    (hcl : StatedClassicalModel G .POmegaMinus n 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut G) (hαp : α ^ p = 1) (hαin : α ∉ OuterAutomorphisms.inner G) : NLWitness α := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n 2 f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e
  set Q := coordinateQuadMinus n F hn1 b c
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((OuterAutomorphisms.congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨-, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      G .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, _, hT⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = 2 ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  refine omega_nlWitness_of_fieldAutT (semilinearFixedSubfield U.val.right) U.val.right hsetup.hQσ
    hsetup.hext hsetup.hσk hsetup.hnd₀ hsetup.hnd hsetup.hT₀ (by omega)
    (CFSG.SignalizerFunctorTheorem.NonLocal.le_pow_sub_four _ Finite.one_lt_card (2 * n) (by omega))
    (θ.trans Θ) ?_
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.congr_eq_fieldAutT θ Θ α U hUκ g' hg'l hg'r hΘ
    hsetup.hQσ

end Outer

theorem omegaMinus_nlWitness_phi {l n : ℕ} (hl : 4 ≤ l) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))
    (hna : ∃ x y : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)), x * y ≠ y * x)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))}
    (hf : f ∈ LargeEvenPhiQ (l - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))))
    (hord : orderOf f = p) : NLWitness f := by
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hcl := statedClassicalModel_omegaMinus l n hK b c hirr ⟨Nat.prime_two, hn, hl⟩
  have hαp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hαin : f ∉ OuterAutomorphisms.inner
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))) := by
    intro h
    have hnot := (RecipeFieldOmega.ggRawInnField_omegaMinus hl hirr hK hn hp.one_lt.ne' hS
      hna).2.2.2 f hf hord
    rw [← RecipeFieldOmega.coe_inner_eq_innSet] at hnot
    exact hnot h
  exact omegaMinus_nlWitness_outer hcl hp hp2 f hαp hαin

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnOmegaMinus_holds : I2015NLOnOmegaMinus := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp hp2 _ _ hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only [regRankGe] at hC ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  have hr2 : r ≠ 2 := by omega
  have hr3 : r ≠ 3 := by omega
  simp only [CFSG.Assembly.LargeEvenRawDatum, hr2, hr3, if_false] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, b, c, hirr, hQ', fun hs hna _ f hf hord _ _ => ?_⟩
  exact omegaMinus_nlWitness_phi hC hn hK hirr hp hp2 hs hna hf hord

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end

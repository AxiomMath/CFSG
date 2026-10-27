module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLBPOmegaOrder
public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedOmega StatedQuadMinus)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem card_fixed_POmegaMinus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .POmegaMinus n (ℓ ^ f₀) ∣
        lieOrderDivisor .POmegaMinus n (ℓ ^ f₀) * Nat.card (fixedSubgroup α) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, b, c, hirr, ⟨e⟩⟩ := hcl
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hchar, -⟩ := coordinate_model_witness_minus hcl' F hF b c hirr e
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f hcl' hn1 F hF b c hirr e
  set θ := coordinateMinusWitnessEquiv F hn1 b c e with hθ
  set Q := coordinateQuadMinus n F hn1 b c with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K
      .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨b', c', hirr', ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = ℓ ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_minus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn4 hdeg b' c' hirr'
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom _ g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l hg'r hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix]
  have : Finite (semilinearFixedSubfield U.val.right) := Subtype.finite
  have hmodel : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n
      (semilinearFixedSubfield U.val.right) b' c'))) .POmegaMinus n ℓ (f / p) :=
    ⟨⟨hℓ, hfp, hn4⟩, semilinearFixedSubfield U.val.right, inferInstance, inferInstance, hcard',
      b', c', hirr', ⟨MulEquiv.refl _⟩⟩
  have hmul := card_mul_lieOrderDivisor_of_orthogonalModel (Or.inr (Or.inr rfl))
    ⟨hℓ, hfp, hn4⟩ hmodel
  have hP : Nat.card (matrixProjectiveDerived (coordinateQuadMinus n
      (semilinearFixedSubfield U.val.right) (by omega) b' c')) =
      Nat.card (StatedProj (StatedOmega (StatedQuadMinus n
        (semilinearFixedSubfield U.val.right) b' c'))) :=
    (Nat.card_congr (coordinateMinusWitnessEquiv (semilinearFixedSubfield U.val.right)
      (by omega) b' c' (MulEquiv.refl _)).toEquiv).symm
  have hdvd := card_matrixProjectiveDerived_dvd_subfieldFixedGroup
    (semilinearFixedSubfield U.val.right) hsetup.hext (show 0 < 2 * n by omega)
  rw [hP] at hdvd
  exact (dvd_of_eq hmul.symm).trans ((Nat.mul_dvd_mul_right hdvd _).trans
    (dvd_of_eq (mul_comm _ _)))

theorem fixedLowerBoundAt_POmegaMinus : FixedLowerBoundAt .POmegaMinus := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .POmegaMinus n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hpos : 0 < p := hp.pos
  obtain ⟨f₁, hf₁, hdvd⟩ := card_fixed_POmegaMinus hcl hp hp2 α hαp hαin
  have : f₁ = f₀ := by
    have := hf.symm.trans hf₁
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  subst this
  exact hdvd

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

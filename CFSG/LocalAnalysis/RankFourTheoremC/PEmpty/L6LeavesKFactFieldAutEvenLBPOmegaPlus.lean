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
  StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem card_fixed_POmegaPlus {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .POmegaPlus n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD4 : ¬ (n = 4 ∧ p = 3)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .POmegaPlus n (ℓ ^ f₀) ∣
        lieOrderDivisor .POmegaPlus n (ℓ ^ f₀) * Nat.card (fixedSubgroup α) := by
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn4⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hcl' F hF e
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f hcl' F hF e
  set θ := coordinatePlusWitnessEquiv F e with hθ
  set Q := coordinateQuadPlus n F with hQ
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
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hp3 : 3 < p := by
        have h3 : p ≠ 3 := fun h3 => hD4 ⟨h4, h3⟩
        have := hp.two_le
        omega
      have hA : Subgroup.zpowers β ≤ familyOrbitKernel Q :=
        hgates.2.2.2.2.2.2.1 p hp hp3 _ (IsPGroup.of_card (n := 1)
          (by rw [Nat.card_zpowers, hβord, pow_one]))
      have h1 := hgates.2.2.2.2.1 (hA (Subgroup.mem_zpowers β))
      rw [hgates.2.2.2.2.2.1] at h1
      exact h1
    · rw [matrixProjectiveImage_eq_top_plus F n h5]
      exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K
      .POmegaPlus (Or.inr (Or.inl rfl)) n ℓ f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l hg'r hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix]
  have : Finite (semilinearFixedSubfield U.val.right) := Subtype.finite
  have hmodel : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n
      (semilinearFixedSubfield U.val.right)))) .POmegaPlus n ℓ (f / p) :=
    ⟨⟨hℓ, hfp, hn4⟩, semilinearFixedSubfield U.val.right, inferInstance, inferInstance, hcard',
      ⟨MulEquiv.refl _⟩⟩
  have hmul := card_mul_lieOrderDivisor_of_orthogonalModel (Or.inr (Or.inl rfl))
    ⟨hℓ, hfp, hn4⟩ hmodel
  have hP : Nat.card (matrixProjectiveDerived (coordinateQuadPlus n
      (semilinearFixedSubfield U.val.right))) =
      Nat.card (StatedProj (StatedOmega (StatedQuadPlus n
        (semilinearFixedSubfield U.val.right)))) :=
    (Nat.card_congr (coordinatePlusWitnessEquiv (semilinearFixedSubfield U.val.right)
      (MulEquiv.refl _)).toEquiv).symm
  have hdvd := card_matrixProjectiveDerived_dvd_subfieldFixedGroup
    (semilinearFixedSubfield U.val.right) hsetup.hext (show 0 < 2 * n by omega)
  rw [hP] at hdvd
  exact (dvd_of_eq hmul.symm).trans ((Nat.mul_dvd_mul_right hdvd _).trans
    (dvd_of_eq (mul_comm _ _)))

theorem fixedLowerBoundAt_POmegaPlus : FixedLowerBoundAt .POmegaPlus := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .POmegaPlus n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hD4 : ¬ (n = 4 ∧ p = 3) := fun h => by omega
  have hpos : 0 < p := hp.pos
  obtain ⟨f₁, hf₁, hdvd⟩ := card_fixed_POmegaPlus hcl hp hp2 hD4 α hαp hαin
  have : f₁ = f₀ := by
    have := hf.symm.trans hf₁
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  subst this
  exact hdvd

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

module

public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOddChar
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneModel
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.KC.OrthogonalNoninnerPlaneWiring

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonalDescent
  CFSG.RankThree.PartOne.KCOrthogonalNoninner CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Lang.Coordinator
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem outerFixedOrderBoundAt_POmegaOdd : OuterFixedOrderBoundAt .POmegaOdd := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv hD4 α hαp hαin
  left
  have hcl : StatedClassicalModel K .POmegaOdd n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hcl' := hcl
  obtain ⟨⟨hℓ, hf, hn3, hℓ2⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
  obtain ⟨hchar, -⟩ := coordinate_model_witness_odd hcl' F hF e
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have : ringChar F = 2 := (ringChar.eq_iff.mpr (CharTwo.of_one_ne_zero_of_two_eq_zero
      one_ne_zero h))
    omega
  have : Fact p.Prime := ⟨hp⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaOdd
    (Or.inl rfl) n ℓ f hcl' F hF e
  set θ := coordinateOddWitnessEquiv F e with hθ
  set Q := coordinateQuadOdd n F with hQ
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .POmegaOdd n (ℓ ^ f₀)
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_odd F n hn3 (by omega)]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K .POmegaOdd
    (Or.inl rfl) n ℓ f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hdeg : Module.finrank (semilinearFixedSubfield U.val.right) F = p := by
    have hK' : Nat.card F = ℓ ^ ((f / p) * p) := by rw [Nat.div_mul_cancel hpf]; exact hF
    exact finrank_subfield_eq _ hℓ hfp hcard' hK'
  have hsetup := subfieldSetup_odd (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' hn3 h2F
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l (hg'r.trans rfl) hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix, ← hcard']
  have h2k : (2 : semilinearFixedSubfield U.val.right) ≠ 0 := two_ne_zero_of_subfield _ h2F
  exact card_subfieldFixedGroup_odd_dvd _ n (by omega) h2k _

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

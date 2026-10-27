module

public import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOddChar
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaChar2
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

private theorem two_eq_zero_imp_char_two {F : Type} [Field F] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hchar : ringChar F = ℓ) (h : (2 : F) = 0) : CharP F 2 := by
  have hcp : CharP F ℓ := hchar ▸ ringChar.charP F
  have h1 : ℓ ∣ 2 := (CharP.cast_eq_zero_iff F ℓ 2).mp (by exact_mod_cast h)
  have hℓ2' : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1
  exact hℓ2' ▸ hcp

theorem outerFixedOrderBoundAt_POmegaPlus : OuterFixedOrderBoundAt .POmegaPlus := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv hD4 α hαp hαin
  left
  have hcl : StatedClassicalModel K .POmegaPlus n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
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
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .POmegaPlus n (ℓ ^ f₀)
  have hE : β ∈ matrixProjectiveImage Q := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · have hp3 : 3 < p := by
        have h3 : p ≠ 3 := fun h3 => hD4 ⟨rfl, h4, h3⟩
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
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hcl' hp hp2 F hF e β hE hD hβord
  obtain ⟨g, hg⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, hCM, hT⟩ := hDisp
  obtain ⟨S, ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = ℓ ^ (f / p) := by
    rw [hUr]; exact hcard
  have hsetup := subfieldSetup_plus (semilinearFixedSubfield U.val.right)
    (σ := U.val.right) (fun x => Iff.rfl) hp hp2 hord' (n := n) (by omega)
  have hΘ' : ∀ x, Θ (β x) = matrixProjectiveConjugationHom Q g' (Θ x) := fun x => by
    rw [← hUκ]; exact hΘ x
  have hfix := card_fixedSubgroup_eq_subfieldFixedGroup hsetup Θ g' hg'l hg'r hΘ'
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hfix, ← hcard']
  by_cases h2F : (2 : F) = 0
  · haveI : CharP F 2 := two_eq_zero_imp_char_two hℓ hchar h2F
    exact (card_subfieldFixedGroup_dvd_model _ n hsetup.hext hsetup.hnd₀ hsetup.hT₀
      hsetup.hnd).trans (dvd_of_eq (card_model_plus_eq _ n hn4))
  · have h2k : (2 : semilinearFixedSubfield U.val.right) ≠ 0 := two_ne_zero_of_subfield _ h2F
    exact card_subfieldFixedGroup_plus_dvd _ n (by omega) h2k _

theorem outerFixedOrderBoundAt_POmegaMinus : OuterFixedOrderBoundAt .POmegaMinus := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv hD4 α hαp hαin
  left
  have hcl : StatedClassicalModel K .POmegaMinus n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
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
  have hβout : β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  rw [← card_fixedSubgroup_congr θ α]
  change ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup β) ∣ lieOrderNumerator .POmegaMinus n (ℓ ^ f₀)
  have hE : β ∈ matrixProjectiveImage Q := by
    rw [matrixProjectiveImage_eq_top_minus F n hn4 b c hirr]
    exact Subgroup.mem_top _
  have hD : β ∉ (linearConjugationHom Q).range := by
    intro hD
    obtain ⟨hHD, k, hk⟩ := hgates.2.2.1
    exact hβout (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp hp2 hD hβp)
  have hdesc := Proving.orthogonal_prime_semilinear_actual_fixed_form_descent' K .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ f p hcl' hp hp2 hn1 F hF b c hirr e β hE hD hβord
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
  rw [hfix, ← hcard']
  by_cases h2F : (2 : F) = 0
  · haveI : CharP F 2 := two_eq_zero_imp_char_two hℓ hchar h2F
    exact (card_subfieldFixedGroup_dvd_model _ n hsetup.hext hsetup.hnd₀ hsetup.hT₀
      hsetup.hnd).trans (dvd_of_eq (card_model_minus_eq _ n hn4 hirr'))
  · have h2k : (2 : semilinearFixedSubfield U.val.right) ≠ 0 := two_ne_zero_of_subfield _ h2F
    exact card_subfieldFixedGroup_minus_dvd _ n (by omega) h2k hirr' _

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadPlus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')

theorem exists_descent_om_plus_of_mem {n ℓ f : ℕ} (hn4 : 4 ≤ n) {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hℓ3 : (3 : ℕ) ≠ ℓ) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα : IsOuterOfOrder 3 α)
    (hE : α ∈ matrixProjectiveImage (coordinateQuadPlus n K)) :
    ∃ (k : Subfield K) (ι : matrixProjectiveDerived (coordinateQuadPlus n k) →*
        matrixProjectiveDerived (coordinateQuadPlus n K)),
      Nat.card k = ℓ ^ (f / 3) ∧ Function.Injective ι ∧ (∀ v, α (ι v) = ι v) ∧
        (∀ x, α x = x → x ∈ ι.range) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus n ℓ f := ⟨hℓ, hf, hn4⟩
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ
      f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  have hD : α ∉ (linearConjugationHom (coordinateQuadPlus n K)).range := by
    intro hD
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ 3 = 1 := hord ▸ pow_orderOf_eq_one α
    obtain ⟨-, k, hk⟩ := hg.2.2.1
    have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixProjectiveDerived (coordinateQuadPlus n K))).Normal :=
      CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
    obtain ⟨g, hgα⟩ :=
      CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp
        hp2 hD hαp
    exact hout g hgα.symm
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f 3 hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, hDlin, σ, hσ, hαeq⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ _ => coordinateQuadPlus_fieldAut n σ)
    (fun U Q₀ _ hdisp => by
      obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      exact ⟨S, ν', hSQ, hSA⟩)
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
  have hcardk0 := hcardk
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
  have hK' : Nat.card K = ℓ ^ (e * 3) := by rw [hK, mul_comm]
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hadm0 : StatedLieAdmissible .POmegaPlus n ℓ e := ⟨hℓ, he, hn4⟩
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ e 3 hadm0 hp hp2 hℓ3 K (semilinearFixedSubfield σ) hcardk hK' σ
      hσ hσk
  have hNJ' := subfieldFixedGroup_le_plus hadm0 hp hp2 (semilinearFixedSubfield σ) hcardk hK' σ
    hσ hσk
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
  have hrange : fixedSubgroup (fieldAutT (coordinateQuadPlus n K) σ
      (coordinateQuadPlus_fieldAut n σ)) =
      (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n)).range :=
    (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
  have hfixι : ∀ y ∈ (incl (semilinearFixedSubfield σ)
      (coordinateQuadPlus_isExtension _ n)).range,
      fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) y = y := fun y hy =>
    mem_fixedSubgroup.1 (hrange ▸ hy)
  refine ⟨semilinearFixedSubfield σ, D.toMonoidHom.comp
    (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n)), hcardk0,
    D.injective.comp hinj, ?_, ?_⟩
  · intro v
    show α (D (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n) v)) =
      D (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n) v)
    rw [hαeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfixι _ ⟨v, rfl⟩]
  · intro x hx
    have h1 : fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) (D⁻¹ x) =
        D⁻¹ x := by
      rw [hαeq, MulAut.mul_apply, MulAut.mul_apply] at hx
      have h2 : D (fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ)
          (D⁻¹ x)) = D (D⁻¹ x) := by
        rw [hx, MulAut.apply_inv_self]
      exact D.injective h2
    have h3 : D⁻¹ x ∈ (incl (semilinearFixedSubfield σ)
        (coordinateQuadPlus_isExtension _ n)).range := hrange ▸ mem_fixedSubgroup.2 h1
    obtain ⟨v, hv⟩ := h3
    refine ⟨v, ?_⟩
    show D (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n) v) = x
    rw [hv, MulAut.apply_inv_self]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end

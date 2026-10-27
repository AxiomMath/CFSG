module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutOrthogonal
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnExcRank

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartOne
  CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.HardMathSupport.Lang.Proving
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.HardMathSupport.Dickson.Sec6.I923.OrthAux
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem rank_field_of_upD42Pumpup_omega_plus_semilinear
    {G : Type} [Group G] [Finite G] {n f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n 2 f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
    (β : MulAut G) (hout : β ∉ (MulAut.conj : G →* MulAut G).range)
    (hE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K))
    (hx : UpD42Pumpup G β) : n = 4 ∧ f = 3 := by
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f hG K hK e
  let E := coordinatePlusWitnessEquiv K e
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv G E.toEquiv
  have hβ3 : MulAut.congr E β ^ 3 = 1 := by rw [← map_pow, hx.1, map_one]
  have hD : MulAut.congr E β ∉ (linearConjugationHom (coordinateQuadPlus n K)).range := by
    intro h
    obtain ⟨t, ht⟩ := mem_inner_of_mem_D_three' hg h hβ3
    apply hout
    refine ⟨E.symm t, (MulAut.congr E).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      MulEquiv.apply_symm_apply, ht]
  have hne : MulAut.congr E β ≠ 1 := fun h => hD (h ▸ Subgroup.one_mem _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (MulAut.congr E β) = 3 := orderOf_eq_prime hβ3 hne
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n 2 f 3 hG Nat.prime_three (by norm_num) K hK e
    (MulAut.congr E β) hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hordσ, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ :=
    hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, hCM, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = 3 := by rw [hUr]; exact hordσ
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = 2 ^ (f / 3) := by
    rw [hUr]; exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
    fun x => RingHom.mem_eqLocusField
  have S := subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk Nat.prime_three
    (by norm_num) hord' (by have h := hG.1.2.2; omega : 3 ≤ n)
  have hxU : UpD42Pumpup (matrixProjectiveDerived (coordinateQuadPlus n K))
      (matrixProjectiveConjugationHom (coordinateQuadPlus n K) U) := by
    rw [hUκ]
    exact hx.congr E
  have hnf := rank_field_of_upD42Pumpup_fieldAutT_plus hCM.1 hcard' S
    (hxU.orthogonal_fieldDescent S U Θ g' hg'l hg'r hΘ)
  refine ⟨hnf.1, ?_⟩
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / 3 = m := by rw [hm]; exact Nat.mul_div_cancel_left m (by norm_num)
  rw [hdiv] at hnf
  omega

theorem not_upD42Pumpup_d4_off_semilinear
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hβ : β ∉ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    ¬ UpD42Pumpup (matrixProjectiveDerived (coordinateQuadPlus 4 K)) β := by
  intro hx
  obtain ⟨E, hE, hc⟩ := hx.exists_elemAbelian_81_fixed
  let ι := (fixSubgroup β).subtype
  have hE' := isElemAbelian_map_up34 ι (fixSubgroup β).subtype_injective hE
  have hfix : ∀ a ∈ E.map ι, β a = a := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have h9 := CFSG.HardMathSupport.Timmesfeld.DFour.card_le_nine_of_charTwo
    CFSG.StandardType.Triality.exists_form_ne_zero β hx.1 hβ (E.map ι) ⟨hE'.1, hE'.2⟩ hfix
  rw [Subgroup.card_map_of_injective (fixSubgroup β).subtype_injective, hc] at h9
  omega

theorem upD42Chev2Out_d4_holds : UpD42Chev2Out
    (fun d => match d with | .D r _ => r = 4 | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hd hc ⟨e⟩ α hout hx
  cases d with
  | D r q =>
    obtain rfl : r = 4 := hd
    have hp : q.p = 2 := hc
    have hC : StatedClassicalModel S .POmegaPlus 4 2 q.exponent := by
      rw [← hp]
      exact (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp
        (blueprintLieModel_D 4 q hv e)
    have hC0 := hC
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hC0
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        Nat.prime_two hC.1.2.1 hK
    let E := coordinatePlusWitnessEquiv K eK
    by_cases hE : MulAut.congr E α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)
    · have hf := (rank_field_of_upD42Pumpup_omega_plus_semilinear hC K hK eK
        α hout hE hx).2
      exact Or.inr (Or.inr ⟨⟨.D 4 q, hv⟩, ⟨rfl, hp, hf⟩, ⟨e⟩⟩)
    · exact (not_upD42Pumpup_d4_off_semilinear hE (hx.congr E)).elim
  | _ => exact hd.elim

end CFSG.HardMathSupport.Dickson.Sec6

end

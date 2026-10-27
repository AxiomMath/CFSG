module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoInvolution

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

universe u

theorem pComponent_of_fixedGroup_equiv (K : Type u) [Field K] [Finite K]
    (S : Subfield K) (hodd : Odd (Nat.card S))
    (a : Equiv.Perm (Omega K)) (e : coordinateD S ≃* fixedGroup K a)
    (ell : ℕ) [Fact ell.Prime] (L : Subgroup (fixedGroup K a))
    (hL : CFSG.IsPComponent ell L) :
    5 ≤ Nat.card S ∧ CFSG.IsQuasisimple L ∧ Nonempty (L ≃* coordinateG S) := by
  let M := L.map e.symm.toMonoidHom
  have hM : CFSG.IsPComponent ell M :=
    CatalogueBAlternating.pComponent_map_equiv ell e.symm L hL
  obtain ⟨hcard, hM_eq, hquasi⟩ :=
    CatalogueBLinearTwo.coordinateD_pComponent_classification S hodd ell M hM
  let r := L.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hquasiL : CFSG.IsQuasisimple L := CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv r
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))
  let g := r.trans ((MulEquiv.subgroupCongr hM_eq).trans
    (Subgroup.subgroupOfEquivOfLe (coordinateG_le_D S)))
  exact ⟨hcard, hquasiL, ⟨g⟩⟩

theorem involution_fixed_pComponent (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (_hsize : 5 ≤ Nat.card K)
    (a : coordinateE K) (ha : orderOf (a : Equiv.Perm (Omega K)) = 2)
    (ell : ℕ) [Fact ell.Prime]
    (L : Subgroup (fixedGroup K (a : Equiv.Perm (Omega K))))
    (hL : CFSG.IsPComponent ell L) :
    CFSG.IsQuasisimple L ∧ Even f ∧ ¬ (p = 3 ∧ f = 2) ∧
      Nat.card (frobeniusFixedField K p f hp hcard) = p ^ (f / 2) ∧
      Nonempty (L ≃* coordinateG (frobeniusFixedField K p f hp hcard)) := by
  rcases involution_fixedGroup_alternative K p f hp hodd hf hcard a ha with hsolvable | hquadratic
  · let : Group.IsSolvable (fixedGroup K (a : Equiv.Perm (Omega K))) := hsolvable
    exact (no_pComponent_of_solvable ell L hL).elim
  · obtain ⟨sigma, _hsigma, heven, hformula, hfixed, ⟨e⟩⟩ := hquadratic
    have hfield := fixedField_eq_frobeniusFixedField K p f hp hcard sigma hformula
    have hoddFixed := fixedField_card_odd K
      (ringChar_ne_two_of_card K p f hp hodd hcard) sigma
    obtain ⟨hbound, hquasi, ⟨r⟩⟩ := pComponent_of_fixedGroup_equiv K
      (CatalogueBLinearTwoFixed.fixedField K sigma) hoddFixed a e ell L hL
    have hexception : ¬ (p = 3 ∧ f = 2) := by
      intro h
      have hthree : p ^ (f / 2) = 3 := (quadratic_card_three_iff p f hf heven).mpr h
      rw [hfixed, hthree] at hbound
      omega
    have hcanonicalCard : Nat.card (frobeniusFixedField K p f hp hcard) = p ^ (f / 2) := by
      rw [← hfield]
      exact hfixed
    have hcanonicalIso : Nonempty (L ≃* coordinateG (frobeniusFixedField K p f hp hcard)) := by
      rw [← hfield]
      exact ⟨r⟩
    exact ⟨hquasi, heven, hexception, hcanonicalCard, hcanonicalIso⟩

theorem involution_fixedGroup_solvable_of_exception (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (_hsize : 5 ≤ Nat.card K)
    (a : coordinateE K) (ha : orderOf (a : Equiv.Perm (Omega K)) = 2)
    (hexception : (a : Equiv.Perm (Omega K)) ∈ coordinateD K ∨
      Odd f ∨ (p = 3 ∧ f = 2)) :
    Group.IsSolvable (fixedGroup K (a : Equiv.Perm (Omega K))) := by
  classical
  by_cases hlinear : (a : Equiv.Perm (Omega K)) ∈ coordinateD K
  · exact linear_involution_fixedGroup_solvable K p f hp hodd hcard a hlinear ha
  · obtain ⟨sigma, _hsigma, heven, _hformula, hfixed, ⟨e⟩⟩ :=
      nonlinear_involution_fixedGroup_structure K p f hp hodd hf hcard a ha hlinear
    rcases hexception with h | hoddF | hsmall
    · exact (hlinear h).elim
    · exact ((Nat.not_even_iff_odd.mpr hoddF) heven).elim
    · have hthree : Nat.card (CatalogueBLinearTwoFixed.fixedField K sigma) = 3 := by
        rw [hfixed, (quadratic_card_three_iff p f hf heven).mpr hsmall]
      let : Group.IsSolvable (coordinateD (CatalogueBLinearTwoFixed.fixedField K sigma)) :=
        coordinateD_three_solvable _ hthree
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem linear_two_involution_fixed_p_components (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hsize : 5 ≤ Nat.card K)
    (a : coordinateE K) (ha : orderOf (a : Equiv.Perm (Omega K)) = 2)
    (ell : ℕ) [Fact ell.Prime] :
    (∀ L : Subgroup (fixedGroup K (a : Equiv.Perm (Omega K))),
      CFSG.IsPComponent ell L → CFSG.IsQuasisimple L ∧ Even f ∧ ¬ (p = 3 ∧ f = 2) ∧
        Nat.card (frobeniusFixedField K p f hp hcard) = p ^ (f / 2) ∧
        Nonempty (L ≃* coordinateG (frobeniusFixedField K p f hp hcard))) ∧
      (((a : Equiv.Perm (Omega K)) ∈ coordinateD K ∨ Odd f ∨ (p = 3 ∧ f = 2)) →
        Group.IsSolvable (fixedGroup K (a : Equiv.Perm (Omega K))) ∧
          ∀ L : Subgroup (fixedGroup K (a : Equiv.Perm (Omega K))),
            ¬ CFSG.IsPComponent ell L) := by
  refine ⟨fun L hL => involution_fixed_pComponent K p f hp hodd hf hcard hsize a ha ell L hL,
    fun hexception => ?_⟩
  let : Group.IsSolvable (fixedGroup K (a : Equiv.Perm (Omega K))) :=
    involution_fixedGroup_solvable_of_exception K p f hp hodd hf hcard hsize a ha hexception
  exact ⟨inferInstance, fun L => no_pComponent_of_solvable ell L⟩

end

end CFSG.ComponentClassification.CatalogueBLinearTwoInvolution

module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LieType.Universal.Symplectic
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem eq_of_isComponent_of_normal_quasisimple {F : Type*} [Group F] {J L : Subgroup F}
    [J.Normal] (hJq : IsQuasisimple J) (hsolv : Group.IsSolvable (F ⧸ J))
    (hL : IsComponent L) : L = J := by
  obtain ⟨hLq, hLs⟩ := hL
  have hLJ : L ≤ J := by
    intro y hy
    have hf := MonoidHom.range_eq_bot_iff.1
      (LieType.Chevalley.OddToralOrdinary.range_eq_bot_of_commutator_eq_top
        (Group.isPerfect_def.mp hLq.1) ((QuotientGroup.mk' J).comp L.subtype))
    have hy' : (QuotientGroup.mk' J) y = 1 := DFunLike.congr_fun hf ⟨y, hy⟩
    exact (QuotientGroup.eq_one_iff y).1 hy'
  have hsub : (L.subgroupOf J).IsSubnormal := Subgroup.IsSubnormal.subgroupOf hLs
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hJq hsub with h | h
  · exact le_antisymm hLJ (Subgroup.subgroupOf_eq_top.mp h)
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hLq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hy : (⟨y, hLJ y.2⟩ : J) ∈ L.subgroupOf J := y.2
    have hc := Subgroup.mem_center_iff.mp (h hy) ⟨x, hLJ x.2⟩
    have hxy' : (x : F) * y = y * x := congrArg Subtype.val hc
    have hxy : x * y = y * x := Subtype.ext hxy'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem nonempty_centerQuotient_equiv_of_quotientFixed {X : Type*} [Group X] [Finite X]
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hinv : Z.map ψ.toMonoidHom = Z) (hC : IsQuasisimple (fixedSubgroup ψ))
    {L : Subgroup (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    Nonempty (L ⧸ center L ≃* fixedSubgroup ψ ⧸ center (fixedSubgroup ψ)) := by
  have hJn := CatalogueBFixedCentralQuotient.fixedImage_normal Z ψ hinv hcentral
  have hab := CatalogueBFixedCentralQuotient.fixed_quotient_abelian Z ψ hinv hcentral
  have hsurj := CatalogueBFixedCentralQuotient.fixedImageProjection_surjective Z ψ hinv
  have hker := CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central Z ψ hinv
    hcentral
  have hJq := LocalCores.isQuasisimple_of_surjective hC _ hsurj hker
  have hsolv : Group.IsSolvable (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ
      hinv) ⧸ CatalogueBFixedCentralQuotient.fixedImage Z ψ hinv) :=
    Group.isSolvable_of_comm fun a b => hab.is_comm.comm a b
  have hLJ := eq_of_isComponent_of_normal_quasisimple hJq hsolv hL
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hC _ hsurj hker
  exact ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hLJ)
    (Subgroup.map_center_eq (MulEquiv.subgroupCongr hLJ))).trans e.symm⟩

open CFSG.ComponentClassification.CatalogueBSymplecticB
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher in
theorem odd_psp_field_oddLieCentralQuotient {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {α : MulAut (StatedProj (StatedSp r K))} (A : gsp r K) (σ : K ≃+* K)
    (hα : α = conjAut r K A * fieldAut r K σ) (hσ2 : σ ^ 2 = 1) (hσ : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin r ⊕ Fin r) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin r ⊕ Fin r) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) : OddLieCentralQuotient p L := by
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have hr1 : 1 ≤ r := by omega
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  let e := projectiveStatedEquiv (K := K) hr1
  have hint : ∀ x, e (α x) = projectiveSemilinearConjugation (pairedSympForm K r) σ
      (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ) (e x) := by
    intro x
    rw [hα]
    exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
  let Φ := CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint
  have hdim : 0 < Module.finrank K (Fin r ⊕ Fin r → K) := by
    rw [SymplecticFlag.finrank_standard]
    omega
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2 hσ
    h2 hdim (pairedSympForm K r) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ d (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ) (semilinearCoordMap_sq _ σ hσ2 d hd)
  obtain ⟨-, -, -, -, hWfin, hWdim, -, halt, hnd, -, eC, -⟩ := hall b c hb hc
  have hcard := CatalogueBHigherLinearField.fixedField_card_square K σ hσ2 hσ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
    (show Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ∣ p ^ f from
      hK ▸ hcard ▸ dvd_pow_self _ two_ne_zero)
  have hfj : f = 2 * j := by
    have h1 : p ^ f = p ^ (2 * j) := by
      rw [← hK, hcard]
      change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) ^ 2 = _
      rw [hj, ← pow_mul, mul_comm]
    exact Nat.pow_right_injective hp.two_le h1
  have hk : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) = p ^ (f / 2) := by
    rw [hj, hfj, Nat.mul_div_cancel_left _ two_pos]
  have hf2 : 1 ≤ f / 2 := by
    rw [hfj, Nat.mul_div_cancel_left _ two_pos]
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hfj
    omega
  have hadm : StatedLieAdmissible .PSp r p (f / 2) := by
    refine ⟨hp, hf2, hr, fun h => ?_⟩
    have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ (f / 2)) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hdim' := hWdim.trans SymplecticFlag.finrank_standard
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdim'
  let Θ := (semilinearFixedCentralizerEquiv (pairedSympForm K r) σ
    (semilinearCoordMap (A : GL (Fin r ⊕ Fin r) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ)).trans (eC.trans eSp)
  have hSpq := LieType.Universal.Symplectic.isQuasisimple_of_admissible r
    (CatalogueBLinearTwoDescent.fixedSubfield K σ) hadm hk
  have hCq := LocalCores.isQuasisimple_of_mulEquiv Θ.symm hSpq
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  obtain ⟨eZ⟩ := nonempty_centerQuotient_equiv_of_quotientFixed (scalarSigns (pairedSympForm K r))
    (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ σ _ μ _ _) hCq hL'
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eTot : L ⧸ center L ≃*
      StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ) ⧸
        center (StatedSp r (CatalogueBLinearTwoDescent.fixedSubfield K σ)) :=
    ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eZ).trans
      (QuotientGroup.congr _ _ Θ (Subgroup.map_center_eq Θ))
  exact ⟨.PSp, r, f / 2, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient r _ hadm
      hk⟩)⟩

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
@[expose] def OddPSpInnerDiagInput : Prop :=
  ∀ (r : ℕ) (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    StatedLieAdmissible .PSp r p f → ∀ A : gsp r K, orderOf (conjAut r K A) = 2 →
      ∀ L : Subgroup (fixedSubgroup (conjAut r K A)), IsComponent L → OddLieCentralQuotient p L

theorem nonempty_mulEquiv_psp_of_lieModel' {J : Type} [Group J] {n p f : ℕ}
    (hadm : StatedLieAdmissible .PSp n p f) (hm : Blueprint.LieModel J .PSp n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (J ≃* StatedProj (StatedSp n K)) := by
  have hn : 2 ≤ n := hadm.2.2.1
  rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    exact ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  all_goals omega

open CFSG.LocalAnalysis.ComponentInitial SymplecticHigher in
theorem gls3OddFamilyInput_PSp (hinner : OddPSpInnerDiagInput) : GLS3OddFamilyInput .PSp := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  refine Or.inl ?_
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α * MulAut.congr e α = 1 := by
    have h2 := pow_orderOf_eq_one (MulAut.congr e α)
    rw [hβ] at h2
    rw [← pow_two]
    exact h2
  have hβ1 : MulAut.congr e α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hβ
    exact absurd hβ (by norm_num)
  obtain ⟨A, σ, hAσ, hσ2, ⟨d, hd⟩, -, -⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar hn).2.2 _ hβ2 hβ1
  have hKc' := LocalCores.isComponent_map_mulEquiv (fixedSubgroupCongrEquiv e α) hKc
  refine oddLieCentralQuotient_of_mulEquiv
    (Kc.equivMapOfInjective (fixedSubgroupCongrEquiv e α).toMonoidHom
      (fixedSubgroupCongrEquiv e α).injective) ?_
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hAσ
    have hord : orderOf (conjAut n K A) = 2 := hAσ ▸ hβ
    exact oddLieCentralQuotient_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAσ)) (hinner n K p f hp hp2 hK hadm A hord)
      hKc'
  · exact odd_psp_field_oddLieCentralQuotient hn hp hp2 hf hK A σ hAσ hσ2 hσ d hd hKc'

end CFSG.ComponentClassification.CatLeafProof

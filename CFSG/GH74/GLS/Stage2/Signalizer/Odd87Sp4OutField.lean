module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp
import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof

theorem exists_mulEquiv_quotient_of_quotientFixed {X : Type*} [Group X] [Finite X]
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hinv : Z.map ψ.toMonoidHom = Z) (hC : IsQuasisimple (FixedCommutingProduct.fixedSubgroup ψ))
    {L : Subgroup (FixedCommutingProduct.fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    Nonempty (L ≃* FixedCommutingProduct.fixedSubgroup ψ ⧸ Z.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ)) := by
  have hJn := CatalogueBFixedCentralQuotient.fixedImage_normal Z ψ hinv hcentral
  have hab := CatalogueBFixedCentralQuotient.fixed_quotient_abelian Z ψ hinv hcentral
  have hsurj := CatalogueBFixedCentralQuotient.fixedImageProjection_surjective Z ψ hinv
  have hker := CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central Z ψ hinv
    hcentral
  have hJq := LocalCores.isQuasisimple_of_surjective hC _ hsurj hker
  have hsolv : Group.IsSolvable (FixedCommutingProduct.fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ
      hinv) ⧸ CatalogueBFixedCentralQuotient.fixedImage Z ψ hinv) :=
    Group.isSolvable_of_comm fun a b => hab.is_comm.comm a b
  have hLJ := eq_of_isComponent_of_normal_quasisimple hJq hsolv hL
  exact ⟨(MulEquiv.subgroupCongr hLJ).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
      (QuotientGroup.quotientMulEquivOfEq
        (CatalogueBFixedCentralQuotient.fixedImageProjection_kernel Z ψ hinv)))⟩

theorem card_center_statedSp_two {k : Type} [Field k] [Finite k] (hk : Odd (Nat.card k)) :
    Nat.card (center (StatedSp 2 k)) = 2 := by
  rw [LieType.Universal.Symplectic.center_eq]
  have h1 : (StatedScalars (Fin 2 ⊕ Fin 2) k).subgroupOf (StatedSp 2 k) =
      (StatedSp 2 k ⊓ StatedScalars (Fin 2 ⊕ Fin 2) k).subgroupOf (StatedSp 2 k) := by
    rw [Subgroup.inf_subgroupOf_left]
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    LieType.Classical.card_statedSp_inf_statedScalars (by norm_num : 1 ≤ 2),
    LieType.Classical.card_sq_eq_one_units]
  obtain ⟨m, hm⟩ := hk
  rw [hm, Nat.add_sub_cancel]
  exact Nat.gcd_eq_left (dvd_mul_right 2 m)


open CFSG.ComponentClassification.CatalogueBSymplecticB
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.LocalAnalysis.ComponentInitial SymplecticFlag SymplecticHigher in
theorem psp4_field_component_model {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {α : MulAut (StatedProj (StatedSp 2 K))} (A : gsp 2 K) (σ : K ≃+* K)
    (hα : α = conjAut 2 K A * fieldAut 2 K σ) (hσ2 : σ ^ 2 = 1) (hσ : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) K) *
      CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) σ A =
        Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    {L : Subgroup (FixedCommutingProduct.fixedSubgroup α)} (hL : IsComponent L) :
    ∃ e : ℕ, 1 ≤ e ∧ LieModel ↥L .PSp 2 p e := by
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have hr1 : 1 ≤ 2 := by omega
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  let e := projectiveStatedEquiv (K := K) hr1
  have hint : ∀ x, e (α x) = projectiveSemilinearConjugation (pairedSympForm K 2) σ
      (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) μ (semilinearCoordMap_smul _ σ)
      (semilinearCoordMap_form _ σ μ hμ) (e x) := by
    intro x
    rw [hα]
    exact projectiveStatedEquiv_conjAut_fieldAut hr1 A σ μ hμ x
  let Φ := CatalogueBOrthogonalFixedTransfer.fixedEquivOfIntertwining e α _ hint
  have hdim : 0 < Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [SymplecticFlag.finrank_standard]
    omega
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2 hσ
    h2 hdim (pairedSympForm K 2) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate
    (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) μ d (semilinearCoordMap_smul _ σ)
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
  have hadm : StatedLieAdmissible .PSp 2 p (f / 2) := by
    refine ⟨hp, hf2, le_rfl, fun h => ?_⟩
    have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ (f / 2)) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hdim' := hWdim.trans SymplecticFlag.finrank_standard
  obtain ⟨eSp⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _ halt hnd hdim'
  let Θ := (semilinearFixedCentralizerEquiv (pairedSympForm K 2) σ
    (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ)).trans (eC.trans eSp)
  have hSpq := LieType.Universal.Symplectic.isQuasisimple_of_admissible 2
    (CatalogueBLinearTwoDescent.fixedSubfield K σ) hadm hk
  have hCq := LocalCores.isQuasisimple_of_mulEquiv Θ.symm hSpq
  have hL' := LocalCores.isComponent_map_mulEquiv Φ hL
  obtain ⟨eJ⟩ := exists_mulEquiv_quotient_of_quotientFixed (scalarSigns (pairedSympForm K 2))
    (scalarSigns_central _) _ (semilinear_scalarSigns_invariant _ σ _ μ _ _) hCq hL'
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hkodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hKodd
    (CatalogueBLinearTwoDescent.fixedSubfield K σ)
  set ψ := semilinearConjugation (pairedSympForm K 2) σ
    (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) μ (semilinearCoordMap_smul _ σ)
    (semilinearCoordMap_form _ σ μ hμ) with hψ
  have hnegfix : ψ (negIsometry (pairedSympForm K 2)) = negIsometry (pairedSympForm K 2) :=
    semilinearConjugation_negIsometry _ σ _ μ _ _
  have hneg1 : negIsometry (pairedSympForm K 2) ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : isometryGroup (pairedSympForm K 2) =>
      (g.val : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))
        (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) (Sum.inl 0)) h
    simp [negIsometry_apply] at h1
    exact h2 (by linear_combination -h1)
  have hle : (scalarSigns (pairedSympForm K 2)).subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) ≤
      center (FixedCommutingProduct.fixedSubgroup ψ) := by
    rw [← CatalogueBFixedCentralQuotient.fixedImageProjection_kernel
      (scalarSigns (pairedSympForm K 2)) ψ (semilinear_scalarSigns_invariant _ σ _ μ _ _)]
    exact CatalogueBFixedCentralQuotient.fixedImageProjection_kernel_central _ ψ _
      (scalarSigns_central _)
  have hcenter2 : Nat.card (center (FixedCommutingProduct.fixedSubgroup ψ)) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr Θ).toEquiv]
    exact card_center_statedSp_two hkodd
  have hn : (⟨negIsometry (pairedSympForm K 2), hnegfix⟩ : FixedCommutingProduct.fixedSubgroup ψ) ∈
      (scalarSigns (pairedSympForm K 2)).subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) :=
    (mem_scalarSigns_iff _ _).mpr (Or.inr rfl)
  have hker : (scalarSigns (pairedSympForm K 2)).subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) =
      center (FixedCommutingProduct.fixedSubgroup ψ) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcenter2]
    have : Nontrivial ((scalarSigns (pairedSympForm K 2)).subgroupOf (FixedCommutingProduct.fixedSubgroup ψ)) :=
      ⟨⟨⟨_, hn⟩, 1, fun h => hneg1 (by
        have := congrArg (fun x : (scalarSigns (pairedSympForm K 2)).subgroupOf
          (FixedCommutingProduct.fixedSubgroup ψ) => ((x : FixedCommutingProduct.fixedSubgroup ψ) : isometryGroup (pairedSympForm K 2))) h
        simpa using this)⟩⟩
    have := Finite.one_lt_card (α := (scalarSigns (pairedSympForm K 2)).subgroupOf
      (FixedCommutingProduct.fixedSubgroup ψ))
    omega
  let eL := L.equivMapOfInjective Φ.toMonoidHom Φ.injective
  let eQ : L ≃* StatedSp 2 (CatalogueBLinearTwoDescent.fixedSubfield K σ) ⧸
      center (StatedSp 2 (CatalogueBLinearTwoDescent.fixedSubfield K σ)) :=
    (eL.trans eJ).trans ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.congr _ _ Θ (Subgroup.map_center_eq Θ)))
  exact ⟨f / 2, hf2, LieType.CurtisTits.lieModel_of_mulEquiv eQ.symm
    (Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 _
      hadm hk⟩)⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightResidualStable
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixSeparate

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem exists_fieldPair_plusFour (hK : Nat.card K = 2 ^ f)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1)
    (hfp : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ ≠ 1) :
    ∃ S : similarityPairs (coordinateQuadPlus 4 K), S ∈ unitMultiplierPairs _ ∧
      matrixProjectiveConjugationHom _ S = α ∧ S.val.right * S.val.right = 1 ∧
      S.val.right ≠ 1 ∧
      ∀ v, coordinateSemilinearMap S.val (coordinateSemilinearMap S.val v) = v := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep hαE
  have hσ : plusImageFieldPart hf hK (by norm_num) ⟨matrixProjectiveConjugationHom _ S, hαE⟩ =
      S.val.right := plusImageFieldPart_kappa hf hK _ S
  rw [hσ] at hfp
  have hα1 : matrixProjectiveConjugationHom _ S ≠ 1 := fun h => hfp (by
    rw [← hσ]
    have h1 : (⟨matrixProjectiveConjugationHom _ S, hαE⟩ :
        matrixProjectiveImage (coordinateQuadPlus 4 K)) = 1 := Subtype.ext h
    rw [h1, map_one])
  have hord : orderOf (matrixProjectiveConjugationHom _ S) = 2 := orderOf_eq_prime hα2 hα1
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ := plusRealization hf hK (n := 4) (by norm_num)
  obtain ⟨hSS, hTT, -⟩ := hinv _ ⟨S, rfl⟩ hord S hS rfl
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus 4 K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  exact ⟨S, hS, rfl, hσσ, hfp, hTT⟩

theorem fieldCore_plusFour (hK : Nat.card K = 2 ^ f)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1)
    (hfp : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ ≠ 1) :
    Even (Nat.card ↥(perfectCore (autFixSubgroup α))) ∧
      ∀ (U : Sylow 2 ↥(perfectCore (autFixSubgroup α))) (z : ↥(perfectCore (autFixSubgroup α))),
        z ≠ 1 → (∀ u ∈ (U : Subgroup _), u * z = z * u) →
        IsLongRoot _ (z : matrixProjectiveDerived (coordinateQuadPlus 4 K)) ∧
          ∃ m, (α m)⁻¹ * m = z := by
  obtain ⟨S, hS, rfl, hσσ, hσ1, hTT⟩ := exists_fieldPair_plusFour hK hαE hα2 hfp
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨⟨F⟩, -, heven, hZT⟩ := fieldCore_spec (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    le_rfl hreg.1 hreg.2 hS hσσ hσ1 hTT
  exact ⟨by rw [Nat.card_congr F.toEquiv]; exact heven, hZT⟩

theorem fieldCore_simple_card_plusFour (hK : Nat.card K = 2 ^ f)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1)
    (hfp : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ ≠ 1) :
    Even f ∧ IsSimpleGroup ↥(perfectCore (autFixSubgroup α)) ∧
      ∃ τ : CFSG.Assembly.LowTwoRank.StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
        Nat.card ↥(perfectCore (autFixSubgroup α)) = F4Pilot.evenLieOrder τ 4 (f / 2) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  obtain ⟨S, hS, rfl, hσσ, hσ1, hTT⟩ := exists_fieldPair_plusFour hK hαE hα2 hfp
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨⟨F⟩, hsimple, -, -⟩ := fieldCore_spec hf hK le_rfl hreg.1 hreg.2 hS hσσ hσ1 hTT
  obtain ⟨τ, hτ, hcard⟩ := card_pairDescentDerived hf hK le_rfl hreg.1 hS hσσ hσ1 hTT
  exact ⟨(card_descentField hf hK hσσ hσ1).1, @MulEquiv.isSimpleGroup _ _ _ _ hsimple F,
    τ, hτ, (Nat.card_congr F.toEquiv).trans hcard⟩

section NonField

variable {n : ℕ}

open CFSG.Assembly.LowTwoRank (StatedProj StatedSp) in
theorem symmetryCore_spec_of_four_le (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {v : Fin (2 * n) → K} (hv : coordinateQuadPlus n K v = 1) :
    IsSimpleGroup ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) ∧
      ⁅perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)),
        perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))⁆ =
        perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ∧
      Nat.card ↥(perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v))) =
        Nat.card K ^ ((n - 1) ^ 2) * ∏ j ∈ Finset.Icc 1 (n - 1), (Nat.card K ^ (2 * j) - 1) := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hout : symmetryAut (coordinateQuadPlus n K) v ∉
      inner (matrixProjectiveDerived (coordinateQuadPlus n K)) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective _ y
    rw [← kappa_derived_eq_conj] at hy
    have h1 := CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
      hreg.1 hreg.2 hE (a₁ := Subgroup.inclusion (matrixDerived_le_isometries _) g)
      (a₂ := symmetryIsometry _ v) hy
    apply CFSG.ComponentClassification.EvenOrthSelector.symmetryGL_not_mem_matrixDerived
      hreg.1 hreg.2 hE hv
    have h2 : ((Subgroup.inclusion (matrixDerived_le_isometries _) g : matrixIsometries _) :
        GL (Fin (2 * n)) K) = symmetryGL _ v := congrArg Subtype.val h1
    rw [← h2]
    exact g.2
  obtain ⟨ε⟩ := F4Pilot.omega_symmetry_fixed hf hK (by omega) hreg.1 hreg.2 hE hv hout
  obtain ⟨hSs, hSp⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (r := n - 1)
    (k := K) (by omega) (by omega)
  have e : ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) ≃*
      StatedProj (StatedSp (n - 1) K) :=
    (MulEquiv.subgroupCongr (autFixSubgroup_eq_fixedSubgroup' _)).trans (ε.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot
          (n - 1))).trans QuotientGroup.quotientBot).symm)
  have hFperf : Group.IsPerfect ↥(autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hXβ : perfectCore (autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v)) =
      autFixSubgroup (symmetryAut (coordinateQuadPlus n K) v) :=
    CFSG.Quasithin.perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hFperf)
  rw [hXβ]
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ hSs e, Subgroup.isPerfect_iff.mp hFperf,
    (Nat.card_congr e.toEquiv).trans
      (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (n - 1))⟩

theorem not_isSimpleGroup_core_of_two_le_rank_of_four_le (hn : 4 ≤ n)
    (s : matrixIsometries (coordinateQuadPlus n K))
    (hs2 : orderOf (isometryConjugationHom _ s) = 2)
    (hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank) :
    ¬ IsSimpleGroup ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  intro hsimple
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hchar :=
    CFSG.ComponentClassification.CatLeafProof.isCharacteristicP_inner_centralizer_of_two_le_rank
      hreg.1 hreg.2 hE s hs2 hr
  have hcj :=
    CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
      hreg.1 hreg.2 hE
  have hchar' := CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (CFSG.ComponentClassification.CatLeafProof.fixedInnerEquiv hcj _).symm hchar
  rw [← autFixSubgroup_eq_fixedSubgroup'] at hchar'
  have hN : ((perfectCore (autFixSubgroup (isometryConjugationHom _ s))).subgroupOf
      (autFixSubgroup (isometryConjugationHom _ s))).Normal :=
    CFSG.Quasithin.perfectCore_normal _
  have hNs : IsSimpleGroup ↥((perfectCore (autFixSubgroup (isometryConjugationHom _ s))).subgroupOf
      (autFixSubgroup (isometryConjugationHom _ s))) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hsimple (Subgroup.subgroupOfEquivOfLe (perfectCore_le _))
  exact false_of_isCharacteristicP_of_normal_simple (p := 2) hchar' hN hNs
    (commutator_perfectCore_subgroupOf _)

end NonField

theorem nonField_cases_four (hK : Nat.card K = 2 ^ f)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hfp : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ = 1) :
    (∃ v : Fin (2 * 4) → K, coordinateQuadPlus 4 K v = 1 ∧
        α = symmetryAut (coordinateQuadPlus 4 K) v) ∨
      ∃ s : matrixIsometries (coordinateQuadPlus 4 K), α = isometryConjugationHom _ s ∧
        orderOf (isometryConjugationHom _ s) = 2 ∧
        2 ≤ (((s : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) - 1).rank := by
  have hreg := regular_coordinateQuadPlus 4 K (by norm_num)
  have hE := commutator_coordinateQuadPlus 4 K (by norm_num)
  obtain ⟨s, hs⟩ := (plusImageFieldPart_eq_one_iff _ hK _ ⟨α, hαE⟩).mp hfp
  change isometryConjugationHom _ s = α at hs
  subst hs
  have hs2 : orderOf (isometryConjugationHom _ s) = 2 := orderOf_eq_prime hα2 hα1
  by_cases hr : 2 ≤ (((s : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) - 1).rank
  · exact Or.inr ⟨s, rfl, hs2, hr⟩
  · left
    have hss : s * s = 1 := by
      apply CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.isometryKappa_injective
        hreg.1 hreg.2 hE
      rw [map_mul, map_one]
      change isometryConjugationHom _ s * isometryConjugationHom _ s = 1
      rw [← pow_two]
      exact hα2
    have hs1 : (s : GL (Fin (2 * 4)) K) ≠ 1 := by
      intro h
      apply hα1
      have : s = 1 := Subtype.ext h
      rw [this, map_one]
    obtain ⟨v, hv, hsv⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical.exists_symmetry_of_rank_le_one
        hreg.1 s.2 (congrArg Subtype.val hss) hs1 (by omega)
    have hincl : s = symmetryIsometry _ v := Subtype.ext hsv
    subst hincl
    exact ⟨v, hv, rfl⟩

theorem fieldCoresSeparated_plusFour (hK : Nat.card K = 2 ^ f)
    {α β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1)
    (hfpα : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ ≠ 1)
    (hβE : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfpβ : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨β, hβE⟩ = 1) :
    IsEmpty (↥(perfectCore (autFixSubgroup α)) ≃* ↥(perfectCore (autFixSubgroup β))) := by
  refine ⟨fun ψ => ?_⟩
  obtain ⟨hfeven, hsimple, τ, hτ, hcard⟩ := fieldCore_simple_card_plusFour hK hαE hα2 hfpα
  rcases nonField_cases_four hK hβE hβ2 hβ1 hfpβ with ⟨v, hv, rfl⟩ | ⟨s, rfl, hs2, hr⟩
  · obtain ⟨-, -, hcardβ⟩ := symmetryCore_spec_of_four_le hK le_rfl hv
    have hψcard := Nat.card_congr ψ.toEquiv
    have hk2 : 1 ≤ f / 2 := by
      obtain ⟨m, hm⟩ := hfeven
      have : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hK
      omega
    obtain ⟨r, hr_odd, hr_eq⟩ : ∃ r, Odd r ∧
        F4Pilot.evenLieOrder τ 4 (f / 2) = 2 ^ (f / 2 * (4 * (4 - 1))) * r := by
      rcases hτ with rfl | rfl
      · exact (F4Pilot.profile_idxD (by norm_num) hk2).two
      · exact (F4Pilot.profile_idx2D (by norm_num) hk2).two
    have hP : Odd (∏ j ∈ Finset.Icc 1 (4 - 1), (Nat.card K ^ (2 * j) - 1)) := by
      rw [hK]
      have hf1 : 1 ≤ f := LinearPilot.one_le_of_card_eq_two_pow hK
      exact CFSG.Timmesfeld.Orders.odd_prod fun j hj =>
        CFSG.Timmesfeld.Orders.odd_pow_sub_one hf1 (by simp at hj; omega)
    have hpow : Nat.card K ^ ((4 - 1) ^ 2) = 2 ^ (f * (4 - 1) ^ 2) := by rw [hK, ← pow_mul]
    have key := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr_odd hP (by
      rw [← hr_eq, ← hcard, hψcard, ← hpow]
      exact hcardβ)
    obtain ⟨g, hg⟩ := hfeven
    norm_num at key
    omega
  · exact not_isSimpleGroup_core_of_two_le_rank_of_four_le le_rfl s hs2 hr
      (@MulEquiv.isSimpleGroup _ _ _ _ hsimple ψ.symm)

theorem fieldRecentre_of_field_four (hK : Nat.card K = 2 ^ f)
    {α β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))}
    (hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hα2 : α ^ 2 = 1)
    (hfpα : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨α, hαE⟩ ≠ 1)
    (hβE : β ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) (hβ2 : β ^ 2 = 1)
    (hfpβ : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num)
      ⟨β, hβE⟩ ≠ 1)
    (Γ : Type) [Group Γ] [Finite Γ]
    (φ₁ φ₂ : matrixProjectiveDerived (coordinateQuadPlus 4 K) →* Γ)
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    (hX : (perfectCore (autFixSubgroup α)).map φ₁ = (perfectCore (autFixSubgroup β)).map φ₂) :
    ∃ m, (α m)⁻¹ * m ∈ perfectCore (autFixSubgroup α) ∧
      ∃ z, IsLongRoot (coordinateQuadPlus 4 K) z ∧ φ₂ z = φ₁ ((α m)⁻¹ * m) := by
  obtain ⟨hevenα, hZTα⟩ := fieldCore_plusFour hK hαE hα2 hfpα
  obtain ⟨-, hZTβ⟩ := fieldCore_plusFour hK hβE hβ2 hfpβ
  obtain ⟨U, z, hz1, hzU⟩ := exists_ne_one_commute_sylow hevenα
  obtain ⟨-, m, hm⟩ := hZTα U z hz1 hzU
  set ψ : ↥(perfectCore (autFixSubgroup α)) ≃* ↥(perfectCore (autFixSubgroup β)) :=
    ((perfectCore (autFixSubgroup α)).equivMapOfInjective φ₁ hφ₁).trans
      ((MulEquiv.subgroupCongr hX).trans
        ((perfectCore (autFixSubgroup β)).equivMapOfInjective φ₂ hφ₂).symm) with hψ
  have hψz : φ₂ (ψ z : matrixProjectiveDerived (coordinateQuadPlus 4 K)) = φ₁ z := by
    have h1 : (perfectCore (autFixSubgroup β)).equivMapOfInjective φ₂ hφ₂ (ψ z) =
        MulEquiv.subgroupCongr hX
          ((perfectCore (autFixSubgroup α)).equivMapOfInjective φ₁ hφ₁ z) := by
      rw [hψ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun y : ↥((perfectCore (autFixSubgroup β)).map φ₂) => (y : Γ)) h1
    simp only [Subgroup.coe_equivMapOfInjective_apply] at h2
    exact h2
  obtain ⟨U', hU'⟩ := exists_sylow_commute_map ψ U hzU
  have hψz1 : ψ z ≠ 1 := fun h => hz1 (ψ.injective (h.trans (map_one ψ).symm))
  obtain ⟨hL, -⟩ := hZTβ U' (ψ z) hψz1 hU'
  refine ⟨m, by rw [hm]; exact z.2, ψ z, hL, ?_⟩
  rw [hm, hψz]

theorem fieldRecentreInE_plusFour (hK : Nat.card K = 2 ^ f) :
    FieldRecentreInE (matrixProjectiveImage (coordinateQuadPlus 4 K))
      (plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK (by norm_num))
      (IsLongRoot (coordinateQuadPlus 4 K)) := by
  intro α β hαE hβE hα2 hfp hβ2 hβ1 Γ _ _ φ₁ φ₂ hφ₁ hφ₂ hX
  by_cases hfpβ : plusImageFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK
      (by norm_num) ⟨β, hβE⟩ = 1
  · exfalso
    exact (fieldCoresSeparated_plusFour hK hαE hα2 hfp hβE hβ2 hβ1 hfpβ).false
      (((perfectCore (autFixSubgroup α)).equivMapOfInjective φ₁ hφ₁).trans
        ((MulEquiv.subgroupCongr hX).trans
          ((perfectCore (autFixSubgroup β)).equivMapOfInjective φ₂ hφ₂).symm))
  · exact fieldRecentre_of_field_four hK hαE hα2 hfp hβE hβ2 hfpβ Γ φ₁ φ₂ hφ₁ hφ₂ hX

end CFSG.SeitzReduction.OmegaPilot

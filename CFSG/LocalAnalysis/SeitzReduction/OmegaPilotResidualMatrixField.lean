module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldGalois

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)

section Trace

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_kappa_inv_mul_eq_eichler [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT3 : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ x ∈ U, Q x = 0)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hσσ : S.val.right * S.val.right = 1) (hσ1 : S.val.right ≠ 1) {u w : Fin d → K}
    (hTu : coordinateSemilinearMap S.val u = u) (hTw : coordinateSemilinearMap S.val w = w)
    (huw : polar Q u w = 0) :
    ∃ m : matrixProjectiveDerived Q, (matrixProjectiveConjugationHom Q S m)⁻¹ * m =
      projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT3 u w⟩ := by
  have hσσ' : ∀ a, S.val.right (S.val.right a) = a := fun a => by
    change (S.val.right * S.val.right) a = a
    rw [hσσ]
    rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c, S.val.right c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨t, ht⟩ : ∃ t : K, t = c₀ - S.val.right c₀ := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := by
    rw [ht]
    exact sub_ne_zero.mpr (Ne.symm hc₀)
  have hσt : S.val.right t = t := by
    rw [ht, map_sub, hσσ', CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  obtain ⟨c, hc⟩ : ∃ c : K, c = t⁻¹ * c₀ := ⟨_, rfl⟩
  have hc1 : c - S.val.right c = 1 := by
    rw [hc, map_mul, map_inv₀, hσt, ← mul_sub, ← ht, inv_mul_cancel₀ ht0]
  have hpol : ∀ a : K, polar Q u (a • w) = 0 := fun a => by
    rw [polar_smul_right, huw, smul_zero]
  obtain ⟨E₁, hE₁⟩ : ∃ E : orthDerived Q,
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) = eichler Q u (c • w) :=
    ⟨⟨_, eichler_mem_orthDerived hQ hT3 _ _⟩, rfl⟩
  obtain ⟨E₂, hE₂⟩ : ∃ E : orthDerived Q,
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) = eichler Q u (S.val.right c • w) :=
    ⟨⟨_, eichler_mem_orthDerived hQ hT3 _ _⟩, rfl⟩
  have hαm : matrixProjectiveConjugationHom Q S (projHom Q E₁) = projHom Q E₂ := by
    refine kappa_projHom S E₁ E₂ fun x => ?_
    rw [hE₁, hE₂, semilinear_eichler_conj (coordinateSemilinearMap_smul S.val)
      (pairSemilinearMap_quad hS), coordinateSemilinearMap_smul, hTu, hTw]
  refine ⟨projHom Q E₁, ?_⟩
  rw [hαm, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hE₁, hE₂, eichler_inv (hpol _),
    eichler_mul (by rw [polar_neg_right, hpol, neg_zero]) (hpol _)]
  congr 1
  rw [← sub_eq_neg_add, ← sub_smul, hc1, one_smul]

end Trace

section FieldCore

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem exists_ne_one_commute_sylow {X : Type*} [Group X] [Finite X] (hX : Even (Nat.card X)) :
    ∃ (U : Sylow 2 X) (z : X), z ≠ 1 ∧ ∀ u ∈ (U : Subgroup X), u * z = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 X))
  have hne : (U : Subgroup X) ≠ ⊥ := U.ne_bot_of_dvd_card (even_iff_two_dvd.mp hX)
  have : Nontrivial (U : Subgroup X) := ((U : Subgroup X).nontrivial_iff_ne_bot).mpr hne
  have := U.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (U : Subgroup X))
  refine ⟨U, ((z : U) : X), fun h => hz1 (Subtype.ext (Subtype.ext h)), fun u hu => ?_⟩
  have h := Subgroup.mem_center_iff.mp z.2 ⟨u, hu⟩
  exact congrArg Subtype.val h


set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem fieldCore_spec (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hT3 : ∃ U : Submodule K (Fin (2 * n) → K), Module.finrank K U = 3 ∧ ∀ x ∈ U, Q x = 0)
    {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (hσσ : S.val.right * S.val.right = 1) (hσ1 : S.val.right ≠ 1)
    (hTT : ∀ v, coordinateSemilinearMap S.val (coordinateSemilinearMap S.val v) = v) :
    Nonempty (↥(perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S))) ≃*
        ↥(pairDescentDerived hS)) ∧
      IsSimpleGroup ↥(pairDescentDerived hS) ∧ Even (Nat.card ↥(pairDescentDerived hS)) ∧
      ∀ (U : Sylow 2 ↥(perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S))))
        (z : ↥(perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S)))), z ≠ 1 →
        (∀ u ∈ (U : Subgroup _), u * z = z * u) →
        IsLongRoot Q (z : matrixProjectiveDerived Q) ∧
          ∃ m : matrixProjectiveDerived Q, (matrixProjectiveConjugationHom Q S m)⁻¹ * m = z := by
  have hσσ' : ∀ a, S.val.right (S.val.right a) = a := fun a => by
    change (S.val.right * S.val.right) a = a
    rw [hσσ]
    rfl
  obtain ⟨c, hc⟩ : ∃ c, S.val.right c ≠ c := by
    by_contra! h
    exact hσ1 (RingEquiv.ext h)
  obtain ⟨hfeven, hk, -⟩ := card_descentField hf hK hσσ hσ1
  have hk2 : 1 ≤ f / 2 := by
    obtain ⟨m, hm⟩ := hfeven
    omega
  have : CharP (descentField S.val.right) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hk2 hk
  obtain ⟨hfin, -, -, hQ₀, -, -, -, e, he⟩ := even_quadratic_semilinear_involution_descent
    hσσ hσ1 hQ (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  have hspan : Submodule.span K (pairFix S : Set (Fin (2 * n) → K)) = ⊤ :=
    span_fixSpace hσσ' hTT hc
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ :=
    (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.2.2.2 n hdim hn
  obtain ⟨hJE, hsimple, heven⟩ := derived_simple_even hn (pairDescentForm hS) hQ₀ hdim
  have hperf := commutator_elementaryGroup_eq_top h₁₂ h₁₃ h₂₃ hQ₀
  have hJ : commutator ↥(pairDescentDerived hS) = ⊤ := by
    change commutator ↥⁅TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS),
      TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)⁆ = ⊤
    rw [hJE]
    exact hperf
  have hQc : ∀ x : pairFix S, Q (x : Fin (2 * n) → K) = ((pairDescentForm hS x :
      descentField S.val.right) : K) := fun x =>
    (coe_descentForm (pairSemilinearMap_quad hS) x).symm
  have hPc : ∀ x y : pairFix S, polar Q (x : Fin (2 * n) → K) (y : Fin (2 * n) → K) =
      ((polar (pairDescentForm hS) x y : descentField S.val.right) : K) := fun x y =>
    (CFSG.ComponentClassification.UnbalancedCatalog.coe_polar_descentForm (pairSemilinearMap_quad hS) x y).symm
  have hQne : ∃ v, Q v ≠ 0 := by
    refine ⟨((P₁.e + P₁.f : pairFix S) : Fin (2 * n) → K), ?_⟩
    rw [hQc, QuadraticMap.map_add (pairDescentForm hS), P₁.Q_e, P₁.Q_f, P₁.polar_ef, zero_add,
      zero_add, OneMemClass.coe_one]
    exact one_ne_zero
  have hX := perfectCore_autFixSubgroup_eq e hQne hJ
  obtain ⟨F, hF⟩ : ∃ F : ↥(perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S))) ≃*
      ↥(pairDescentDerived hS),
      F = (MulEquiv.subgroupCongr hX).trans (descentImageEquiv e hQne).symm := ⟨_, rfl⟩
  refine ⟨⟨F⟩, hsimple, heven, fun U z hz1 hzU => ?_⟩
  have : Finite ↥(pairDescentDerived hS) := Finite.of_equiv _ F.toEquiv
  obtain ⟨U', hU'⟩ := exists_sylow_commute_map F U hzU
  have hg1 : F z ≠ 1 := fun h => hz1 (F.injective (h.trans (map_one F).symm))
  have hEΩ : ∀ a b, eichler (pairDescentForm hS) a b ∈ pairDescentDerived hS := fun a b => by
    change _ ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS),
      TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)⁆
    rw [hJE]
    exact eichler_mem_elementaryGroup _ _ _
  obtain ⟨x, hxΩ, c', hc'0, hgx⟩ :=
    exists_eq_eichler_of_commute_sylow hQ₀ h₁₂ h₁₃ h₂₃ hEΩ U' hg1 hU'
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS) :=
    Subgroup.commutator_le_self _ hxΩ
  have hzF : (z : matrixProjectiveDerived Q) = projHom Q (descentDerivedExt e (F z)) := by
    have h1 : descentImageEquiv e hQne (F z) = MulEquiv.subgroupCongr hX z := by
      rw [hF, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have h2 := congrArg (fun y : descentImage e => (y : matrixProjectiveDerived Q)) h1
    rw [coe_descentImageEquiv] at h2
    exact h2.symm
  have hx0 : pairDescentForm hS (x P₁.e) = 0 := by rw [map_of_mem hxO, P₁.Q_e]
  have hxy0 : polar (pairDescentForm hS) (x P₁.e) (c' • x P₂.e) = 0 := by
    rw [polar_smul_right, polar_map_of_mem hxO, h₁₂.ee, smul_zero]
  have hFz : F z = ⟨eichler (pairDescentForm hS) (x P₁.e) (c' • x P₂.e), hEΩ _ _⟩ :=
    Subtype.ext hgx
  have hext := coe_descentDerivedExt_eichler e he hspan hx0 hxy0 (hEΩ _ _)
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * n) → K, u = ((x P₁.e : pairFix S) : Fin (2 * n) → K) :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin (2 * n) → K,
      w = ((c' • x P₂.e : pairFix S) : Fin (2 * n) → K) := ⟨_, rfl⟩
  have hzE : (z : matrixProjectiveDerived Q) =
      projHom Q ⟨eichler Q u w, eichler_mem_orthDerived hQ hT3 u w⟩ := by
    rw [hzF, hFz]
    congr 1
    apply Subtype.ext
    rw [hext, hu, hw]
  have hu0 : Q u = 0 := by rw [hu, hQc, hx0, ZeroMemClass.coe_zero]
  have hw0 : Q w = 0 := by
    rw [hw, hQc, QuadraticMap.map_smul, map_of_mem hxO, P₂.Q_e, smul_zero,
      ZeroMemClass.coe_zero]
  have huw : polar Q u w = 0 := by rw [hu, hw, hPc, hxy0, ZeroMemClass.coe_zero]
  refine ⟨?_, ?_⟩
  · refine ⟨u, w, hu0, hw0, huw, ?_, ⟨eichler Q u w, eichler_mem_orthDerived hQ hT3 u w⟩, rfl,
      hzE.symm⟩
    have huf₁ : polar Q u ((x P₁.f : pairFix S) : Fin (2 * n) → K) = 1 := by
      rw [hu, hPc, polar_map_of_mem hxO, P₁.polar_ef, OneMemClass.coe_one]
    have hwf₁ : polar Q w ((x P₁.f : pairFix S) : Fin (2 * n) → K) = 0 := by
      rw [hw, hPc, polar_smul_left, polar_map_of_mem hxO, polar_comm, h₁₂.fe, smul_zero,
        ZeroMemClass.coe_zero]
    have huf₂ : polar Q u ((x P₂.f : pairFix S) : Fin (2 * n) → K) = 0 := by
      rw [hu, hPc, polar_map_of_mem hxO, h₁₂.ef, ZeroMemClass.coe_zero]
    have hwf₂ : polar Q w ((x P₂.f : pairFix S) : Fin (2 * n) → K) = (c' : K) := by
      rw [hw, hPc, polar_smul_left, polar_map_of_mem hxO, P₂.polar_ef, smul_eq_mul, mul_one]
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => polar Q v ((x P₁.f : pairFix S) : Fin (2 * n) → K)) hab
    have h2 := congrArg (fun v => polar Q v ((x P₂.f : pairFix S) : Fin (2 * n) → K)) hab
    simp only [polar_add_left, polar_smul_left, huf₁, hwf₁, huf₂, hwf₂, polar_zero_left,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    refine ⟨h1, (mul_eq_zero.mp h2).resolve_right ?_⟩
    exact fun h => hc'0 (Subtype.ext h)
  · obtain ⟨m, hm⟩ := exists_kappa_inv_mul_eq_eichler hQ hT3 hS hσσ hσ1
      (u := u) (w := w) (by rw [hu]; exact (x P₁.e).2) (by rw [hw]; exact (c' • x P₂.e).2) huw
    exact ⟨m, hm.trans hzE.symm⟩

end FieldCore


section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem fieldCore_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα2 : α ^ 2 = 1)
    (hfp : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn α ≠ 1) :
    Even (Nat.card ↥(perfectCore (autFixSubgroup α))) ∧
      ∀ (U : Sylow 2 ↥(perfectCore (autFixSubgroup α))) (z : ↥(perfectCore (autFixSubgroup α))),
        z ≠ 1 → (∀ u ∈ (U : Subgroup _), u * z = z * u) →
        IsLongRoot _ (z : matrixProjectiveDerived (coordinateQuadPlus n K)) ∧
          ∃ m, (α m)⁻¹ * m = z := by
  obtain ⟨S, hS, rfl, hσσ, hσ1, hTT⟩ := exists_fieldPair_plus hK hn hα2 hfp
  have hreg := regular_coordinateQuadPlus n K (by omega)
  obtain ⟨⟨F⟩, -, heven, hZT⟩ := fieldCore_spec (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    (by omega) hreg.1 hreg.2 hS hσσ hσ1 hTT
  exact ⟨by rw [Nat.card_congr F.toEquiv]; exact heven, hZT⟩

theorem fieldRecentre_of_field (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {α β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα2 : α ^ 2 = 1)
    (hfpα : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn α ≠ 1)
    (hβ2 : β ^ 2 = 1)
    (hfpβ : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn β ≠ 1)
    (Γ : Type) [Group Γ] [Finite Γ]
    (φ₁ φ₂ : matrixProjectiveDerived (coordinateQuadPlus n K) →* Γ)
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    (hX : (perfectCore (autFixSubgroup α)).map φ₁ = (perfectCore (autFixSubgroup β)).map φ₂) :
    ∃ m, (α m)⁻¹ * m ∈ perfectCore (autFixSubgroup α) ∧
      ∃ z, IsLongRoot (coordinateQuadPlus n K) z ∧ φ₂ z = φ₁ ((α m)⁻¹ * m) := by
  obtain ⟨hevenα, hZTα⟩ := fieldCore_plus hK hn hα2 hfpα
  obtain ⟨-, hZTβ⟩ := fieldCore_plus hK hn hβ2 hfpβ
  obtain ⟨U, z, hz1, hzU⟩ := exists_ne_one_commute_sylow hevenα
  obtain ⟨-, m, hm⟩ := hZTα U z hz1 hzU
  set ψ : ↥(perfectCore (autFixSubgroup α)) ≃* ↥(perfectCore (autFixSubgroup β)) :=
    ((perfectCore (autFixSubgroup α)).equivMapOfInjective φ₁ hφ₁).trans
      ((MulEquiv.subgroupCongr hX).trans
        ((perfectCore (autFixSubgroup β)).equivMapOfInjective φ₂ hφ₂).symm) with hψ
  have hψz : φ₂ (ψ z : matrixProjectiveDerived (coordinateQuadPlus n K)) = φ₁ z := by
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

end Plus

end CFSG.SeitzReduction.OmegaPilot

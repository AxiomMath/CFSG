module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverImage
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverGen

public section

namespace CFSG.SeitzReduction.F4Pilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer descentField
  mem_descentField)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry (eichler_isometry
  elementaryGroup_map)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (rootElt rootElt_eps_sub_eps'
  rootElt_neg_eps_add_eps' rootElt_eps_add_eps' rootElt_neg_eps_sub_eps' eps neg_mem_roots)

theorem tailModelEquiv_hypVec_inr {K : Type*} [Field K] {r : ℕ} {κ : Type*} [DecidableEq κ]
    (i : Fin r) :
    tailModelEquiv r K κ (hypVec K (κ → K) (.inr i)) = Pi.single (.inr (.inl i)) 1 := by
  funext x
  rcases x with j | j | j
  · rw [tailModelEquiv_inl, hypVec]
    simp
  · rw [tailModelEquiv_inr_inl, hypVec]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · rw [tailModelEquiv_inr_inr, hypVec]
    simp

section Images


variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

variable (σ) in
@[expose] noncomputable def twCoverImage :
    Subgroup ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ)) :=
  (twCoverPhi σ hσσ hω).range.map
    (elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))).subtype

include hω in
theorem eichler_long_zero_mem (t : descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inl 0) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) ∈
        twCoverImage σ hσσ hω := by
  obtain ⟨x, hx⟩ := exists_twLevi_xm_fixed (σ := σ) (k := 0) (Or.inl rfl) (s := 1) (Or.inl rfl)
    (c := (t : F)) (mem_descentField.1 t.2)
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inl _) ?_ (x := x) ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 0 (t : F)⟩)
      (by rw [hx, one_smul, e6IsogenyM_xm_single]), d4Psi_xUnit, simpleRoot_zero,
      rootElt_eps_sub_eps' (by decide), map_smul, d4Iota_single_inl, d4Iota_single_inr,
      Subfield.smul_def, Subfield.coe_neg]
    rfl

include hω in
theorem eichler_long_zero_neg_mem (t : descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inl 1) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 0)) 1) ∈
        twCoverImage σ hσσ hω := by
  obtain ⟨x, hx⟩ := exists_twLevi_xm_fixed (σ := σ) (k := 0) (Or.inl rfl) (s := -1) (Or.inr rfl)
    (c := (t : F)) (mem_descentField.1 t.2)
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inl _) ?_ (x := x) ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 0 (t : F)⟩)
      (by rw [hx, neg_one_smul, e6IsogenyM_xm_neg_single]), d4Psi_yUnit, simpleRoot_zero,
      neg_sub, sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide), map_smul, d4Iota_single_inl,
      d4Iota_single_inr, Subfield.smul_def, Subfield.coe_neg]
    rfl

include hω in
theorem eichler_long_one_mem (t : descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inl 1) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 2)) 1) ∈
        twCoverImage σ hσσ hω := by
  obtain ⟨x, hx⟩ := exists_twLevi_xm_fixed (σ := σ) (k := 1) (Or.inr rfl) (s := 1) (Or.inl rfl)
    (c := (t : F)) (mem_descentField.1 t.2)
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inl _) ?_ (x := x) ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 1 (t : F)⟩)
      (by rw [hx, one_smul, e6IsogenyM_xm_single]), d4Psi_xUnit, simpleRoot_one,
      rootElt_eps_sub_eps' (by decide), map_smul, d4Iota_single_inl, d4Iota_single_inr,
      Subfield.smul_def, Subfield.coe_neg]
    rfl

include hω in
theorem eichler_long_one_neg_mem (t : descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inl 2) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) ∈
        twCoverImage σ hσσ hω := by
  obtain ⟨x, hx⟩ := exists_twLevi_xm_fixed (σ := σ) (k := 1) (Or.inr rfl) (s := -1) (Or.inr rfl)
    (c := (t : F)) (mem_descentField.1 t.2)
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inl _) ?_ (x := x) ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 1 (t : F)⟩)
      (by rw [hx, neg_one_smul, e6IsogenyM_xm_neg_single]), d4Psi_yUnit, simpleRoot_one,
      neg_sub, sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide), map_smul, d4Iota_single_inl,
      d4Iota_single_inr, Subfield.smul_def, Subfield.coe_neg]
    rfl

include hω in
theorem eichler_short_mem (a : Fin 2 → descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inl 2) 1) (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) ∈
        twCoverImage σ hσσ hω := by
  set c : F := -((a 0 : F) + (a 1 : F) * σ ω) with hc
  have ha0 : σ (a 0 : F) = a 0 := mem_descentField.1 (a 0).2
  have ha1 : σ (a 1 : F) = a 1 := mem_descentField.1 (a 1).2
  have hσc : σ c = -((a 0 : F) + (a 1 : F) * ω) := by
    rw [hc, map_neg, map_add, map_mul, ha0, ha1, hσσ]
  obtain ⟨x, hx⟩ := exists_twLevi_xm_pair hσσ (s := 1) (Or.inl rfl) c
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inl _) ?_ (x := x) ?_
  · rw [polar_single_inl_quadMinus, tailModelEquiv_inr_inl]
    rfl
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 2 c⟩ * ⟨_, xUnit_mem_d4Levi 3 (σ c)⟩)
      (by rw [hx, one_smul, one_smul, map_mul, e6IsogenyM_xm_single, e6IsogenyM_xm_single]; rfl),
      map_mul, d4Psi_xUnit, d4Psi_xUnit, simpleRoot_two, simpleRoot_three,
      rootElt_eps_sub_eps' (by decide), rootElt_eps_add_eps' (by decide),
      eichler_mul (by rw [polar_smul_right, polar_single_inl_quadPlus]; simp)
        (by rw [polar_smul_right, polar_single_inl_quadPlus]; simp),
      d4Iota_single_inl, d4Iota_tail, hσc, hc, neg_neg, neg_neg, add_comm]
    rfl

include hω in
theorem eichler_short_neg_mem (a : Fin 2 → descentField σ) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
      (Pi.single (Sum.inr (Sum.inl 2)) 1)
        (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) ∈ twCoverImage σ hσσ hω := by
  set c : F := (a 0 : F) + (a 1 : F) * ω with hc
  have ha0 : σ (a 0 : F) = a 0 := mem_descentField.1 (a 0).2
  have ha1 : σ (a 1 : F) = a 1 := mem_descentField.1 (a 1).2
  have hσc : σ c = (a 0 : F) + (a 1 : F) * σ ω := by
    rw [hc, map_add, map_mul, ha0, ha1]
  obtain ⟨x, hx⟩ := exists_twLevi_xm_pair hσσ (s := -1) (Or.inr rfl) c
  have hswap : ∀ (p : Fin 4 ⊕ Fin 4) (d : F), p ≠ Sum.inl 2 →
      eichler (quadPlus 4 F) (Pi.single p 1) ((-d) • Pi.single (Sum.inr 2) 1) =
        eichler (quadPlus 4 F) (Pi.single (Sum.inr 2) 1) (d • Pi.single p 1) := by
    intro p d hp
    rw [eichler_eq_eichler_neg_of_isotropic (quadPlus_single _)
      (by rw [QuadraticMap.map_smul, quadPlus_single, smul_zero])
      (by rw [polar_comm, polar_smul_left, polar_single_inr_quadPlus]; simp [Ne.symm hp]),
      eichler_smul_left, neg_smul_neg]
  refine eichler_mem_range_twCoverPhi hσσ hω (quadMinus_single_inr _) ?_ (x := x) ?_
  · rw [polar_single_inr_quadMinus, tailModelEquiv_inl]
    rfl
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 2 c⟩ * ⟨_, yUnit_mem_d4Levi 3 (σ c)⟩)
      (by rw [hx, neg_one_smul, neg_one_smul, map_mul, e6IsogenyM_xm_neg_single,
        e6IsogenyM_xm_neg_single]; rfl),
      map_mul, d4Psi_yUnit, d4Psi_yUnit, simpleRoot_two, simpleRoot_three, neg_sub,
      sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide),
      show -(eps 4 2 + eps 4 3 : Fin 4 → ℤ) = -eps 4 2 - eps 4 3 by abel,
      rootElt_neg_eps_sub_eps' (by decide), hswap _ _ (by decide), hswap _ _ (by decide),
      eichler_mul (by rw [polar_smul_right, polar_single_inr_quadPlus]; simp)
        (by rw [polar_smul_right, polar_single_inr_quadPlus]; simp),
      d4Iota_single_inr, d4Iota_tail, hσc]
    rfl

omit
  [Finite F] [CharP F 2] in
theorem minusTailIsometry_apply' (b c : descentField σ)
    (v : (Fin (4 - 1) ⊕ Fin (4 - 1) → descentField σ) × (Fin 2 → descentField σ)) :
    minusTailIsometry 4 (descentField σ) b c v =
      tailModelEquiv (4 - 1) (descentField σ) (Fin 2) v :=
  rfl

include hω in
theorem tailRootGroup_simple_le_comap (i : Fin (4 - 1)) :
    tailRootGroup (4 - 1) (minusTailForm (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (simpleRootB (4 - 1) i) ≤
      (twCoverImage σ hσσ hω).comap (LinearEquiv.autCongr (minusTailIsometry 4 (descentField σ)
        (d4MinusB hσσ ω) (d4MinusC hσσ ω)).toLinearEquiv).toMonoidHom := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
  intro g hg
  rcases hi with rfl | rfl | rfl
  · obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long (simpleRootB_mem_roots_of_lt (by decide))).1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, simpleRootB_of_lt (by decide),
      tailLongElt_eps_sub_eps (by decide), eichler_isometry, minusTailIsometry_apply',
      minusTailIsometry_apply', map_smul, tailModelEquiv_hypVec_inl, tailModelEquiv_hypVec_inr]
    exact eichler_long_zero_mem hσσ hω t
  · obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long (simpleRootB_mem_roots_of_lt (by decide))).1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, simpleRootB_of_lt (by decide),
      tailLongElt_eps_sub_eps (by decide), eichler_isometry, minusTailIsometry_apply',
      minusTailIsometry_apply', map_smul, tailModelEquiv_hypVec_inl, tailModelEquiv_hypVec_inr]
    exact eichler_long_one_mem hσσ hω t
  · rw [simpleRootB_of_not_lt (by decide)] at hg
    obtain ⟨a, rfl⟩ := mem_tailRootGroup_eps.1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, eichler_isometry,
      minusTailIsometry_apply', minusTailIsometry_apply', tailModelEquiv_hypVec_inl]
    exact eichler_short_mem hσσ hω a

include hω in
theorem tailRootGroup_neg_simple_le_comap (i : Fin (4 - 1)) :
    tailRootGroup (4 - 1) (minusTailForm (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (-simpleRootB (4 - 1) i) ≤
      (twCoverImage σ hσσ hω).comap (LinearEquiv.autCongr (minusTailIsometry 4 (descentField σ)
        (d4MinusB hσσ ω) (d4MinusC hσσ ω)).toLinearEquiv).toMonoidHom := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
  intro g hg
  rcases hi with rfl | rfl | rfl
  · obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long
      (neg_mem_roots (simpleRootB_mem_roots_of_lt (by decide)))).1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, simpleRootB_of_lt (by decide), neg_sub,
      sub_eq_neg_add, tailLongElt_neg_eps_add_eps (by decide), eichler_isometry,
      minusTailIsometry_apply', minusTailIsometry_apply', map_smul, tailModelEquiv_hypVec_inl,
      tailModelEquiv_hypVec_inr]
    exact eichler_long_zero_neg_mem hσσ hω t
  · obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long
      (neg_mem_roots (simpleRootB_mem_roots_of_lt (by decide)))).1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, simpleRootB_of_lt (by decide), neg_sub,
      sub_eq_neg_add, tailLongElt_neg_eps_add_eps (by decide), eichler_isometry,
      minusTailIsometry_apply', minusTailIsometry_apply', map_smul, tailModelEquiv_hypVec_inl,
      tailModelEquiv_hypVec_inr]
    exact eichler_long_one_neg_mem hσσ hω t
  · rw [simpleRootB_of_not_lt (by decide)] at hg
    obtain ⟨a, rfl⟩ := mem_tailRootGroup_neg_eps.1 hg
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, eichler_isometry,
      minusTailIsometry_apply', minusTailIsometry_apply', tailModelEquiv_hypVec_inr]
    exact eichler_short_neg_mem hσσ hω a

include hω in
theorem elementaryGroup_le_twCoverImage :
    elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) ≤
      twCoverImage σ hσσ hω := by
  have hJ := orthElementaryGroup_le_of_simpleRoots
    (anisotropic_minusTailForm (d4Minus_irr hσσ hω)) ⟨Pi.single 0 1, by simp⟩ (by norm_num)
    (tailRootGroup_simple_le_comap hσσ hω) (tailRootGroup_neg_simple_le_comap hσσ hω)
  rw [← elementaryGroup_map (minusTailIsometry 4 (descentField σ) (d4MinusB hσσ ω)
    (d4MinusC hσσ ω))]
  rintro _ ⟨g, hg, rfl⟩
  exact hJ hg

include hσσ hω in
theorem twCoverIsog_surjective : Function.Surjective (twCoverIsog F (σ : F →+* F)) := by
  intro t
  obtain ⟨y, ⟨x, rfl⟩, hy⟩ := elementaryGroup_le_twCoverImage hσσ hω (d4FixedEquiv hσσ hω t).2
  exact ⟨x, (d4FixedEquiv hσσ hω).injective (Subtype.ext hy)⟩

end Images

end CFSG.SeitzReduction.F4Pilot

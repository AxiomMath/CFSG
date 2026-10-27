module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedCoverImage

public section

namespace CFSG.SeitzReduction.F4Pilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer descentField
  mem_descentField mem_descentField_decomp)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup proj_single proj_neg_single
  rho_single rho_neg_single twistSign_single twistSign_neg_single
  mem_twistedRootGroup_iff_of_fixed mem_twistedRootGroup_iff_of_pair)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (rootElt rootElt_eps_sub_eps'
  rootElt_neg_eps_add_eps' rootElt_eps_add_eps' rootElt_neg_eps_sub_eps' eps)

section Images


variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

theorem twCoverPhi_long_zero {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {t : descentField σ}
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 0) 1) (t : F)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inl 0) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) := by
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inl _) ?_ _ ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 0 (t : F)⟩)
      (by rw [hx, e6IsogenyM_xm_single]), d4Psi_xUnit, simpleRoot_zero,
      rootElt_eps_sub_eps' (by decide), map_smul, d4Iota_single_inl, d4Iota_single_inr,
      Subfield.smul_def, Subfield.coe_neg]
    rfl

theorem twCoverPhi_long_zero_neg {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {t : descentField σ}
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 0) 1) (t : F)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inl 1) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 0)) 1) := by
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inl _) ?_ _ ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 0 (t : F)⟩)
      (by rw [hx, e6IsogenyM_xm_neg_single]), d4Psi_yUnit, simpleRoot_zero,
      neg_sub, sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide), map_smul, d4Iota_single_inl,
      d4Iota_single_inr, Subfield.smul_def, Subfield.coe_neg]
    rfl

theorem twCoverPhi_long_one {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {t : descentField σ}
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 1) 1) (t : F)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inl 1) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 2)) 1) := by
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inl _) ?_ _ ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 1 (t : F)⟩)
      (by rw [hx, e6IsogenyM_xm_single]), d4Psi_xUnit, simpleRoot_one,
      rootElt_eps_sub_eps' (by decide), map_smul, d4Iota_single_inl, d4Iota_single_inr,
      Subfield.smul_def, Subfield.coe_neg]
    rfl

theorem twCoverPhi_long_one_neg {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {t : descentField σ}
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 1) 1) (t : F)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inl 2) 1) ((-t) • Pi.single (Sum.inr (Sum.inl 1)) 1) := by
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inl _) ?_ _ ?_
  · rw [polar_smul_right, polar_single_inl_quadMinus]
    simp
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 1 (t : F)⟩)
      (by rw [hx, e6IsogenyM_xm_neg_single]), d4Psi_yUnit, simpleRoot_one,
      neg_sub, sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide), map_smul, d4Iota_single_inl,
      d4Iota_single_inr, Subfield.smul_def, Subfield.coe_neg]
    rfl

theorem twCoverPhi_short {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    (a : Fin 2 → descentField σ) {c : F} (hc : c = -((a 0 : F) + (a 1 : F) * σ ω))
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 2) 1) c * e6Data_valid.xm F (Pi.single (jD 3) 1) (σ c)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inl 2) 1) (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) := by
  have ha0 : σ (a 0 : F) = a 0 := mem_descentField.1 (a 0).2
  have ha1 : σ (a 1 : F) = a 1 := mem_descentField.1 (a 1).2
  have hσc : σ c = -((a 0 : F) + (a 1 : F) * ω) := by
    rw [hc, map_neg, map_add, map_mul, ha0, ha1, hσσ]
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inl _) ?_ _ ?_
  · rw [polar_single_inl_quadMinus, tailModelEquiv_inr_inl]
    rfl
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, xUnit_mem_d4Levi 2 c⟩ * ⟨_, xUnit_mem_d4Levi 3 (σ c)⟩)
      (by rw [hx, map_mul, e6IsogenyM_xm_single, e6IsogenyM_xm_single]; rfl),
      map_mul, d4Psi_xUnit, d4Psi_xUnit, simpleRoot_two, simpleRoot_three,
      rootElt_eps_sub_eps' (by decide), rootElt_eps_add_eps' (by decide),
      eichler_mul (by rw [polar_smul_right, polar_single_inl_quadPlus]; simp)
        (by rw [polar_smul_right, polar_single_inl_quadPlus]; simp),
      d4Iota_single_inl, d4Iota_tail, hσc, hc, neg_neg, neg_neg, add_comm]
    rfl

theorem twCoverPhi_short_neg {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    (a : Fin 2 → descentField σ) {c : F} (hc : c = (a 0 : F) + (a 1 : F) * ω)
    (hx : ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 2) 1) c *
        e6Data_valid.xm F (-Pi.single (jD 3) 1) (σ c)) :
    (twCoverPhi σ hσσ hω x).val =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))
        (Pi.single (Sum.inr (Sum.inl 2)) 1)
          (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) := by
  have ha0 : σ (a 0 : F) = a 0 := mem_descentField.1 (a 0).2
  have ha1 : σ (a 1 : F) = a 1 := mem_descentField.1 (a 1).2
  have hσc : σ c = (a 0 : F) + (a 1 : F) * σ ω := by
    rw [hc, map_add, map_mul, ha0, ha1]
  have hswap : ∀ (p : Fin 4 ⊕ Fin 4) (d : F), p ≠ Sum.inl 2 →
      eichler (quadPlus 4 F) (Pi.single p 1) ((-d) • Pi.single (Sum.inr 2) 1) =
        eichler (quadPlus 4 F) (Pi.single (Sum.inr 2) 1) (d • Pi.single p 1) := by
    intro p d hp
    rw [eichler_eq_eichler_neg_of_isotropic (quadPlus_single _)
      (by rw [QuadraticMap.map_smul, quadPlus_single, smul_zero])
      (by rw [polar_comm, polar_smul_left, polar_single_inr_quadPlus]; simp [Ne.symm hp]),
      eichler_smul_left, neg_smul_neg]
  rw [coe_twCoverPhi]
  refine d4DescentEquiv_eq_eichler hσσ hω (quadMinus_single_inr _) ?_ _ ?_
  · rw [polar_single_inr_quadMinus, tailModelEquiv_inl]
    rfl
  · rw [d4FixedPsi_twCoverIsog hσσ (h := ⟨_, yUnit_mem_d4Levi 2 c⟩ * ⟨_, yUnit_mem_d4Levi 3 (σ c)⟩)
      (by rw [hx, map_mul, e6IsogenyM_xm_neg_single, e6IsogenyM_xm_neg_single]; rfl),
      map_mul, d4Psi_yUnit, d4Psi_yUnit, simpleRoot_two, simpleRoot_three, neg_sub,
      sub_eq_neg_add, rootElt_neg_eps_add_eps' (by decide),
      show -(eps 4 2 + eps 4 3 : Fin 4 → ℤ) = -eps 4 2 - eps 4 3 by abel,
      rootElt_neg_eps_sub_eps' (by decide), hswap _ _ (by decide), hswap _ _ (by decide),
      eichler_mul (by rw [polar_smul_right, polar_single_inr_quadPlus]; simp)
        (by rw [polar_smul_right, polar_single_inr_quadPlus]; simp),
      d4Iota_single_inr, d4Iota_tail, hσc, hc]
    rfl

end Images

section Roots


variable {F : Type} [Field F] {σ : F ≃+* F}

local instance f4PilotGraphTwistedPiModelImagesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem exists_xm_of_mem_twistedRootGroup_zero {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (Pi.single 0 1)) :
    ∃ t : descentField σ, (g : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 0) 1) (t : F) := by
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed (σ : F →+* F)
    (isRoot_single .E6 (jD 0)) (by rw [proj_single]; rfl) (by rw [rho_single]; rfl) g).1 hg
  exact ⟨⟨c, mem_descentField.2 hc⟩, hgc⟩

theorem exists_xm_of_mem_twistedRootGroup_neg_zero {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (-Pi.single 0 1)) :
    ∃ t : descentField σ, (g : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 0) 1) (t : F) := by
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed (σ : F →+* F)
    (isRoot_neg_single .E6 (jD 0)) (by rw [proj_neg_single]; rfl) (by rw [rho_neg_single]; rfl)
      g).1 hg
  exact ⟨⟨c, mem_descentField.2 hc⟩, hgc⟩

theorem exists_xm_of_mem_twistedRootGroup_one {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (Pi.single 1 1)) :
    ∃ t : descentField σ, (g : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (Pi.single (jD 1) 1) (t : F) := by
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed (σ : F →+* F)
    (isRoot_single .E6 (jD 1)) (by rw [proj_single]; rfl) (by rw [rho_single]; rfl) g).1 hg
  exact ⟨⟨c, mem_descentField.2 hc⟩, hgc⟩

theorem exists_xm_of_mem_twistedRootGroup_neg_one {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (-Pi.single 1 1)) :
    ∃ t : descentField σ, (g : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-Pi.single (jD 1) 1) (t : F) := by
  obtain ⟨c, hc, hgc⟩ := (mem_twistedRootGroup_iff_of_fixed (σ : F →+* F)
    (isRoot_neg_single .E6 (jD 1)) (by rw [proj_neg_single]; rfl) (by rw [rho_neg_single]; rfl)
      g).1 hg
  exact ⟨⟨c, mem_descentField.2 hc⟩, hgc⟩

theorem exists_xm_of_mem_twistedRootGroup_two (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)
    {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (Pi.single 2 1)) :
    ∃ (a : Fin 2 → descentField σ) (c : F), c = -((a 0 : F) + (a 1 : F) * σ ω) ∧
      (g : e6Data_valid.minGroup F) =
        e6Data_valid.xm F (Pi.single (jD 2) 1) c *
          e6Data_valid.xm F (Pi.single (jD 3) 1) (σ c) := by
  have hne : CFSG.LieType.Steinberg.TwistedE6.rho (Pi.single (jD 2) 1) ≠ Pi.single (jD 2) 1 := by
    have := rho_smul_single_jD_two_ne (s := 1) (Or.inl rfl)
    rwa [one_smul] at this
  obtain ⟨c, hgc⟩ := (mem_twistedRootGroup_iff_of_pair (σ : F →+* F) (isRoot_single .E6 (jD 2))
    (by rw [proj_single]; rfl) hne g).1 hg
  rw [rho_single, twistSign_single, Int.cast_one, one_mul] at hgc
  have hne' : σ (σ ω) ≠ σ ω := by
    rw [hσσ]
    exact Ne.symm hω
  obtain ⟨h1, h2⟩ := mem_descentField_decomp hσσ hne' (-c)
  refine ⟨![⟨-c - σ ω * ((σ ω - σ (σ ω))⁻¹ * (-c - σ (-c))), h2⟩,
    ⟨(σ ω - σ (σ ω))⁻¹ * (-c - σ (-c)), h1⟩], c, ?_, hgc⟩
  show c = -((-c - σ ω * ((σ ω - σ (σ ω))⁻¹ * (-c - σ (-c)))) +
    (σ ω - σ (σ ω))⁻¹ * (-c - σ (-c)) * σ ω)
  ring

theorem exists_xm_of_mem_twistedRootGroup_neg_two (hσσ : ∀ c, σ (σ c) = c) {ω : F}
    (hω : σ ω ≠ ω) {g : fixedGroup F (σ : F →+* F)}
    (hg : g ∈ twistedRootGroup F (σ : F →+* F) (-Pi.single 2 1)) :
    ∃ (a : Fin 2 → descentField σ) (c : F), c = (a 0 : F) + (a 1 : F) * ω ∧
      (g : e6Data_valid.minGroup F) =
        e6Data_valid.xm F (-Pi.single (jD 2) 1) c *
          e6Data_valid.xm F (-Pi.single (jD 3) 1) (σ c) := by
  have hne : CFSG.LieType.Steinberg.TwistedE6.rho (-Pi.single (jD 2) 1) ≠ -Pi.single (jD 2) 1 := by
    have := rho_smul_single_jD_two_ne (s := -1) (Or.inr rfl)
    rwa [neg_one_smul] at this
  obtain ⟨c, hgc⟩ := (mem_twistedRootGroup_iff_of_pair (σ : F →+* F)
    (isRoot_neg_single .E6 (jD 2)) (by rw [proj_neg_single]; rfl) hne g).1 hg
  rw [rho_neg_single, twistSign_neg_single, Int.cast_one, one_mul] at hgc
  obtain ⟨h1, h2⟩ := mem_descentField_decomp hσσ hω c
  refine ⟨![⟨c - ω * ((ω - σ ω)⁻¹ * (c - σ c)), h2⟩, ⟨(ω - σ ω)⁻¹ * (c - σ c), h1⟩], c, ?_, hgc⟩
  show c = (c - ω * ((ω - σ ω)⁻¹ * (c - σ c))) + (ω - σ ω)⁻¹ * (c - σ c) * ω
  ring

end Roots

end CFSG.SeitzReduction.F4Pilot

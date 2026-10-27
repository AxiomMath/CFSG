module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiAdd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphHighestRoot

open Psi

variable {K : Type} [Field K]

theorem Psi.diagramMap_apply_labelPerm (y : RootModule TwistTag.E6.tag K)
    (b : Label TwistTag.E6.tag) :
    (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) y
      (labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm b) = y b := by
  simp [diagramMap, Finsupp.domLCongr_apply, Finsupp.equivMapDomain_apply]

theorem Psi.permLattice_sub_aux (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (v - w) =
      permLattice TwistTag.E6.perm v - permLattice TwistTag.E6.perm w := rfl

theorem Psi.permLattice_neg_aux (v : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (-v) = -permLattice TwistTag.E6.perm v := rfl

theorem Psi.labelPerm_lab (γ : Dr) :
    labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm (lab γ) = lab (rhoD γ) := by
  simp only [lab, labelPerm, rhoD, Equiv.coe_fn_mk, Sum.inr.injEq, Subtype.mk.injEq]
  rw [permLattice_sub_aux, permLattice_e6HighestRoot]

theorem Psi.psi_apply_rhoD (σ : K →+* K) {z : ModGL TwistTag.E6.tag K}
    (hz : twistHom TwistTag.E6 K σ z = z) (γ : Dr) :
    psi K z (rhoD γ) = σ (psi K z γ) := by
  have hPv0 : (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
      (v0 K) = v0 K := by
    unfold v0
    rw [diagramMap_rootVec _ _ _ isRoot_neg_highest, permLattice_neg_aux, permLattice_e6HighestRoot]
  have hPinv : (((diagramMap TwistTag.E6 K)⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) = v0 K := by
    have h := congrArg (fun x => (((diagramMap TwistTag.E6 K)⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) x) hPv0
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply] at h
    exact h.symm
  have hmr : Finsupp.mapRange σ σ.map_zero (v0 K) = v0 K := by
    rw [v0_eq]
    simp
  have h1 : (z : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) =
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
        (entrywise σ (z : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K)) := by
    have := congrArg (fun g : ModGL TwistTag.E6.tag K =>
      (g : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K)) hz.symm
    simp only [coe_twistHom, Module.End.mul_apply, hPinv] at this
    exact this
  have h2 : entrywise σ (z : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K) =
      Finsupp.mapRange σ σ.map_zero ((z : Module.End K (RootModule TwistTag.E6.tag K)) (v0 K)) := by
    conv_lhs => rw [← hmr]
    exact entrywise_apply_mapRange σ _ _
  rw [h2] at h1
  have h3 := DFunLike.congr_fun h1 (lab (rhoD γ))
  have h4 : ∀ y : RootModule TwistTag.E6.tag K,
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) y
        (lab (rhoD γ)) = y (lab γ) := fun y => by
    rw [← labelPerm_lab]
    exact diagramMap_apply_labelPerm y (lab γ)
  rw [h4, Finsupp.mapRange_apply] at h3
  exact h3

theorem psi_mem_RPhi_of_mem_twistedFixedGroup
    (σ : K ≃+* K) {z : ModGL TwistTag.E6.tag K}
    (hzF : z ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom) : psi K z ∈ RPhi K σ :=
  fun γ => psi_apply_rhoD σ.toRingHom ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hzF).2 γ

theorem psi_mem_RPhi
    (σ : K ≃+* K) {z : ModGL TwistTag.E6.tag K} (_hz : z ∈ Qbar K)
    (hzF : z ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom) : psi K z ∈ RPhi K σ :=
  psi_mem_RPhi_of_mem_twistedFixedGroup σ hzF

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

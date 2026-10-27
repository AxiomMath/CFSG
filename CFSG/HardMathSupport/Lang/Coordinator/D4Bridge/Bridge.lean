module

public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Kernel
public import CFSG.HardMathSupport.Lang.D4Three.BridgeRange
public import CFSG.HardMathSupport.Lang.Proving.StatedProjQuadPlus
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.TauCetiBridge.Twisted CFSG.TauCetiBridge.Minuscule CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank TauCeti

variable (F : Type) [Field F]

section Theta


@[expose] def blockRepE : d4tData_valid.minGroup F →* elementaryGroup (quadPlus 4 F) :=
  (blockRep F).codRestrict _ fun g => by
    rw [← CFSG.HardMathSupport.Lang.D4Three.range_blockRep F]
    exact ⟨g, rfl⟩

theorem coe_blockRepE (g : d4tData_valid.minGroup F) :
    (blockRepE F g : V F ≃ₗ[F] V F) = blockRep F g :=
  rfl

theorem blockRepE_surjective : Function.Surjective (blockRepE F) := by
  rintro ⟨e, he⟩
  rw [← CFSG.HardMathSupport.Lang.D4Three.range_blockRep F] at he
  obtain ⟨g, rfl⟩ := he
  exact ⟨g, rfl⟩


@[expose] def adjRep : d4tData_valid.minGroup F →* adjointGroup Tag.D4 F :=
  (adMin d4tData_valid posDef_cartan_D4 d4tSigns_check F).codRestrict _ fun g => by
    rw [← range_adMin d4tData_valid posDef_cartan_D4 d4tSigns_check F]
    exact ⟨g, rfl⟩

theorem adjRep_surjective : Function.Surjective (adjRep F) := by
  rintro ⟨c, hc⟩
  rw [← range_adMin d4tData_valid posDef_cartan_D4 d4tSigns_check F] at hc
  obtain ⟨g, rfl⟩ := hc
  exact ⟨g, rfl⟩

theorem ker_blockRepE_le : (blockRepE F).ker ≤ (adjRep F).ker := fun g hg => by
  rw [MonoidHom.mem_ker] at hg ⊢
  have h1 : blockRep F g = 1 := by
    rw [← coe_blockRepE, hg]
    rfl
  exact Subtype.ext (adMin_eq_one_of_blockRep_eq_one h1)

@[expose] def theta : elementaryGroup (quadPlus 4 F) →* adjointGroup Tag.D4 F :=
  (QuotientGroup.lift (blockRepE F).ker (adjRep F) (ker_blockRepE_le F)).comp
    (QuotientGroup.quotientKerEquivOfSurjective (blockRepE F)
      (blockRepE_surjective F)).symm.toMonoidHom

theorem theta_blockRepE (g : d4tData_valid.minGroup F) :
    theta F (blockRepE F g) = adjRep F g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (blockRepE F) (blockRepE_surjective F)).symm
      (blockRepE F g) = (g : d4tData_valid.minGroup F ⧸ (blockRepE F).ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  rw [theta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]

theorem theta_surjective : Function.Surjective (theta F) := fun c => by
  obtain ⟨g, rfl⟩ := adjRep_surjective F c
  exact ⟨blockRepE F g, theta_blockRepE F g⟩

@[expose] def omegaEquiv : StatedOmega (StatedQuadPlus 4 F) ≃* elementaryGroup (quadPlus 4 F) :=
  statedOmegaEquiv (coe_quadPlus 4 F) (commutator_orthogonalGroup_quadPlus (by norm_num))

@[expose] def thetaOmega : StatedOmega (StatedQuadPlus 4 F) →* adjointGroup Tag.D4 F :=
  (theta F).comp (omegaEquiv F).toMonoidHom

theorem thetaOmega_surjective : Function.Surjective (thetaOmega F) :=
  (theta_surjective F).comp (omegaEquiv F).surjective

theorem exists_ne_one_adjointGroup_D4 : ∃ c : adjointGroup Tag.D4 F, c ≠ 1 :=
  ⟨⟨xUnit Tag.D4 F ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ _⟩, fun h => by
    have h' : xOp Tag.D4 F ⟨0, by decide⟩ 1 = xOp Tag.D4 F ⟨0, by decide⟩ 0 := by
      rw [xOp_zero]
      exact congrArg (fun g : adjointGroup Tag.D4 F =>
        ((g : ModGL Tag.D4 F) : Module.End F (RootModule Tag.D4 F))) h
    exact one_ne_zero (xOp_injective _ h')⟩

theorem nonempty_statedProj_equiv_adjointGroup [Finite F] :
    Nonempty (StatedProj (StatedOmega (StatedQuadPlus 4 F)) ≃* adjointGroup Tag.D4 F) := by
  obtain ⟨c, hc⟩ := exists_ne_one_adjointGroup_D4 F
  obtain ⟨x, rfl⟩ := thetaOmega_surjective F c
  exact CFSG.HardMathSupport.Lang.Proving.nonempty_statedProj_statedOmega_quadPlus_equiv
    (by norm_num) CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (thetaOmega F)
    (thetaOmega_surjective F) ⟨x, hc⟩

end Theta


theorem nonempty_adjointQuotient_D4_equiv (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid)
    [Finite F] (hF : Nat.card F = q.card) :
    Nonempty (AdjointQuotient Tag.D4 F ≃* ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hL : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = q.card := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]
  have := Fintype.ofFinite F
  have := Fintype.ofFinite ↥(ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  have hcard : Fintype.card F = Fintype.card ↥(ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hL]
  obtain ⟨e⟩ := nonempty_statedProj_equiv_adjointGroup ↥(ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
  exact ⟨(CFSG.TauCetiBridge.adjointQuotientCongr (FiniteField.ringEquivOfCardEq hcard)).trans
    (((QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).trans
      (e.symm.trans
        (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q
          hv).symm))⟩

end CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

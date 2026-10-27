module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionComponentsTransfer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

variable {X : Type*} [Group X]

@[expose] def restrictAutomorphism (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) : MulAut N :=
  (ψ.subgroupMap N).trans (MulEquiv.subgroupCongr hN)

theorem restrictAutomorphism_apply (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (x : N) :
    (restrictAutomorphism N ψ hN x).val = ψ x.val := rfl

theorem restrictAutomorphism_symm_apply (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (x : N) :
    ((restrictAutomorphism N ψ hN).symm x).val = ψ.symm x.val := by
  apply ψ.injective
  rw [ψ.apply_symm_apply]
  exact congrArg Subtype.val ((restrictAutomorphism N ψ hN).apply_symm_apply x)

@[expose] def fixedNormalEquiv (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) :
    FixedCommutingProduct.fixedSubgroup (restrictAutomorphism N ψ hN) ≃*
      N.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ) where
  toFun x := ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fixedNormalEquiv_apply (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N)
    (x : FixedCommutingProduct.fixedSubgroup (restrictAutomorphism N ψ hN)) :
    (fixedNormalEquiv N ψ hN x).val.val = x.val.val := rfl

theorem fixedNormalEquiv_symm_apply (N : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N)
    (x : N.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ)) :
    ((fixedNormalEquiv N ψ hN).symm x).val.val = x.val.val := rfl

theorem central_subgroupOf (N Z : Subgroup X) (hZ : Z ≤ Subgroup.center X) :
    Z.subgroupOf N ≤ Subgroup.center N := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro n
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hZ hz) n.val

theorem restricted_central_invariant (N Z : Subgroup X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z) :
    (Z.subgroupOf N).map (restrictAutomorphism N ψ hN).toMonoidHom = Z.subgroupOf N := by
  have hZinv : Z.map ψ.symm.toMonoidHom = Z :=
    (Subgroup.map_symm_eq_iff_map_eq (K := Z) (e := ψ)).mpr hZ
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ψ y.val ∈ Z
    rw [← hZ]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom hy
  · intro hx
    refine ⟨(restrictAutomorphism N ψ hN).symm x, ?_, by simp⟩
    change ((restrictAutomorphism N ψ hN).symm x).val ∈ Z
    rw [restrictAutomorphism_symm_apply, ← hZinv]
    exact Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hx

variable [Finite X]

theorem normal_subgroup_pComponent_quasisimple (N : Subgroup X) [N.Normal]
    (p : ℕ) [Fact p.Prime]
    (hX : ∀ L : Subgroup X, CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup N) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have himage := CatalogueBAlternating.pComponent_of_normal_subgroup p N L hL
  have hquasi := hX (L.map N.subtype) himage
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective N.subtype N.subtype_injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem normal_fixed_pComponent_quasisimple (N : Subgroup X) [N.Normal]
    (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N) (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup (restrictAutomorphism N ψ hN)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (fixedNormalEquiv N ψ hN)
    (normal_subgroup_pComponent_quasisimple
      (N.subgroupOf (FixedCommutingProduct.fixedSubgroup ψ)) p hfixed) L hL

@[expose] def onNormalCentralQuotient (N Z : Subgroup X) [Z.Normal]
    (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z) :
    MulAut (N ⧸ Z.subgroupOf N) :=
  CatalogueBFixedCentralQuotient.onQuotient (Z.subgroupOf N)
    (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ)

omit [Finite X] in
theorem onNormalCentralQuotient_mk (N Z : Subgroup X) [Z.Normal]
    (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    (x : N) :
    onNormalCentralQuotient N Z ψ hN hZ ((QuotientGroup.mk' (Z.subgroupOf N)) x) =
      (QuotientGroup.mk' (Z.subgroupOf N)) (restrictAutomorphism N ψ hN x) :=
  CatalogueBFixedCentralQuotient.onQuotient_mk _ _ _ x

theorem normal_central_quotient_fixed_pComponent_quasisimple
    (N Z : Subgroup X) [N.Normal] [Z.Normal] (hcentral : Z ≤ Subgroup.center X)
    (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    (p : ℕ) [Fact p.Prime]
    (hfixed : ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (onNormalCentralQuotient N Z ψ hN hZ)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.quotientFixed_pComponent_quasisimple
    (Z.subgroupOf N) (central_subgroupOf N Z hcentral)
    (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ) p
    (normal_fixed_pComponent_quasisimple N ψ hN p hfixed) L hL

theorem normal_central_quotient_fixed_p_component_transfer
    (N Z : Subgroup X) [N.Normal] (hcentral : Z ≤ Subgroup.center X)
    (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z) :
    letI := Subgroup.normal_of_le_center hcentral
    ∀ p : ℕ, p.Prime →
      (∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L) →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup
        (onNormalCentralQuotient N Z ψ hN hZ)),
        CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  let := Subgroup.normal_of_le_center hcentral
  intro p hp hfixed L hL
  let : Fact p.Prime := ⟨hp⟩
  exact normal_central_quotient_fixed_pComponent_quasisimple
    N Z hcentral ψ hN hZ p hfixed L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

module

public import CFSG.ClassicalInvolution.Balance.ToralBalance
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientAlgebra
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

section Transfer

@[expose] def InvolutionFixedB (M : Type*) [Group M] : Prop :=
  ∀ α : MulAut M, Function.Involutive α →
    ∀ T : Subgroup (fixedSubgroup α), TwoComponents.IsTwoComponent T → CFSG.Open.IsQuasisimple T

theorem InvolutionFixedB.of_mulEquiv {M N : Type*} [Group M] [Finite M] [Group N] [Finite N]
    (e : M ≃* N) (h : InvolutionFixedB N) : InvolutionFixedB M := by
  intro α hα T hT
  let β : MulAut N := MulAut.congr e α
  have hβ : Function.Involutive β := fun y => by
    change e (α (e.symm (e (α (e.symm y))))) = y
    rw [e.symm_apply_apply, hα, e.apply_symm_apply]
  let f : fixedSubgroup α ≃* fixedSubgroup β :=
    CatalogueRelativeB.fixedSubgroupEquivalence e α
  have h1 : TwoComponents.IsTwoComponent (T.map f.toMonoidHom) :=
    (TwoComponentTransport.equiv_iff f T).mpr hT
  exact Components.quasisimple_of_equiv (T.equivMapOfInjective f.toMonoidHom f.injective)
    (h β hβ _ h1)

variable {L : Type*} [Group L] [Finite L]

theorem isQuasisimple_of_quotient (Z : Subgroup L) [Z.Normal] (hcentral : Z ≤ Subgroup.center L)
    (ψ : MulAut L) (hinvariant : Z.map ψ.toMonoidHom = Z)
    (hquot : ∀ T : Subgroup (fixedSubgroup (onQuotient Z ψ hinvariant)),
      TwoComponents.IsTwoComponent T → CFSG.Open.IsQuasisimple T)
    (T : Subgroup (fixedSubgroup ψ)) (hT : TwoComponents.IsTwoComponent T) :
    CFSG.Open.IsQuasisimple T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := fixedImage_normal Z ψ hinvariant hcentral
  have hsurj := fixedImageProjection_surjective Z ψ hinvariant
  have hker := fixedImageProjection_kernel_central Z ψ hinvariant hcentral
  have hTp : CFSG.IsPComponent 2 T := (CatalogueBAlternating.pComponent_two_iff T).mpr hT
  have h1 := CatalogueBCentralQuotient.pComponent_map 2 (fixedImageProjection Z ψ hinvariant)
    hsurj hker T hTp
  have h2 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 (fixedImage Z ψ hinvariant) _ h1
  have h3 := hquot _ ((CatalogueBAlternating.pComponent_two_iff _).mp h2)
  have h4 : CFSG.Open.IsQuasisimple (T.map (fixedImageProjection Z ψ hinvariant)) :=
    Components.quasisimple_of_equiv
      ((T.map (fixedImageProjection Z ψ hinvariant)).equivMapOfInjective
        (fixedImage Z ψ hinvariant).subtype (fixedImage Z ψ hinvariant).subtype_injective) h3
  have h5 := ((CatalogueBCentralQuotient.central_quotient_p_component_bijection 2 Nat.prime_two
    (fixedImageProjection Z ψ hinvariant) hsurj hker).2.1 T hTp).2.2
  exact CatalogueBAlternating.quasisimple_iff_native.mp
    (h5.mpr (CatalogueBAlternating.quasisimple_iff_native.mpr h4))

end Transfer

section Conjugation

variable {X : Type*} [Group X]

@[expose] def conjOn (L : Subgroup X) (f : X) (hf : f ∈ Subgroup.normalizer (L : Set X)) :
    MulAut ↥L where
  toFun l := ⟨f * l * f⁻¹, (Subgroup.mem_normalizer_iff.mp hf l).mp l.2⟩
  invFun l := ⟨f⁻¹ * l * f, (Subgroup.mem_normalizer_iff.mp hf _).mpr (by simp [mul_assoc])⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (L : Subgroup X) (f : X) (hf : f ∈ Subgroup.normalizer (L : Set X))
    (l : ↥L) : ((conjOn L f hf l : ↥L) : X) = f * l * f⁻¹ := rfl

@[expose] def centralizerEquivFixed (L : Subgroup X) (f : X)
    (hf : f ∈ Subgroup.normalizer (L : Set X)) :
    ↥(L ⊓ Subgroup.centralizer ({f} : Set X)) ≃* fixedSubgroup (conjOn L f hf) where
  toFun x := ⟨⟨x.1, x.2.1⟩, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    refine Subtype.ext ?_
    change f * (x : X) * f⁻¹ = x
    rw [← h, mul_inv_cancel_right]⟩
  invFun y := ⟨y.1.1, y.1.2, by
    have h : f * (y.1 : X) * f⁻¹ = y.1 := congrArg Subtype.val y.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (y.1 : X) * f = f * (y.1 : X) * f⁻¹ * f := by rw [h]
      _ = f * (y.1 : X) := by group⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext (Subtype.ext rfl)
  map_mul' x y := Subtype.ext (Subtype.ext rfl)

end Conjugation

section Involutions

variable {X : Type*} [Group X] [Finite X]

theorem involutionCentralizerB_of_involutionFixedB {L : Subgroup X}
    (hL : InvolutionFixedB (↥L ⧸ Subgroup.center ↥L)) : InvolutionCentralizerB L := by
  intro f hf1 hf2 hfn M hM
  let ψ : MulAut ↥L := conjOn L f hfn
  have hψ : Function.Involutive ψ := fun l => Subtype.ext (by
    change f * (f * (l : X) * f⁻¹) * f⁻¹ = l
    calc f * (f * (l : X) * f⁻¹) * f⁻¹ = (f * f) * (l : X) * (f * f)⁻¹ := by group
      _ = l := by rw [hf2]; group)
  have hinv : (Subgroup.center ↥L).map ψ.toMonoidHom = Subgroup.center ↥L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance ψ
  have hψ' : Function.Involutive (onQuotient (Subgroup.center ↥L) ψ hinv) := fun q => by
    induction q using QuotientGroup.induction_on with
    | H x =>
      change onQuotient _ ψ hinv (onQuotient _ ψ hinv (QuotientGroup.mk' _ x)) =
        QuotientGroup.mk' _ x
      rw [onQuotient_mk, onQuotient_mk, hψ x]
  have hfix := isQuasisimple_of_quotient (Subgroup.center ↥L) le_rfl ψ hinv (hL _ hψ')
  let e := centralizerEquivFixed L f hfn
  have h1 : TwoComponents.IsTwoComponent (M.map e.toMonoidHom) :=
    (TwoComponentTransport.equiv_iff e M).mpr hM
  exact Components.quasisimple_of_equiv (M.equivMapOfInjective e.toMonoidHom e.injective)
    (hfix _ h1)

end Involutions

end CFSG.ClassicalInvolution.Balance

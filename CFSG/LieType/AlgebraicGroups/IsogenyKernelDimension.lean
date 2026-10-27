module
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Augmentation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Composite
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness

public noncomputable section
open CategoryTheory
namespace CFSG.LieType.AlgebraicGroups.Isogeny
universe u
variable {k : Type u} [Field k]
variable {D S X : _root_.CommHopfAlgCat.{u} k}

abbrev kernelDimension (q : D ⟶ S) : ℕ :=
  Module.finrank k (S ⧸ (TauCeti.CommHopfAlgCat.kernelHopfIdeal q).toIdeal)

theorem finite_kernelCompositeMap
    (q : D ⟶ S) (f : S ⟶ X)
    (hf : TauCeti.CommHopfAlgCat.IsIsogeny f) :
    (TauCeti.CommHopfAlgCat.kernelCompositeMap q f).hom.toAlgHom.Finite := by
  let g := TauCeti.CommHopfAlgCat.kernelCompositeMap q f
  have hff := TauCeti.CommHopfAlgCat.faithfullyFlat_kernelCompositeMap q f hf.faithfullyFlat
  apply (TauCeti.CommHopfAlgCat.finite_iff_moduleFinite_quotient_kernelHopfIdeal g hff).2
  let e := TauCeti.CommHopfAlgCat.kernelCompositeKernelIso q f
  let : Module.Finite k (X ⧸ (TauCeti.CommHopfAlgCat.kernelHopfIdeal f).toIdeal) :=
    TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hf.finite
  exact Module.Finite.equiv (_root_.CommHopfAlgCat.ofIso e).toAlgEquiv.symm.toLinearEquiv

theorem isIso_of_kernelDimension_le
    (q : D ⟶ S) (hq : TauCeti.CommHopfAlgCat.IsIsogeny q)
    (f : S ⟶ X) (hf : TauCeti.CommHopfAlgCat.IsIsogeny f)
    (hdeg : kernelDimension (q ≫ f) ≤ kernelDimension q) : IsIso f := by
  let K := TauCeti.CommHopfAlgCat.quotient S (TauCeti.CommHopfAlgCat.kernelHopfIdeal q)
  let L := TauCeti.CommHopfAlgCat.quotient X (TauCeti.CommHopfAlgCat.kernelHopfIdeal (q ≫ f))
  let g : K ⟶ L := TauCeti.CommHopfAlgCat.kernelCompositeMap q f
  have hg : TauCeti.CommHopfAlgCat.IsIsogeny g := by
    apply (TauCeti.CommHopfAlgCat.isIsogeny_iff _).2
    exact ⟨finite_kernelCompositeMap q f hf,
      TauCeti.CommHopfAlgCat.faithfullyFlat_kernelCompositeMap q f hf.faithfullyFlat⟩
  let : Module.Finite k K := TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hq.finite
  let : Module.Finite k L := TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal (hq.comp hf).finite
  have hdim : Module.finrank k K = Module.finrank k L := by
    apply le_antisymm
    · exact LinearMap.finrank_le_finrank_of_injective (f := g.hom.toLinearMap) hg.injective
    · exact hdeg
  have hgs : Function.Surjective g.hom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hg.injective
  have hker : TauCeti.CommHopfAlgCat.kernelHopfIdeal g = TauCeti.HopfIdeal.augmentation k L :=
    TauCeti.CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective g hgs
  let e := TauCeti.CommHopfAlgCat.kernelCompositeKernelIso q f
  have hKdim : Module.finrank k (TauCeti.CommHopfAlgCat.quotient X
      (TauCeti.CommHopfAlgCat.kernelHopfIdeal f)) = 1 := by
    have he := (_root_.CommHopfAlgCat.ofIso e).toAlgEquiv.toLinearEquiv.finrank_eq
    rw [hker] at he
    have haug := TauCeti.HopfIdeal.quotientAugmentationIso (TauCeti.FiniteTypeCommHopfAlgCat.of k L)
    have ha := (_root_.CommHopfAlgCat.ofIso (CategoryTheory.Functor.mapIso (forget₂ (TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (_root_.CommHopfAlgCat.{u} k)) haug)).toAlgEquiv.toLinearEquiv.finrank_eq
    exact he.symm.trans (ha.trans (Module.finrank_self k))
  let F := TauCeti.CommHopfAlgCat.quotient X (TauCeti.CommHopfAlgCat.kernelHopfIdeal f)
  let : Module.Finite k F :=
    TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hf.finite
  let c := Bialgebra.counitAlgHom k F
  have hcs : Function.Surjective c.toLinearMap := by
    intro a
    exact ⟨algebraMap k F a, c.commutes a⟩
  have hci : Function.Injective c :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hKdim.trans (Module.finrank_self k).symm)).2 hcs
  have hkill : TauCeti.CommHopfAlgCat.kernelHopfIdeal f = TauCeti.HopfIdeal.augmentation k X := by
    apply le_antisymm (TauCeti.HopfIdeal.le_augmentation _ _ _)
    intro a ha
    apply (Ideal.Quotient.eq_zero_iff_mem).1
    apply hci
    have he := CoalgHomClass.counit_comp_apply
      (TauCeti.CommHopfAlgCat.mkQuotient X (TauCeti.CommHopfAlgCat.kernelHopfIdeal f)).hom a
    exact (he.trans ((TauCeti.HopfIdeal.mem_augmentation _ _).1 ha)).trans c.map_zero.symm
  exact hf.isIso_iff_kernelHopfIdeal_eq_augmentation.2 hkill

end CFSG.LieType.AlgebraicGroups.Isogeny

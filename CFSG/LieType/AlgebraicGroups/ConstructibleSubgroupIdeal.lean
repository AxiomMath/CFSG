module

public import CFSG.LieType.AlgebraicGroups.ZariskiPoints
public import CFSG.LieType.AlgebraicGroups.InnerTwistDifferential
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TensorProduct WithConv

open scoped CFSG.ConvolutionPoints

section Points

variable {k : Type} [Field k] {A : Type} [CommRing A] [Algebra k A]

@[expose] def pointsIdeal (S : Set (A →ₐ[k] k)) : Ideal A :=
  PrimeSpectrum.vanishingIdeal (pointSpec '' S)

theorem mem_pointsIdeal {S : Set (A →ₐ[k] k)} {a : A} :
    a ∈ pointsIdeal S ↔ ∀ y ∈ S, y a = 0 := by
  rw [pointsIdeal, PrimeSpectrum.mem_vanishingIdeal, Set.forall_mem_image]
  simp only [pointSpec_asIdeal, RingHom.mem_ker]

theorem isRadical_pointsIdeal (S : Set (A →ₐ[k] k)) : (pointsIdeal S).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

variable (k) in
@[expose] def pointsZero (I : Ideal A) : Set (A →ₐ[k] k) :=
  {y | ∀ a ∈ I, y a = 0}

theorem mem_pointsZero {I : Ideal A} {y : A →ₐ[k] k} : y ∈ pointsZero k I ↔ ∀ a ∈ I, y a = 0 :=
  Iff.rfl

theorem pointSpec_mem_zeroLocus {I : Ideal A} {y : A →ₐ[k] k} :
    pointSpec y ∈ PrimeSpectrum.zeroLocus (I : Set A) ↔ y ∈ pointsZero k I := by
  rw [PrimeSpectrum.mem_zeroLocus, pointSpec_asIdeal]
  exact ⟨fun h a ha => h ha, fun h a ha => h a ha⟩

theorem subset_pointsZero_pointsIdeal (S : Set (A →ₐ[k] k)) : S ⊆ pointsZero k (pointsIdeal S) :=
  fun y hy _ ha => mem_pointsIdeal.1 ha y hy

theorem pointsZero_pointsIdeal (S : Set (A →ₐ[k] k)) :
    pointsZero k (pointsIdeal S) = pointSpec ⁻¹' closure (pointSpec '' S) := by
  ext y
  rw [Set.mem_preimage, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, ← pointsIdeal,
    pointSpec_mem_zeroLocus]

end Points

section Hopf

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

abbrev subgroupPoints (H : Subgroup (WithConv (A →ₐ[k] k))) : Set (A →ₐ[k] k) :=
  toConv ⁻¹' (H : Set (WithConv (A →ₐ[k] k)))

abbrev subgroupIdeal (H : Subgroup (WithConv (A →ₐ[k] k))) : Ideal A :=
  pointsIdeal (subgroupPoints H)

theorem mem_subgroupIdeal {H : Subgroup (WithConv (A →ₐ[k] k))} {a : A} :
    a ∈ subgroupIdeal H ↔ ∀ y ∈ H, y.ofConv a = 0 :=
  mem_pointsIdeal.trans ⟨fun h y hy => h y.ofConv hy, fun h y hy => h (toConv y) hy⟩

theorem antipode_mem_subgroupIdeal (H : Subgroup (WithConv (A →ₐ[k] k))) {a : A}
    (ha : a ∈ subgroupIdeal H) : HopfAlgebra.antipode k a ∈ subgroupIdeal H :=
  mem_subgroupIdeal.2 fun y hy => mem_subgroupIdeal.1 ha y⁻¹ (H.inv_mem hy)

theorem comp_mem_pointsZero {I : Ideal A} {φ : A →ₐ[k] A} (hφ : ∀ a ∈ I, φ a ∈ I)
    {y : A →ₐ[k] k} (hy : y ∈ pointsZero k I) : y.comp φ ∈ pointsZero k I :=
  fun a ha => hy (φ a) (hφ a ha)

theorem inv_mem_pointsZero_subgroupIdeal (H : Subgroup (WithConv (A →ₐ[k] k)))
    {y : WithConv (A →ₐ[k] k)} (hy : y.ofConv ∈ pointsZero k (subgroupIdeal H)) :
    y⁻¹.ofConv ∈ pointsZero k (subgroupIdeal H) :=
  comp_mem_pointsZero (φ := HopfAlgebra.antipodeAlgHom k A)
    (fun _ ha => antipode_mem_subgroupIdeal H ha) hy

theorem mul_mem_pointsZero_subgroupIdeal (H : Subgroup (WithConv (A →ₐ[k] k)))
    {y z : WithConv (A →ₐ[k] k)}
    (hz : ∀ g ∈ H, (g * z).ofConv ∈ pointsZero k (subgroupIdeal H))
    (hy : y.ofConv ∈ pointsZero k (subgroupIdeal H)) :
    (y * z).ofConv ∈ pointsZero k (subgroupIdeal H) := by
  intro a ha
  have hmem : rightTransCo z a ∈ subgroupIdeal H := mem_subgroupIdeal.2 fun g hg => by
    have h := congrArg (fun p : WithConv (A →ₐ[k] k) => p.ofConv a) (point_comp_rightTransCo z g)
    simp only [AlgHom.comp_apply] at h
    rw [h]
    exact hz g hg a ha
  have h := congrArg (fun p : WithConv (A →ₐ[k] k) => p.ofConv a) (point_comp_rightTransCo z y)
  simp only [AlgHom.comp_apply] at h
  rw [← h]
  exact hy _ hmem

@[expose] def closureSubgroup (H : Subgroup (WithConv (A →ₐ[k] k))) :
    Subgroup (WithConv (A →ₐ[k] k)) where
  carrier := ofConv ⁻¹' pointsZero k (subgroupIdeal H)
  one_mem' := subset_pointsZero_pointsIdeal _
    (show toConv (1 : WithConv (A →ₐ[k] k)).ofConv ∈ H from H.one_mem)
  inv_mem' := inv_mem_pointsZero_subgroupIdeal H
  mul_mem' {y z} hy hz := by
    have hHz : ∀ g ∈ H, (g * z).ofConv ∈ pointsZero k (subgroupIdeal H) := by
      intro g hg
      have h1 : (z⁻¹ * g⁻¹).ofConv ∈ pointsZero k (subgroupIdeal H) :=
        mul_mem_pointsZero_subgroupIdeal H
          (fun g' hg' => subset_pointsZero_pointsIdeal _
            (show toConv (g' * g⁻¹).ofConv ∈ H from H.mul_mem hg' (H.inv_mem hg)))
          (inv_mem_pointsZero_subgroupIdeal H hz)
      have h2 := inv_mem_pointsZero_subgroupIdeal H h1
      rwa [mul_inv_rev, inv_inv, inv_inv] at h2
    exact mul_mem_pointsZero_subgroupIdeal H hHz hy

theorem mem_closureSubgroup {H : Subgroup (WithConv (A →ₐ[k] k))} {y : WithConv (A →ₐ[k] k)} :
    y ∈ closureSubgroup H ↔ y.ofConv ∈ pointsZero k (subgroupIdeal H) :=
  Iff.rfl

theorem le_closureSubgroup (H : Subgroup (WithConv (A →ₐ[k] k))) : H ≤ closureSubgroup H :=
  fun y hy => subset_pointsZero_pointsIdeal _ (show toConv y.ofConv ∈ H from hy)

end Hopf

instance isHopfIdeal_subgroupIdeal {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A]
    [HopfAlgebra k A] [Algebra.FiniteType k A] (H : Subgroup (WithConv (A →ₐ[k] k))) :
    (subgroupIdeal H).IsHopfIdeal k := by
  have h : subgroupIdeal H = (TauCeti.HopfIdeal.vanishingIdeal (ofTauCeti.symm H)).toIdeal := by
    ext x
    simp [mem_subgroupIdeal, TauCeti.HopfIdeal.mem_toIdeal]
  rw [h]
  infer_instance

section HopfIdeal

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

@[expose] def quotientPointsEquiv (H : Subgroup (WithConv (A →ₐ[k] k))) :
    WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k) ≃* closureSubgroup H where
  toFun φ := ⟨toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal H))), fun a ha => by
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]⟩
  invFun y := toConv (Ideal.Quotient.liftₐ (subgroupIdeal H) y.1.ofConv y.2)
  left_inv φ := WithConv.ext (Ideal.Quotient.algHom_ext k (AlgHom.ext fun _ => rfl))
  right_inv y := Subtype.ext (WithConv.ext (AlgHom.ext fun _ => rfl))
  map_mul' φ ψ := Subtype.ext (congrArg toConv
    (AlgHom.convMul_comp_bialgHom_distrib φ ψ (Bialgebra.Quotient.mkBialgHom (subgroupIdeal H))))

theorem quotientPointsEquiv_apply (H : Subgroup (WithConv (A →ₐ[k] k)))
    (φ : WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k)) :
    ((quotientPointsEquiv H φ : closureSubgroup H) : WithConv (A →ₐ[k] k)).ofConv =
      φ.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal H)) :=
  rfl

end HopfIdeal

end CFSG.LieType.AlgebraicGroups

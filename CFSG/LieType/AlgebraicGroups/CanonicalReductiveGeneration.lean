module

public import CFSG.LieType.AlgebraicGroups.DynamicUnipotentDerived
public import CFSG.ThirdParty.TauCeti.OppositeCocharacter
import CFSG.LieType.AlgebraicGroups.DynamicOpenCellDensity
import CFSG.LieType.AlgebraicGroups.CanonicalReductiveTorus
import TauCeti.Algebra.AlgebraicGroup.Dynamic.LeviDecomposition.Basic

public noncomputable section

open WithConv

namespace CFSG.LieType.AlgebraicGroups.CanonicalReductive

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem eq_zero_of_forall_mem_closure_unipotent_levi
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M]
    (hconn : TauCeti.geometricallyConnectedCommHopfAlgProperty k M.obj)
    (l : M →ₐc[k] LaurentPolynomial k) (x : M)
    (hx : ∀ g ∈ Subgroup.closure
      ((TauCeti.Cocharacter.unipotent k l : Set (WithConv (M →ₐ[k] k))) ∪
        (TauCeti.Cocharacter.levi k l : Set (WithConv (M →ₐ[k] k))) ∪
        (TauCeti.Cocharacter.unipotent k
          (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) :
            Set (WithConv (M →ₐ[k] k)))), g.ofConv x = 0) :
    x = 0 := by
  have : ConnectedSpace (PrimeSpectrum M) :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k M.obj).mp hconn
  set S := Subgroup.closure
    ((TauCeti.Cocharacter.unipotent k l : Set (WithConv (M →ₐ[k] k))) ∪
      (TauCeti.Cocharacter.levi k l : Set (WithConv (M →ₐ[k] k))) ∪
      (TauCeti.Cocharacter.unipotent k
        (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) :
          Set (WithConv (M →ₐ[k] k)))) with hS
  have hU : TauCeti.Cocharacter.unipotent k l ≤ S := fun g hg ↦
    Subgroup.subset_closure (Or.inl (Or.inl hg))
  have hZ : TauCeti.Cocharacter.levi k l ≤ S := fun g hg ↦
    Subgroup.subset_closure (Or.inl (Or.inr hg))
  have hU' : TauCeti.Cocharacter.unipotent k
      (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) ≤ S := fun g hg ↦
    Subgroup.subset_closure (Or.inr hg)
  have h₁ : TauCeti.Cocharacter.parabolic k l ≤ S := by
    rw [← TauCeti.Cocharacter.unipotent_sup_levi]
    exact sup_le hU hZ
  have h₂ : TauCeti.Cocharacter.parabolic k
      (CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l) ≤ S := by
    rw [← TauCeti.Cocharacter.unipotent_sup_levi,
      CFSG.ThirdParty.TauCeti.Cocharacter.levi_oppositeCocharacter]
    exact sup_le hU' hZ
  have hJ := DynamicOpenCell.vanishingIdeal_eq_bot_of_parabolic_le M l S h₁ h₂
  have hxJ : x ∈ TauCeti.HopfIdeal.vanishingIdeal S :=
    (TauCeti.HopfIdeal.mem_vanishingIdeal S x).mpr fun g ↦ hx g.1 g.2
  rw [hJ, ← TauCeti.HopfIdeal.mem_toIdeal, TauCeti.HopfIdeal.bot_toIdeal, Ideal.mem_bot] at hxJ
  exact hxJ

theorem commute_mapDomain_connectedCenterCoordinateMap
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (z : TauCeti.HopfAlgebra.points (R := k) (H := connectedCenter M) (CommAlgCat.of k k))
    (y : WithConv (M →ₐ[k] k)) :
    Commute (TauCeti.AlgHom.mapDomain (connectedCenterCoordinateMap M) z) y := by
  apply TauCeti.HopfAlgebra.IsCentralPoint.commute
  apply TauCeti.CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup M.obj
    (TauCeti.CommHopfAlgCat.centerDefiningIdeal M.obj)
    (TauCeti.CommHopfAlgCat.isCentral_centerDefiningIdeal M.obj) (CommAlgCat.of k k)
  rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro x hx
  rw [TauCeti.AlgHom.mapDomain_apply_apply, connectedCenterCoordinateMap_kills_centerDefiningIdeal
    M x hx, map_zero]

theorem eq_zero_of_forall_connectedCenter_mul_derived
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M) (x : M)
    (hx : ∀ (z : TauCeti.HopfAlgebra.points (R := k) (H := connectedCenter M) (CommAlgCat.of k k))
      (d : TauCeti.HopfAlgebra.points (R := k) (H := derivedCoordinate M) (CommAlgCat.of k k)),
      (TauCeti.AlgHom.mapDomain (connectedCenterCoordinateMap M) z *
        TauCeti.AlgHom.mapDomain (derivedCoordinateMap M) d).ofConv x = 0) :
    x = 0 := by
  classical
  let : Algebra.Smooth k M := hM.smooth
  let : ConnectedSpace (PrimeSpectrum M) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k M.obj
      hM.geometricallyConnected
  let : IsDomain M := CFSG.isDomain_of_smooth_of_connected (k := k) M
  obtain ⟨I, hI, hfin⟩ := exists_isMaximalTorus_relIndex_centralizer_ne_zero M hM
  let T := TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)
  obtain ⟨l, hl⟩ := RegularCocharacter.exists_cocharacter_levi_le_centralizer M I
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k M.obj I).mp hI).1
  let l' := CFSG.ThirdParty.TauCeti.BialgHom.oppositeCocharacter l
  let Λ := TauCeti.Cocharacter.levi k l
  let Zc : Subgroup (WithConv (M →ₐ[k] k)) :=
    (TauCeti.AlgHom.mapDomain (A := k) (connectedCenterCoordinateMap M)).range
  let Dc : Subgroup (WithConv (M →ₐ[k] k)) :=
    (TauCeti.AlgHom.mapDomain (A := k) (derivedCoordinateMap M)).range
  have hZc : Zc.Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨z, rfl⟩ := hn
    rw [(commute_mapDomain_connectedCenterCoordinateMap M z y).symm.eq, mul_inv_cancel_right]
    exact ⟨z, rfl⟩
  let Γ' : Subgroup (WithConv (M →ₐ[k] k)) := Subgroup.closure
    ((TauCeti.Cocharacter.unipotent k l : Set (WithConv (M →ₐ[k] k))) ∪
      ((T ⊓ Λ : Subgroup (WithConv (M →ₐ[k] k))) : Set (WithConv (M →ₐ[k] k))) ∪
      (TauCeti.Cocharacter.unipotent k l' : Set (WithConv (M →ₐ[k] k))))
  have hle : Γ' ≤ Zc ⊔ Dc := by
    rw [Subgroup.closure_le]
    rintro y ((hy | hy) | hy)
    · obtain ⟨d, hd⟩ := exists_derivedCoordinateMap_point_of_mem_unipotent M l hy
      exact Subgroup.mem_sup_right ⟨d, hd⟩
    · exact quotientPointsSubgroup_le_connectedCenter_sup_derived M hM I hI hy.1
    · obtain ⟨d, hd⟩ := exists_derivedCoordinateMap_point_of_mem_unipotent M l' hy
      exact Subgroup.mem_sup_right ⟨d, hd⟩
  have hnorm : ∀ z ∈ Λ, ∀ g ∈ Γ', z * g * z⁻¹ ∈ Γ' := by
    intro z hz g hg
    have hz' : z ∈ TauCeti.Cocharacter.levi k l' := by
      rw [CFSG.ThirdParty.TauCeti.Cocharacter.levi_oppositeCocharacter]
      exact hz
    have hcl : Γ' ≤ Γ'.comap (MulAut.conj z).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ((hy | hy) | hy)
      · have h := (TauCeti.Cocharacter.leviConjugation k l ⟨z, hz⟩ ⟨y, hy⟩).2
        rw [TauCeti.Cocharacter.coe_leviConjugation_apply] at h
        exact Subgroup.subset_closure (Or.inl (Or.inl h))
      · have hc : y * z = z * y := Subgroup.mem_centralizer_iff.mp (hl hz) y hy.1
        change z * y * z⁻¹ ∈ Γ'
        rw [← hc, mul_inv_cancel_right]
        exact Subgroup.subset_closure (Or.inl (Or.inr hy))
      · have h := (TauCeti.Cocharacter.leviConjugation k l' ⟨z, hz'⟩ ⟨y, hy⟩).2
        rw [TauCeti.Cocharacter.coe_leviConjugation_apply] at h
        exact Subgroup.subset_closure (Or.inr h)
    exact hcl hg
  have hdecomp : ∀ g ∈ Subgroup.closure
      ((TauCeti.Cocharacter.unipotent k l : Set (WithConv (M →ₐ[k] k))) ∪
        (Λ : Set (WithConv (M →ₐ[k] k))) ∪
        (TauCeti.Cocharacter.unipotent k l' : Set (WithConv (M →ₐ[k] k)))),
      ∃ γ ∈ Γ', ∃ z ∈ Λ, g = γ * z := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with (hy | hy) | hy
      · exact ⟨y, Subgroup.subset_closure (Or.inl (Or.inl hy)), 1, Λ.one_mem, (mul_one y).symm⟩
      · exact ⟨1, Γ'.one_mem, y, hy, (one_mul y).symm⟩
      · exact ⟨y, Subgroup.subset_closure (Or.inr hy), 1, Λ.one_mem, (mul_one y).symm⟩
    | one => exact ⟨1, Γ'.one_mem, 1, Λ.one_mem, (mul_one 1).symm⟩
    | mul a b _ _ ha hb =>
      obtain ⟨γ₁, hγ₁, z₁, hz₁, rfl⟩ := ha
      obtain ⟨γ₂, hγ₂, z₂, hz₂, rfl⟩ := hb
      refine ⟨γ₁ * (z₁ * γ₂ * z₁⁻¹), Γ'.mul_mem hγ₁ (hnorm z₁ hz₁ γ₂ hγ₂), z₁ * z₂,
        Λ.mul_mem hz₁ hz₂, by group⟩
    | inv a _ ha =>
      obtain ⟨γ, hγ, z, hz, rfl⟩ := ha
      refine ⟨z⁻¹ * γ⁻¹ * z⁻¹⁻¹, hnorm z⁻¹ (Λ.inv_mem hz) γ⁻¹ (Γ'.inv_mem hγ), z⁻¹,
        Λ.inv_mem hz, by group⟩
  have hTΛ : (T.subgroupOf Λ).index ≠ 0 :=
    mt (Subgroup.relIndex_eq_zero_of_le_right hl) hfin
  have : Finite (Λ ⧸ T.subgroupOf Λ) := Subgroup.index_ne_zero_iff_finite.mp hTΛ
  let : Fintype (Λ ⧸ T.subgroupOf Λ) := Fintype.ofFinite _
  let F : Finset (WithConv (M →ₐ[k] k)) :=
    Finset.univ.image fun q : Λ ⧸ T.subgroupOf Λ => ((Quotient.out q : Λ) : WithConv (M →ₐ[k] k))
  refine TorusConjugacy.eq_zero_of_forall_mem_of_forall_exists_mul_inv_mem
    (fun y hy => eq_zero_of_forall_mem_closure_unipotent_levi M hM.geometricallyConnected l y hy)
    F ?_ (Γ' := (Γ' : Set (WithConv (M →ₐ[k] k)))) ?_
  · intro g hg
    obtain ⟨γ, hγ, z, hz, rfl⟩ := hdecomp g hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (T.subgroupOf Λ) ⟨z, hz⟩
    refine ⟨((Quotient.out (QuotientGroup.mk ⟨z, hz⟩ : Λ ⧸ T.subgroupOf Λ) : Λ) :
      WithConv (M →ₐ[k] k)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have hh' : ((Quotient.out (QuotientGroup.mk ⟨z, hz⟩ : Λ ⧸ T.subgroupOf Λ) : Λ) :
        WithConv (M →ₐ[k] k)) = z * ((h : Λ) : WithConv (M →ₐ[k] k)) := by
      rw [show (Quotient.out (QuotientGroup.mk ⟨z, hz⟩ : Λ ⧸ T.subgroupOf Λ) : Λ) =
        ⟨z, hz⟩ * (h : Λ) from hh]
      rfl
    have hhT : ((h : Λ) : WithConv (M →ₐ[k] k)) ∈ T := Subgroup.mem_subgroupOf.mp h.2
    have hhΛ : ((h : Λ) : WithConv (M →ₐ[k] k)) ∈ Λ := (h : Λ).2
    have hc : z * ((h : Λ) : WithConv (M →ₐ[k] k))⁻¹ * z⁻¹ =
        ((h : Λ) : WithConv (M →ₐ[k] k))⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.mp (hl hz) _ (T.inv_mem hhT), mul_inv_cancel_right]
    rw [hh', show γ * z * (z * ((h : Λ) : WithConv (M →ₐ[k] k)))⁻¹ =
      γ * (z * ((h : Λ) : WithConv (M →ₐ[k] k))⁻¹ * z⁻¹) by group, hc]
    exact Γ'.mul_mem hγ (Γ'.inv_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨hhT, hhΛ⟩))))
  · intro g hg
    have hg' := hle hg
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg'
    obtain ⟨a, ⟨z, rfl⟩, b, ⟨d, rfl⟩, hab⟩ := hg'
    rw [← hab]
    exact hx z d

end CFSG.LieType.AlgebraicGroups.CanonicalReductive

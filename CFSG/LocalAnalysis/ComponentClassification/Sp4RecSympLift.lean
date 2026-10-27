module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module CFSG.LocalAnalysis.ComponentInitial

theorem exists_pComponent_lifts_map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hcentral : f.ker ≤ center X) [f.range.Normal]
    [Group.IsSolvable (Y ⧸ f.range)] {L₁ L₂ : Subgroup Y} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) :
    ∃ M₁ M₂ : Subgroup X, IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ ∧
      M₁.map f = L₁ ∧ M₂.map f = L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : f.rangeRestrict.ker ≤ center X := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hcentral
  obtain ⟨hle₁, hr₁⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₁ h₁
  obtain ⟨hle₂, hr₂⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₂ h₂
  obtain ⟨M₁, hM₁, hm₁, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₁
  obtain ⟨M₂, hM₂, hm₂, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₂
  have hmap : ∀ (M L : Subgroup Y) (N : Subgroup X), L ≤ f.range →
      N.map f.rangeRestrict = L.subgroupOf f.range → N.map f = L := by
    intro M L N hL hN
    have h1 : (N.map f.rangeRestrict).map f.range.subtype = N.map f := by
      rw [map_map]
      rfl
    rw [← h1, hN, map_subgroupOf_eq_of_le hL]
  refine ⟨M₁, M₂, hM₁, hM₂, fun h => hne ?_, hmap L₁ L₁ M₁ hle₁ hm₁, hmap L₂ L₂ M₂ hle₂ hm₂⟩
  rw [h, hm₂] at hm₁
  have h12 := subgroupOf_inj.mp hm₁
  rw [inf_of_le_left hle₂, inf_of_le_left hle₁] at h12
  exact h12.symm

theorem exists_fixed_lifts {X : Type*} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hZ : Z ≤ center X) (ψ : MulAut X) (hψ : Z.map ψ.toMonoidHom = Z)
    {L₁ L₂ : Subgroup (FixedCommutingProduct.fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient Z ψ hψ))}
    (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) :
    ∃ M₁ M₂ : Subgroup (FixedCommutingProduct.fixedSubgroup ψ),
      IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ ∧
      M₁.map (CatalogueBFixedCentralQuotient.fixedProjection Z ψ hψ) = L₁ ∧
      M₂.map (CatalogueBFixedCentralQuotient.fixedProjection Z ψ hψ) = L₂ := by
  have hN : (CatalogueBFixedCentralQuotient.fixedProjection Z ψ hψ).range.Normal :=
    CatalogueBFixedCentralQuotient.fixedImage_normal Z ψ hψ hZ
  have hcomm := CatalogueBFixedCentralQuotient.fixed_quotient_abelian Z ψ hψ hZ
  have : Group.IsSolvable (FixedCommutingProduct.fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient Z ψ hψ) ⧸
        (CatalogueBFixedCentralQuotient.fixedProjection Z ψ hψ).range) :=
    Group.isSolvable_of_comm (fun a b => hcomm.is_comm.comm a b)
  exact exists_pComponent_lifts_map _
    (CatalogueBFixedCentralQuotient.fixedProjection_kernel_central Z ψ hψ hZ) h₁ h₂ hne

theorem linGL_pComponent_eq {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hW : 1 ≤ finrank K W)
    {J₁ J₂ : Subgroup (LinearMap.GeneralLinearGroup K W)} (h₁ : IsPComponent 2 J₁)
    (h₂ : IsPComponent 2 J₂) : J₁ = J₂ := by
  set e := (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).trans
    (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis K W))
  obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ K hW 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁)
  obtain ⟨-, -, -, k₂, -⟩ := CatalogueBGeneralLinear.pComponent_classification _ K hW 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂)
  exact map_injective e.injective (k₁.trans k₂.symm)

theorem sp_pComponent_eq {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hodd : Odd (Nat.card K)) {C : LinearMap.BilinForm K W}
    (hC : C.IsAlt) (hnd : C.Nondegenerate) (hW : 2 ≤ finrank K W)
    {J₁ : Subgroup (sesqUnitaryGroup C)} (h₁ : IsPComponent 2 J₁) :
    (∀ J₂ : Subgroup (sesqUnitaryGroup C), IsPComponent 2 J₂ → J₁ = J₂) ∧
      (4 ≤ finrank K W → J₁ = ⊤) := by
  set e := CatalogueBSymplecticB.sesqUnitaryIsometryEquiv C
  obtain ⟨-, hsmall, hbig⟩ :=
    CatalogueBAlternatingIsometry.odd_symplectic_all_dimensional_isometry_p_components C hC hnd
      hW hodd
  have k₁ := CatalogueBAlternating.pComponent_map_equiv 2 e _ h₁
  by_cases hs : finrank K W = 2 ∧ Nat.card K = 3
  · exact ((hsmall hs).2 2 Nat.prime_two _ k₁).elim
  · have hs' : finrank K W ≠ 2 ∨ Nat.card K ≠ 3 := not_and_or.mp hs
    have e₁ := (hbig hs').2 2 Nat.prime_two _ k₁
    refine ⟨fun J₂ h₂ => ?_, fun _ => ?_⟩
    · have e₂ := (hbig hs').2 2 Nat.prime_two _
        (CatalogueBAlternating.pComponent_map_equiv 2 e _ h₂)
      exact map_injective e.injective (e₁.trans e₂.symm)
    · exact map_injective e.injective
        (e₁.trans (map_top_of_surjective e.toMonoidHom e.surjective).symm)

end CFSG.ComponentClassification.Sp4Rec

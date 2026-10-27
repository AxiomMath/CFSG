module

public import CFSG.ThirdParty.TauCeti.DynamicSmooth

public noncomputable section

open WithConv TauCeti

namespace CFSG.LieType.AlgebraicGroups.DynamicUnipotent

universe u v w

theorem formallySmooth_of_retraction {R : Type u} {P : Type v} {A : Type w} [CommRing R]
    [CommRing P] [CommRing A] [Algebra R P] [Algebra R A] [Algebra.FormallySmooth R P]
    (ι : A →ₐ[R] P) (π : P →ₐ[R] A) (h : π.comp ι = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  refine Algebra.FormallySmooth.iff_comp_surjective.mpr fun C _ _ J hJ f => ?_
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective (R := R) (A := P) J hJ (f.comp π)
  refine ⟨g.comp ι, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, h, AlgHom.comp_id]

variable {R : Type u} {H : Type v} [CommRing R] [CommRing H] [HopfAlgebra R H]

local notation "Pideal" l => (CFSG.ThirdParty.TauCeti.Cocharacter.parabolicDefiningHopfIdeal l)
local notation "Uideal" l => (CFSG.ThirdParty.TauCeti.BialgHom.unipotentDefiningHopfIdeal l)

theorem mkₐ_mem_parabolic (l : H →ₐc[R] LaurentPolynomial R) :
    toConv (Ideal.Quotient.mkₐ R (Pideal l).toIdeal) ∈
      Cocharacter.parabolic (H ⧸ (Pideal l).toIdeal) l := by
  rw [← CFSG.ThirdParty.TauCeti.Cocharacter.quotientPointsSubgroup_parabolicDefiningHopfIdeal l,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro h hh
  rw [ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hh)

theorem mkₐ_mem_unipotent (l : H →ₐc[R] LaurentPolynomial R) :
    toConv (Ideal.Quotient.mkₐ R (Uideal l).toIdeal) ∈
      Cocharacter.unipotent (H ⧸ (Uideal l).toIdeal) l := by
  rw [← CFSG.ThirdParty.TauCeti.BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal l,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro h hh
  rw [ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hh)

theorem exists_retraction_unipotent (l : H →ₐc[R] LaurentPolynomial R) :
    ∃ (ι : H ⧸ (Uideal l).toIdeal →ₐ[R] H ⧸ (Pideal l).toIdeal)
      (π : H ⧸ (Pideal l).toIdeal →ₐ[R] H ⧸ (Uideal l).toIdeal),
      π.comp ι = AlgHom.id R _ := by
  set IP := (Pideal l).toIdeal
  set IU := (Uideal l).toIdeal
  have hle : IP ≤ IU := HopfIdeal.toIdeal_le_toIdeal.mpr
    (CFSG.ThirdParty.TauCeti.BialgHom.parabolicDefiningHopfIdeal_le_unipotentDefiningHopfIdeal l)
  let x : WithConv (H →ₐ[R] H ⧸ IP) := toConv (Ideal.Quotient.mkₐ R IP)
  have hx : x ∈ Cocharacter.parabolic (H ⧸ IP) l := mkₐ_mem_parabolic l
  let r := x * (Cocharacter.limit (H ⧸ IP) l ⟨x, hx⟩)⁻¹
  have hr : r ∈ Cocharacter.unipotent (H ⧸ IP) l := Cocharacter.mul_limit_inv_mem_unipotent hx
  have hrker : ∀ a ∈ IU, r.ofConv a = 0 := by
    have hr' := hr
    rw [← CFSG.ThirdParty.TauCeti.BialgHom.quotientPointsSubgroup_unipotentDefiningHopfIdeal l,
      CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hr'
    exact fun a ha => hr' a (HopfIdeal.mem_toIdeal.mp ha)
  let ι : H ⧸ IU →ₐ[R] H ⧸ IP := Ideal.Quotient.liftₐ IU r.ofConv hrker
  let π : H ⧸ IP →ₐ[R] H ⧸ IU := Ideal.Quotient.factorₐ R hle
  refine ⟨ι, π, Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)⟩
  have hπx : TauCeti.AlgHom.mapValue π x = toConv (Ideal.Quotient.mkₐ R IU) := by
    rw [TauCeti.AlgHom.mapValue_apply, ofConv_toConv]
    rfl
  have hlim : TauCeti.AlgHom.mapValue π (Cocharacter.limit (H ⧸ IP) l ⟨x, hx⟩) = 1 := by
    rw [Cocharacter.mapValue_limit]
    obtain ⟨hU, hU1⟩ := Cocharacter.mem_unipotent_iff.mp (mkₐ_mem_unipotent l)
    rw [← hU1]
    congr 1
    exact Subtype.ext hπx
  have hπr : TauCeti.AlgHom.mapValue π r = toConv (Ideal.Quotient.mkₐ R IU) := by
    simp only [r, map_mul, map_inv, hπx, hlim, inv_one, mul_one]
  have h := congrArg ofConv hπr
  simp only [TauCeti.AlgHom.mapValue_apply, ofConv_toConv] at h
  have hι : ι (Ideal.Quotient.mkₐ R IU a) = r.ofConv a := by
    simp only [ι, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.id_apply, hι]
  exact DFunLike.congr_fun h a

theorem formallySmooth_quotient_unipotentDefiningHopfIdeal (l : H →ₐc[R] LaurentPolynomial R)
    [Algebra.FormallySmooth R H] :
    Algebra.FormallySmooth R (H ⧸ (Uideal l).toIdeal) := by
  obtain ⟨ι, π, h⟩ := exists_retraction_unipotent l
  exact formallySmooth_of_retraction ι π h

theorem smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal [IsNoetherianRing R]
    {M : FiniteTypeCommHopfAlgCat.{u, v} R} [Algebra.Smooth R M]
    (l : M →ₐc[R] LaurentPolynomial R) :
    smoothCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient M (Uideal l)).obj := by
  have := formallySmooth_quotient_unipotentDefiningHopfIdeal l
  rw [smoothCommHopfAlgProperty_iff]
  exact ⟨this, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end CFSG.LieType.AlgebraicGroups.DynamicUnipotent

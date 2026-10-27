module

public import CFSG.GroupTheory.GLS2.GroupTheory.PiComponents
import CFSG.GroupTheory.GLS2.GroupTheory.Residuals
import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.SecondGeneration

theorem IsPiQuasisimple.of_mulEquiv
    {π : Set Nat.Primes} {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (hH : IsPiQuasisimple π H) : IsPiQuasisimple π G := by
  refine ⟨?_, ?_⟩
  · rw [← map_piResidual_eq_of_surjective πᶜ e.symm.toMonoidHom e.symm.surjective,
      hH.residual_eq_top, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective]
  · exact CFSG.IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (CFSG.piCore πᶜ G) (CFSG.piCore πᶜ H) e
        (CFSG.LocalCores.piCore_map_mulEquiv πᶜ e)) hH.quotient_isQuasisimple

theorem IsPiComponent.map_mulEquiv
    {π : Set Nat.Primes} {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {K : Subgroup G} (hK : IsPiComponent π G K) (e : G ≃* H) :
    IsPiComponent π H (K.map e.toMonoidHom) :=
  ⟨hK.isSubnormal.map e.surjective,
    IsPiQuasisimple.of_mulEquiv
      (K.equivMapOfInjective e.toMonoidHom e.injective).symm hK.isPiQuasisimple⟩

theorem isPiComponent_map_mulAut_iff
    {G : Type*} [Group G] [Finite G] (π : Set Nat.Primes)
    (e : MulAut G) (K : Subgroup G) :
    IsPiComponent π G (K.map e.toMonoidHom) ↔ IsPiComponent π G K := by
  constructor
  · intro hK
    have hback := hK.map_mulEquiv e.symm
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.symm_apply_apply x
    simpa only [Subgroup.map_map, hcomp, Subgroup.map_id] using hback
  · exact fun hK => hK.map_mulEquiv e

instance piLayer_characteristic
    {G : Type*} [Group G] [Finite G] (π : Set Nat.Primes) :
    (piLayer π G).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun e => ?_
  let S : Set (Subgroup G) := {K | IsPiComponent π G K}
  let E : Subgroup G ≃o Subgroup G := MulEquiv.mapSubgroup e
  have hImage : E '' S = S := by
    ext K
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact (isPiComponent_map_mulAut_iff π e L).2 hL
    · intro hK
      change IsPiComponent π G K at hK
      refine ⟨E.symm K, ?_, E.apply_symm_apply K⟩
      apply (isPiComponent_map_mulAut_iff π e (E.symm K)).1
      change IsPiComponent π G (E (E.symm K))
      simpa only [E.apply_symm_apply] using hK
  change E (sSup S) = sSup S
  rw [OrderIso.map_sSup, ← sSup_image, hImage]

end CFSG.SecondGeneration

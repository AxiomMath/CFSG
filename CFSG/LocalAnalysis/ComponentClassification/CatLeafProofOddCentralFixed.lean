module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def commutatorEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    commutator G ≃* commutator H :=
  ((commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]))

theorem nonempty_centerQuotient_equiv_of_quotientFixed_commutator {X : Type*} [Group X]
    (Z : Subgroup X) [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hinv : Z.map ψ.toMonoidHom = Z) (hD : IsQuasisimple (commutator (fixedSubgroup ψ)))
    {L : Subgroup (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))}
    (hL : IsComponent L) :
    Nonempty (L ⧸ center L ≃*
      commutator (fixedSubgroup ψ) ⧸ center (commutator (fixedSubgroup ψ))) := by
  set F := fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)
  set π := CatalogueBFixedCentralQuotient.fixedProjection Z ψ hinv
  have hF0n : π.range.Normal := CatalogueBFixedCentralQuotient.fixedImage_normal Z ψ hinv hcentral
  set D := commutator (fixedSubgroup ψ)
  obtain ⟨Dbar, hDbar⟩ : ∃ Dbar : Subgroup F, Dbar = ⁅π.range, π.range⁆ := ⟨_, rfl⟩
  have hDmap : D.map π = Dbar := (map_commutator_eq (f := π)).trans hDbar.symm
  have hDn : Dbar.Normal := hDbar ▸ Subgroup.commutator_normal _ _
  have hFF : commutator F ≤ π.range :=
    CatalogueBFixedCentralQuotient.fixed_commutator_le_image Z ψ hinv hcentral
  have hsolv : Group.IsSolvable (F ⧸ Dbar) := by
    refine ⟨⟨2, ?_⟩⟩
    rw [eq_bot_iff]
    refine (derivedSeries_le_map_derivedSeries (QuotientGroup.mk'_surjective Dbar) 2).trans ?_
    rw [le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hDbar, derivedSeries_succ,
      derivedSeries_succ, derivedSeries_zero]
    exact Subgroup.commutator_mono hFF hFF
  set πD := π.subgroupMap D
  have hsurjD : Function.Surjective πD := π.subgroupMap_surjective D
  have hkerD : πD.ker ≤ center D := by
    intro x hx
    have hx1 : π x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxZ : x.val ∈ Z.subgroupOf (fixedSubgroup ψ) := by
      rw [← CatalogueBFixedCentralQuotient.fixedProjection_kernel Z ψ hinv]
      exact hx1
    rw [Subgroup.mem_subgroupOf] at hxZ
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hxZ) _
  have hDbarq : IsQuasisimple (D.map π) :=
    LocalCores.isQuasisimple_of_surjective hD πD hsurjD hkerD
  rw [hDmap] at hDbarq
  have hLD := eq_of_isComponent_of_normal_quasisimple hDbarq hsolv hL
  obtain ⟨e⟩ :=
    LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hD πD hsurjD hkerD
  exact ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (hLD.trans hDmap.symm))
    (Subgroup.map_center_eq _)).trans e.symm⟩

open CatalogueBOrthogonalLinearFixed in
theorem nonempty_centerQuotient_equiv_of_normalQuotientFixed {X : Type*} [Group X]
    (N Z : Subgroup X) [N.Normal] [Z.Normal] (hcentral : Z ≤ center X) (ψ : MulAut X)
    (hN : N.map ψ.toMonoidHom = N) (hZ : Z.map ψ.toMonoidHom = Z)
    (hDN : ∀ x ∈ commutator (fixedSubgroup ψ), (x : X) ∈ N)
    (hD : IsQuasisimple (commutator (fixedSubgroup ψ)))
    {L : Subgroup (fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ))} (hL : IsComponent L) :
    Nonempty (L ⧸ center L ≃*
      commutator (fixedSubgroup ψ) ⧸ center (commutator (fixedSubgroup ψ))) := by
  set C := fixedSubgroup ψ
  set C₀ := N.subgroupOf C
  have hC₀ : ⁅C₀, C₀⁆ = commutator C := by
    refine le_antisymm (Subgroup.commutator_mono le_top le_top) ?_
    have hle : commutator C ≤ C₀ := fun x hx => hDN x hx
    have hperf : ⁅commutator C, commutator C⁆ = commutator C :=
      Subgroup.isPerfect_iff.mp hD.1
    calc commutator C = ⁅commutator C, commutator C⁆ := hperf.symm
      _ ≤ ⁅C₀, C₀⁆ := Subgroup.commutator_mono hle hle
  let Φ : commutator (fixedSubgroup (restrictAutomorphism N ψ hN)) ≃* commutator C :=
    (commutatorEquiv (fixedNormalEquiv N ψ hN)).trans
      ((((commutator C₀).equivMapOfInjective C₀.subtype C₀.subtype_injective).trans
        (MulEquiv.subgroupCongr (by rw [map_commutator_eq, Subgroup.range_subtype]))).trans
        (MulEquiv.subgroupCongr hC₀))
  have hD' : IsQuasisimple (commutator (fixedSubgroup (restrictAutomorphism N ψ hN))) :=
    LocalCores.isQuasisimple_of_mulEquiv Φ.symm hD
  obtain ⟨e⟩ := nonempty_centerQuotient_equiv_of_quotientFixed_commutator (Z.subgroupOf N)
    (central_subgroupOf N Z hcentral) (restrictAutomorphism N ψ hN)
    (restricted_central_invariant N Z ψ hN hZ) hD' hL
  exact ⟨e.trans (QuotientGroup.congr _ _ Φ (Subgroup.map_center_eq Φ))⟩

end CFSG.ComponentClassification.CatLeafProof

module

public import CFSG.LieType.AlgebraicGroups.TorusCoordinates
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem surjective_identityComponent_of_surjective_torus
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (p : T →ₐc[k] H)
    (hsur : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) p)) :
    Function.Surjective (TauCeti.AlgHom.mapDomain (A := k)
      ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H))).hom.hom.comp p)) := by
  classical
  let I := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let q : H →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.identityComponent H :=
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I).hom.hom
  change Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) (q.comp p))
  intro t
  let n := Nat.card (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H)
  have hn : 0 < n := Nat.card_pos
  obtain ⟨d, ⟨e⟩⟩ := exists_coordinateEquiv_of_torus T hT
  let ψ : WithConv (T →ₐ[k] k) ≃* (Fin d → kˣ) :=
    (TauCeti.AlgHom.mapDomainMulEquiv (A := k) e).trans
      (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := Fin d))
  have hroot : ∀ i : Fin d, ∃ u : kˣ, u ^ n = ψ t i := by
    intro i
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) (ψ t i : k) hn
    have hz0 : z ≠ 0 := by
      intro hzero
      have h : (ψ t i : k) = 0 := by
        rw [← hz, hzero, zero_pow (Nat.ne_of_gt hn)]
      exact (ψ t i).ne_zero h
    exact ⟨Units.mk0 z hz0, Units.ext hz⟩
  choose c hc using hroot
  let rt : WithConv (T →ₐ[k] k) := ψ.symm c
  have hrt : rt ^ n = t := by
    apply ψ.injective
    rw [map_pow, ψ.apply_symm_apply]
    exact funext fun i => by simpa using hc i
  obtain ⟨h, hh⟩ := hsur rt
  let : Group (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H) :=
    (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H).str
  have hcomponent : (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMk H h) ^ n = 1 :=
    pow_card_eq_one'
  have hmem : h ^ n ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
    (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMk_eq_one_iff H (h ^ n)).mp (by
      rw [map_pow, hcomponent])
  have hrange : h ^ n ∈
      (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I
        (CommAlgCat.of k k)).hom.range := by
    change h ^ n ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)
    exact hmem
  obtain ⟨h0, hh0⟩ := MonoidHom.mem_range.mp hrange
  refine ⟨h0, ?_⟩
  have hq : TauCeti.AlgHom.mapDomain (A := k) q h0 = h ^ n := by
    rw [← hh0]
    apply WithConv.ofConv_injective
    ext x
    rw [TauCeti.AlgHom.mapDomain_apply_apply,
      TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply]
    have hqx : q x = (Ideal.Quotient.mkₐ k I.toIdeal) x := by
      change (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom x =
        (Ideal.Quotient.mkₐ k I.toIdeal) x
      exact TauCeti.CommHopfAlgCat.mkQuotient_apply H.obj I x
    rw [hqx]
  calc
    TauCeti.AlgHom.mapDomain (A := k) (q.comp p) h0 =
        TauCeti.AlgHom.mapDomain (A := k) p
          (TauCeti.AlgHom.mapDomain (A := k) q h0) := by
      rw [TauCeti.AlgHom.mapDomain_comp]
      rfl
    _ = TauCeti.AlgHom.mapDomain (A := k) p (h ^ n) := by rw [hq]
    _ = (TauCeti.AlgHom.mapDomain (A := k) p h) ^ n := by rw [map_pow]
    _ = rt ^ n := by rw [hh]
    _ = t := hrt

end CFSG.LieType.AlgebraicGroups

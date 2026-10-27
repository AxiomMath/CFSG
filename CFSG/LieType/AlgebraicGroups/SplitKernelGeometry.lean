module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k]
variable {B T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}

noncomputable abbrev splitKernelIdeal (p : T →ₐc[k] B) :
    TauCeti.HopfIdeal k B :=
  TauCeti.CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p)

noncomputable abbrev splitKernelQuotient (p : T →ₐc[k] B) :
    TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.quotient B (splitKernelIdeal p)

noncomputable abbrev splitKernelQuotientMap (p : T →ₐc[k] B) :
    B →ₐ[k] splitKernelQuotient p :=
  (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient B (splitKernelIdeal p)).hom.hom.toAlgHom

noncomputable def splitKernelProjection (p : T →ₐc[k] B) (j : B →ₐc[k] T) :
    B →ₐ[k] B :=
  (toConv (AlgHom.id k B) * (toConv ((p.comp j).toAlgHom))⁻¹).ofConv

theorem splitKernelProjection_comp_p
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T) :
    (splitKernelProjection p j).comp p.toAlgHom =
      (Algebra.ofId k B).comp (Bialgebra.counitAlgHom k T) := by
  have hj' : j.toAlgHom.comp p.toAlgHom = AlgHom.id k T := by
    simpa only [BialgHom.comp_toAlgHom, BialgHom.id_toAlgHom] using
      congrArg BialgHom.toAlgHom hj
  have hmaps : TauCeti.AlgHom.mapDomain p (toConv (AlgHom.id k B)) =
      TauCeti.AlgHom.mapDomain p (toConv ((p.comp j).toAlgHom)) := by
    rw [TauCeti.AlgHom.mapDomain_apply, TauCeti.AlgHom.mapDomain_apply]
    simp only [AlgHom.id_comp, BialgHom.comp_toAlgHom,
      AlgHom.comp_assoc, hj', AlgHom.comp_id]
  have h : TauCeti.AlgHom.mapDomain p
      (toConv (AlgHom.id k B) * (toConv ((p.comp j).toAlgHom))⁻¹) = 1 := by
    rw [map_mul, map_inv, hmaps, mul_inv_cancel]
  simpa only [splitKernelProjection, TauCeti.AlgHom.mapDomain_apply, toConv_ofConv,
    AlgHom.convOne_def, WithConv.ofConv_toConv] using congrArg WithConv.ofConv h

theorem splitKernelIdeal_toIdeal_le_ker_splitKernelProjection
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T) :
    (splitKernelIdeal p).toIdeal ≤
      RingHom.ker (splitKernelProjection p j).toRingHom :=
  (TauCeti.CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff
    (_root_.CommHopfAlgCat.ofHom p) (splitKernelProjection p j)).mpr
      (splitKernelProjection_comp_p p j hj)

theorem exists_splitKernelQuotient_retraction
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T) :
    ∃ r : splitKernelQuotient p →ₐ[k] B,
      Function.Injective r ∧
      r.comp (splitKernelQuotientMap p) = splitKernelProjection p j ∧
      (splitKernelQuotientMap p).comp r = AlgHom.id k (splitKernelQuotient p) := by
  let I := splitKernelIdeal p
  let K := splitKernelQuotient p
  let projection := splitKernelProjection p j
  have hkill : I.toIdeal ≤ RingHom.ker projection.toRingHom :=
    splitKernelIdeal_toIdeal_le_ker_splitKernelProjection p j hj
  let q : B →ₐ[k] K := Ideal.Quotient.mkₐ k I.toIdeal
  let r : K →ₐ[k] B :=
    Ideal.Quotient.liftₐ I.toIdeal projection fun x hx => RingHom.mem_ker.mp (hkill hx)
  have hrq : r.comp q = projection := by
    simpa only [r, q] using Ideal.Quotient.liftₐ_comp I.toIdeal projection
      (fun x hx => RingHom.mem_ker.mp (hkill hx))
  have hqp : q.comp p.toAlgHom =
      (Algebra.ofId k K).comp (Bialgebra.counitAlgHom k T) := by
    refine (TauCeti.CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff
      (_root_.CommHopfAlgCat.ofHom p) q).mp ?_
    change I.toIdeal ≤ RingHom.ker q.toRingHom
    simpa only [q, AlgHom.toRingHom_eq_coe] using
      le_of_eq (Ideal.Quotient.mkₐ_ker (R₁ := k) I.toIdeal).symm
  have hF : TauCeti.AlgHom.mapValue q (toConv ((p.comp j).toAlgHom)) =
      (1 : WithConv (B →ₐ[k] K)) := by
    rw [TauCeti.AlgHom.mapValue_apply]
    apply WithConv.ofConv_injective
    rw [AlgHom.convOne_def, WithConv.toConv_ofConv, BialgHom.comp_toAlgHom,
      ← AlgHom.comp_assoc, hqp, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp j]
  have hqP : q.comp projection = q := by
    have hproj : toConv projection =
        toConv (AlgHom.id k B) * (toConv ((p.comp j).toAlgHom))⁻¹ := by
      dsimp only [projection, splitKernelProjection]
    have h : TauCeti.AlgHom.mapValue q (toConv projection) = toConv q := by
      rw [hproj, map_mul, map_inv]
      have hid : TauCeti.AlgHom.mapValue q (toConv (AlgHom.id k B)) = toConv q := by
        rw [TauCeti.AlgHom.mapValue_apply, WithConv.ofConv_toConv, AlgHom.comp_id]
      rw [hid, hF, inv_one, mul_one]
    simpa only [TauCeti.AlgHom.mapValue_apply, WithConv.toConv_ofConv,
      WithConv.ofConv_toConv] using congrArg WithConv.ofConv h
  have hqsurj : Function.Surjective q := by
    simpa only [q] using Ideal.Quotient.mkₐ_surjective k I.toIdeal
  have hq_rq : (q.comp r).comp q = q := by
    rw [AlgHom.comp_assoc, hrq, hqP]
  have hqr : q.comp r = AlgHom.id k K := by
    apply AlgHom.ext
    intro x
    obtain ⟨b, rfl⟩ := hqsurj x
    exact DFunLike.congr_fun hq_rq b
  have hqr_inj : Function.Injective r := by
    intro x y hxy
    have hx := DFunLike.congr_fun hqr x
    have hy := DFunLike.congr_fun hqr y
    calc
      x = (q.comp r) x := by simpa using hx.symm
      _ = (q.comp r) y := by
        change q (r x) = q (r y)
        exact congrArg q hxy
      _ = y := by simpa using hy
  have hqmap : q = splitKernelQuotientMap p := by
    ext x
    exact TauCeti.CommHopfAlgCat.mkQuotient_apply B.obj I x
  refine ⟨r, hqr_inj, ?_, ?_⟩
  · rw [← hqmap]
    exact hrq
  · rw [← hqmap]
    exact hqr

theorem splitKernelQuotient_isReduced
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    [IsReduced B] :
    IsReduced (splitKernelQuotient p) := by
  obtain ⟨r, hr, -⟩ := exists_splitKernelQuotient_retraction p j hj
  exact isReduced_of_injective r.toRingHom hr

theorem splitKernelQuotient_connectedSpace
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (splitKernelQuotient p)) := by
  obtain ⟨r, hr, -⟩ := exists_splitKernelQuotient_retraction p j hj
  exact TauCeti.connectedSpace_primeSpectrum_of_injective r.toRingHom hr

section IsAlgClosed

variable [IsAlgClosed k]

theorem splitKernelQuotient_smooth
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    [IsReduced B] :
    TauCeti.smoothCommHopfAlgProperty k (splitKernelQuotient p).obj :=
  (TauCeti.smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k
    (splitKernelQuotient p).obj).mpr (splitKernelQuotient_isReduced p j hj)

theorem splitKernelQuotient_geometricallyConnected
    (p : T →ₐc[k] B) (j : B →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    [ConnectedSpace (PrimeSpectrum B)] :
    TauCeti.geometricallyConnectedCommHopfAlgProperty k (splitKernelQuotient p).obj :=
  (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).mpr
    (splitKernelQuotient_connectedSpace p j hj)


end IsAlgClosed

end CFSG.LieType.AlgebraicGroups

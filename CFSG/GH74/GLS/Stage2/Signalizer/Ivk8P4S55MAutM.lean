module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Weak
public import Certificates.Data.GH74.Ivk8Weak
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MN1
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.Generic6
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3Spec
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Certificates CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem map_P_eq_innSub {Y : Type} [Group Y] {G : Type*} [Group G]
    (M : CFSG.GH74.KGroups.AutModel Y G) (hPA : M.P ≤ M.A) :
    (M.P.subgroupOf M.A).map M.Φ.symm.toMonoidHom = innSub Y := by
  ext φ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have h : (M.Φ (M.Φ.symm σ) : G) ∈ M.P := by
      rw [MulEquiv.apply_symm_apply]
      exact hσ
    obtain ⟨k, hk⟩ := M.inner_of_mem _ h
    exact ⟨k, MulEquiv.ext fun x => by rw [MulAut.conj_apply]; exact (hk x).symm⟩
  · rintro ⟨k, rfl⟩
    have hk : (M.e k : G) ∈ M.A := hPA (M.e k).2
    have hτ := (M.Φ (MulAut.conj k)).2
    have h1 : (M.Φ (MulAut.conj k) : G)⁻¹ * (M.e k : G) = 1 := by
      refine M.centralizer_trivial (M.A.mul_mem (M.A.inv_mem hτ) hk) fun x hx => ?_
      obtain ⟨y, rfl⟩ : ∃ y : Y, (M.e y : G) = x := ⟨M.e.symm ⟨x, hx⟩, by simp⟩
      have h2 := M.spec (MulAut.conj k) y
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      calc (M.Φ (MulAut.conj k) : G)⁻¹ * (M.e k : G) * (M.e y : G)
          = (M.Φ (MulAut.conj k) : G)⁻¹ * ((M.e k : G) * (M.e y : G) * (M.e k : G)⁻¹) *
            (M.e k : G) := by group
        _ = (M.Φ (MulAut.conj k) : G)⁻¹ * ((M.Φ (MulAut.conj k) : G) * (M.e y : G) *
            (M.Φ (MulAut.conj k) : G)⁻¹) * (M.e k : G) := by rw [h2]
        _ = (M.e y : G) * ((M.Φ (MulAut.conj k) : G)⁻¹ * (M.e k : G)) := by group
    have h3 : (M.Φ (MulAut.conj k) : G) = (M.e k : G) := inv_mul_eq_one.1 h1
    refine ⟨⟨(M.e k : G), hk⟩, (M.e k).2, ?_⟩
    have : M.Φ (MulAut.conj k) = ⟨(M.e k : G), hk⟩ := Subtype.ext h3
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← this, MulEquiv.symm_apply_apply]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

module

public import CFSG.GF2Type.Smith1979.CaseIIA0
public import CFSG.GF2Type.Smith1979.CaseIIASp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

@[expose] noncomputable def eps (t : S.O) : S.Qt →ₗ[ZMod 2] S.Qt :=
  ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1

@[expose] noncomputable def epsU (t : S.O) :
    S.Qt →ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (eps t).rangeRestrict

theorem coe_epsU (t : S.O) (x : S.Qt) :
    ((epsU t x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x := rfl

theorem epsU_surjective (t : S.O) : Function.Surjective (epsU t) :=
  (eps t).surjective_rangeRestrict

@[expose] noncomputable def secU (t : S.O) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (epsU t)
    (LinearMap.range_eq_top.mpr (epsU_surjective t)))

theorem epsU_secU (t : S.O) (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    epsU t (secU t u) = u :=
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective
    (epsU t) (LinearMap.range_eq_top.mpr (epsU_surjective t)))) u

@[expose] noncomputable def omegaU (t : S.O) :
    LinearMap.BilinForm (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  S.q.polarBilin.compl₁₂ (secU t) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype

theorem omegaU_apply (t : S.O) (u u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    omegaU t u u' = polar S.q (secU t u) (u' : S.Qt) := rfl

namespace Data

variable (D : Data S g t)
include D

theorem omegaU_epsU (x : S.Qt) (u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    omegaU t (epsU t x) u' = polar S.q x (u' : S.Qt) := by
  have h1 : secU t (epsU t x) - x ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [mem_fixSpace, map_sub]
    have h := congrArg (fun w : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) => (w : S.Qt))
      (epsU_secU t (epsU t x))
    simp only [coe_epsU] at h
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  rw [← D.commSpace_eq_fixSpace] at h1
  have h2 := polar_commSpace_eq_zero t.2 D.htt h1 u'.2
  rw [omegaU_apply, ← sub_eq_zero, ← polar_sub_left]
  exact h2

theorem omegaU_alt (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : omegaU t u u = 0 := by
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  rw [D.omegaU_epsU, coe_epsU, polar_sub_right, polar_self_eq_zero, sub_zero, polar_comm]
  have := map_sub_eq_polar t.2 x
  rw [← this]
  exact D.q_eq_zero (sub_mem_commSpace _ x)

theorem omegaU_symm (u v : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    omegaU t u v = omegaU t v u :=
  Sp.alt_symm _ D.omegaU_alt u v

theorem omegaU_nondeg : (omegaU t).Nondegenerate := by
  have hL : (omegaU t).SeparatingLeft := by
    intro u hu
    obtain ⟨x, rfl⟩ := epsU_surjective t u
    have hx : x ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 D.htt,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have := hu ⟨n, hn⟩
      rw [D.omegaU_epsU] at this
      rw [polarBilin_apply_apply, polar_comm]
      exact this
    apply Subtype.ext
    rw [coe_epsU, mem_fixSpace.mp hx, sub_self]
    rfl
  refine ⟨hL, fun u hu => hL u fun u' => ?_⟩
  rw [D.omegaU_symm]
  exact hu u'

end Data

@[expose] noncomputable def Vsub (g : G) (t : S.O) :
    Submodule (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  (Vt S g t).comap (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype

namespace Data

variable (D : Data S g t)
include D

theorem omegaU_isotropic {v v' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)} (hv : v ∈ Vsub g t)
    (hv' : v' ∈ Vsub g t) : omegaU t v v' = 0 := by
  have hvT : (v : S.Qt) ∈ Tt S g t := by rw [D.Tt_eq_Vt]; exact hv
  obtain ⟨w, hw, hwv⟩ := mem_Tt.mp hvT
  have hv_eq : v = epsU t w := Subtype.ext (by rw [coe_epsU]; exact hwv.symm)
  rw [hv_eq, D.omegaU_epsU, polar_comm]
  exact mem_Wt.mp hw v' hv'

theorem finrank_Vsub : finrank (ZMod 2) (Vsub g t) = 3 :=
  (Submodule.comapSubtypeEquivOfLe (Vt_le_commSpace D.H D.ht1)).finrank_eq.trans D.h3

theorem spData : Sp.SpData (omegaU t) (Vsub g t) where
  alt := D.omegaU_alt
  nondeg := D.omegaU_nondeg
  iso := fun _ hv _ hv' => D.omegaU_isotropic hv hv'
  finrank_W := D.finrank_commSpace
  finrank_V := D.finrank_Vsub

end Data

@[expose] noncomputable def resCt (t : S.O) :
    ↥(centralizer ({t} : Set S.O)) →*
      (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  restrictHom (S.O.subtype.comp (centralizer ({t} : Set S.O)).subtype)
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun x _ hu => apply_mem_commSpace_of_commute (mem_centralizer_singleton_iff.mp x.2) hu)

theorem coe_resCt (c : ↥(centralizer ({t} : Set S.O)))
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ((resCt t c u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt) := rfl

theorem resCt_eq_one_iff (c : ↥(centralizer ({t} : Set S.O))) :
    resCt t c = 1 ↔ ∀ u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
  restrictHom_eq_one_iff _ _ _ c

namespace Data

variable (D : Data S g t)
include D

theorem omegaU_resCt (c : ↥(centralizer ({t} : Set S.O)))
    (u u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    omegaU t (resCt t c u) (resCt t c u') = omegaU t u u' := by
  obtain ⟨x, rfl⟩ := epsU_surjective t u
  have hc : (c : S.O) * t = t * (c : S.O) := mem_centralizer_singleton_iff.mp c.2
  have e : resCt t c (epsU t x) = epsU t (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := by
    apply Subtype.ext
    rw [coe_resCt, coe_epsU, coe_epsU, map_sub, ← coe_mul_apply, ← coe_mul_apply, hc]
  rw [e, D.omegaU_epsU, D.omegaU_epsU, coe_resCt]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (c : S.O).2 x u'

@[expose] noncomputable def resR : Rbar S g t →*
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  (resCt t).comp (Subgroup.inclusion (Rbar_le_centralizer D.H.conj_mem))

theorem coe_resR (r : Rbar S g t) (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ((D.resR r u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
      ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt) := rfl

@[expose] noncomputable def Gam : Subgroup
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2] commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  D.resR.range

theorem isGamma : Sp.IsGamma (omegaU t) (Vsub g t) D.Gam where
  isom := by
    rintro _ ⟨r, rfl⟩ u v
    exact D.omegaU_resCt _ u v
  stabV := by
    rintro _ ⟨r, rfl⟩ v hv
    exact apply_mem_Vt_of_mem_Rbar D.H.conj_mem r.2 hv
  onto := by
    intro h
    let eV : Vsub g t ≃ₗ[ZMod 2] Vt S g t :=
      Submodule.comapSubtypeEquivOfLe (Vt_le_commSpace D.H D.ht1)
    let h' : Vt S g t ≃ₗ[ZMod 2] Vt S g t := (eV.symm.trans h).trans eV
    have hmem : h' ∈ RmodN S g t := by
      rw [D.hL.eq_top]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hxv⟩ := mem_RmodN.mp hmem
    refine ⟨D.resR ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, fun v => ?_⟩
    apply Subtype.ext
    have := hxv (eV v)
    have e : h' (eV v) = eV (h v) := by simp [h']
    rw [e] at this
    exact this.symm

end Data

end CFSG.GF2Type.Smith1979.Case2

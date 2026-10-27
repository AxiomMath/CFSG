module

public import CFSG.GF2Type.Smith1979.CaseIIA6Sp
public import CFSG.GF2Type.Smith1979.CaseIIA1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Data

variable (D : Data S g t)
include D

theorem epsU_of_mem (w : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : epsU t (w : S.Qt) = 0 := by
  apply Subtype.ext
  have hw : (w : S.Qt) ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← D.commSpace_eq_fixSpace]
    exact w.2
  rw [coe_epsU, mem_fixSpace.mp hw, sub_self]
  rfl

theorem exists_goodSec : ∃ σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt,
    (∀ u, epsU t (σ u) = u) ∧ ∀ u, S.q (σ u) = 0 := by
  classical
  let Φ : QuadraticMap (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) (ZMod 2) :=
    S.q.comp (secU t)
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Φ
  have hBu : ∀ u, B u u = S.q (secU t u) := fun u => by
    have := congrArg (fun Q => Q u) hB
    simpa [Φ] using this
  let Θ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2]
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ((omegaU t).toDual D.omegaU_nondeg).symm.toLinearMap ∘ₗ B.flip
  have hΘ : ∀ u v, omegaU t (Θ v) u = B u v := fun u v =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := D.omegaU_nondeg) (B.flip v) u
  refine ⟨secU t + (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)).subtype ∘ₗ Θ, fun u => ?_,
    fun u => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add]
    rw [epsU_secU, D.epsU_of_mem, add_zero]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [QuadraticMap.map_add S.q (secU t u)]
    have h1 : S.q ((Θ u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) = 0 :=
      D.q_eq_zero (Θ u).2
    have h2 : polar S.q (secU t u) ((Θ u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
        S.q (secU t u) := by
      have e1 : polar S.q (secU t u) ((Θ u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) =
          omegaU t u (Θ u) := rfl
      rw [e1, D.omegaU_symm, hΘ u u, hBu]
    rw [h1, h2, add_zero]
    exact Sp.zmod2_add_self _

theorem resCt_t : resCt t (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ :
    ↥(centralizer ({t} : Set S.O))) = 1 := by
  rw [resCt_eq_one_iff]
  intro u hu
  rw [D.commSpace_eq_fixSpace] at hu
  exact mem_fixSpace.mp hu

end Data

@[expose] noncomputable def dmap
    (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
    (c : ↥(centralizer ({t} : Set S.O))) :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt :=
  (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ∘ₗ σ ∘ₗ
      (((resCt t c).symm : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
          commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2]
            commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) - σ

theorem dmap_apply (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
    (c : ↥(centralizer ({t} : Set S.O))) (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    dmap σ c u = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ ((resCt t c).symm u)) - σ u := rfl

@[expose] noncomputable def Bd (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
    (c : ↥(centralizer ({t} : Set S.O))) :
    LinearMap.BilinForm (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  S.q.polarBilin.compl₁₂ σ (dmap σ c)

theorem Bd_apply (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
    (c : ↥(centralizer ({t} : Set S.O))) (u u' : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    Bd σ c u u' = polar S.q (σ u) (dmap σ c u') := rfl

namespace Data

variable (D : Data S g t) (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
  (hσ : ∀ u, epsU t (σ u) = u) (hσq : ∀ u, S.q (σ u) = 0)
include D hσ

theorem polar_sigma (u w : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    polar S.q (σ u) (w : S.Qt) = omegaU t u w := by
  have := D.omegaU_epsU (σ u) w
  rw [hσ u] at this
  exact this.symm

theorem t_sigma (w : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ w) = σ w + (w : S.Qt) := by
  have h := congrArg Subtype.val (hσ w)
  rw [coe_epsU] at h
  have e : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ w) =
      σ w + ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ w) - σ w) := by abel
  rw [e, h]

theorem c_resCt_symm (c : ↥(centralizer ({t} : Set S.O)))
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((resCt t c).symm u : commSpace
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) = (u : S.Qt) := by
  have := coe_resCt c ((resCt t c).symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem dmap_mem (c : ↥(centralizer ({t} : Set S.O)))
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    dmap σ c u ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  suffices h : dmap σ c u ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) by
    rwa [← D.commSpace_eq_fixSpace] at h
  rw [mem_fixSpace]
  have hc : (c : S.O) * t = t * (c : S.O) := mem_centralizer_singleton_iff.mp c.2
  have hct : ∀ x : S.Qt, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x) =
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) x) := fun x => by
    rw [← coe_mul_apply, ← coe_mul_apply, hc]
  have h1 := D.t_sigma σ hσ ((resCt t c).symm u)
  have h2 := D.t_sigma σ hσ u
  have h3 := D.c_resCt_symm σ hσ c u
  rw [dmap_apply]
  generalize (resCt t c).symm u = w at h1 h3 ⊢
  generalize ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = C at hct h3 ⊢
  rw [map_sub (t : S.Qt ≃ₗ[ZMod 2] S.Qt), hct, h1, h2, map_add C, h3]
  abel

include hσq in
theorem Bd_alt (c : ↥(centralizer ({t} : Set S.O))) (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    Bd σ c u u = 0 := by
  have hd := D.dmap_mem σ hσ c u
  have hx : σ u + dmap σ c u = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ ((resCt t c).symm u)) := by
    rw [dmap_apply]
    abel
  have e1 := QuadraticMap.map_add S.q (σ u) (dmap σ c u)
  rw [hx, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (c : S.O).2, hσq, hσq,
    D.q_eq_zero hd, zero_add, zero_add] at e1
  exact e1.symm

theorem polar_sigma_apply (c : ↥(centralizer ({t} : Set S.O)))
    (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) (d : S.Qt)
    (hd : d ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    polar S.q (σ u) (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d) =
      polar S.q (σ ((resCt t c).symm u)) d := by
  have e1 : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d =
      ((resCt t c ⟨d, hd⟩ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt) :=
    (coe_resCt c ⟨d, hd⟩).symm
  have e2 := D.omegaU_resCt c ((resCt t c).symm u) ⟨d, hd⟩
  rw [LinearEquiv.apply_symm_apply] at e2
  rw [e1, D.polar_sigma σ hσ u, e2]
  exact (D.polar_sigma σ hσ ((resCt t c).symm u) ⟨d, hd⟩).symm

end Data

theorem aux_sub_add {A : Type*} [AddCommGroup A] (X Y s : A) : X - s = (Y - s) + (X - Y) := by
  abel

namespace Data

variable (D : Data S g t) (σ : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2] S.Qt)
  (hσ : ∀ u, epsU t (σ u) = u)
include D hσ

theorem Bd_mul (c c' : ↥(centralizer ({t} : Set S.O))) :
    Bd σ (c * c') = Bd σ c + (Bd σ c').compl₁₂
      (((resCt t c).symm : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
          commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2]
            commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (((resCt t c).symm : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≃ₗ[ZMod 2]
        commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
          commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →ₗ[ZMod 2]
            commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  refine LinearMap.ext fun u => LinearMap.ext fun u' => ?_
  have hs : (resCt t (c * c')).symm u' = (resCt t c').symm ((resCt t c).symm u') := by
    rw [LinearEquiv.symm_apply_eq, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hmul : ∀ y : S.Qt, (((c * c' : ↥(centralizer ({t} : Set S.O))) : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) y = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((c' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y) := fun y =>
    coe_mul_apply (c : S.O) (c' : S.O) y
  have h1 : dmap σ (c * c') u' = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((c' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ ((resCt t c').symm ((resCt t c).symm u')))) -
        σ u' :=
    (dmap_apply σ (c * c') u').trans
      ((congrArg (fun x : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =>
        (((c * c' : ↥(centralizer ({t} : Set S.O))) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ x) -
          σ u') hs).trans
        (congrArg (fun y => y - σ u') (hmul _)))
  have h2 : dmap σ c u' = ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ ((resCt t c).symm u')) - σ u' :=
    dmap_apply σ c u'
  have h3 : dmap σ c' ((resCt t c).symm u') = ((c' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (σ ((resCt t c').symm ((resCt t c).symm u'))) - σ ((resCt t c).symm u') :=
    dmap_apply σ c' ((resCt t c).symm u')
  have e3 : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (dmap σ c' ((resCt t c).symm u')) =
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((c' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (σ ((resCt t c').symm ((resCt t c).symm u')))) -
      ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (σ ((resCt t c).symm u')) :=
    (congrArg (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h3).trans
      (map_sub ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ _)
  have hkey : dmap σ (c * c') u' =
      dmap σ c u' + ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (dmap σ c' ((resCt t c).symm u')) :=
    h1.trans ((aux_sub_add _ (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (σ ((resCt t c).symm u'))) (σ u')).trans
      (congrArg₂ (· + ·) h2.symm e3.symm))
  have hp := D.polar_sigma_apply σ hσ c u _ (D.dmap_mem σ hσ c' ((resCt t c).symm u'))
  show polar S.q (σ u) (dmap σ (c * c') u') =
    polar S.q (σ u) (dmap σ c u') +
      polar S.q (σ ((resCt t c).symm u)) (dmap σ c' ((resCt t c).symm u'))
  exact (congrArg (polar S.q (σ u)) hkey).trans
    ((polar_add_right S.q (σ u) _ _).trans (congrArg₂ (· + ·) rfl hp))

theorem dmap_one : dmap σ (1 : ↥(centralizer ({t} : Set S.O))) = 0 := by
  refine LinearMap.ext fun u => ?_
  rw [dmap_apply]
  have e1 : (resCt t (1 : ↥(centralizer ({t} : Set S.O)))).symm u = u := by
    rw [map_one]
    rfl
  have e2 : (((1 : ↥(centralizer ({t} : Set S.O))) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := rfl
  rw [e1, e2]
  exact sub_self _

theorem Bd_one : Bd σ (1 : ↥(centralizer ({t} : Set S.O))) = 0 := by
  refine LinearMap.ext fun u => LinearMap.ext fun u' => ?_
  rw [Bd_apply, D.dmap_one σ hσ]
  simp

theorem dmap_t (u : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    dmap σ (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({t} : Set S.O))) u =
      (u : S.Qt) := by
  rw [dmap_apply, D.resCt_t]
  have h := congrArg Subtype.val (hσ u)
  rw [coe_epsU] at h
  exact h

theorem Bd_t : Bd σ (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ :
    ↥(centralizer ({t} : Set S.O))) = omegaU t := by
  refine LinearMap.ext fun u => LinearMap.ext fun u' => ?_
  rw [Bd_apply, D.dmap_t σ hσ u']
  exact D.polar_sigma σ hσ u u'

end Data

namespace Data

variable (D : Data S g t)
include D

theorem exists_chi : ∃ χ : ↥(centralizer ({t} : Set S.O)) →* Multiplicative (ZMod 2),
    χ ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ = Multiplicative.ofAdd 1 := by
  obtain ⟨σ, hσ, hσq⟩ := D.exists_goodSec
  obtain ⟨τ, hτadd, hτω, hτinv⟩ :=
    Sp.exists_halfTrace D.omegaU_alt D.omegaU_nondeg D.finrank_commSpace
  have hτ0 : τ 0 = 0 := by
    have h := hτadd 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  refine ⟨{ toFun := fun c => Multiplicative.ofAdd (τ (Bd σ c))
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · show Multiplicative.ofAdd (τ (Bd σ 1)) = 1
    rw [D.Bd_one σ hσ, hτ0]
    rfl
  · intro c c'
    show Multiplicative.ofAdd (τ (Bd σ (c * c'))) =
      Multiplicative.ofAdd (τ (Bd σ c)) * Multiplicative.ofAdd (τ (Bd σ c'))
    have hiso : ∀ u v, omegaU t ((resCt t c).symm u) ((resCt t c).symm v) = omegaU t u v := by
      intro u v
      have h := D.omegaU_resCt c ((resCt t c).symm u) ((resCt t c).symm v)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
      exact h.symm
    rw [D.Bd_mul σ hσ c c', hτadd, hτinv (resCt t c).symm hiso (Bd σ c')
      (D.Bd_alt σ hσ hσq c')]
    rfl
  · show Multiplicative.ofAdd (τ (Bd σ ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩)) =
      Multiplicative.ofAdd 1
    rw [D.Bd_t σ hσ, hτω]

end Data

end CFSG.GF2Type.Smith1979.Case2

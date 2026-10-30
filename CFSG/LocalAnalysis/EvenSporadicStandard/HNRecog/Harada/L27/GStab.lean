module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRStab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

@[expose] def CzS5 (t z : G) (R0 : Subgroup G) : Prop :=
  ∃ ψ : ↥(centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) →* Equiv.Perm (Fin 5),
    Function.Surjective ψ ∧
      ψ.ker = R0.subgroupOf (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))

theorem Czgrp_le_Ngrp (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) :
    centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤ Ngrp h := by
  intro c hc
  obtain ⟨hct, hcz⟩ := Subgroup.mem_inf.mp hc
  have hct' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hct
  have hcz' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcz
  have hczc : c * z * c⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcz'
  have hmem : c ∈ normalizer ((zpowers t ⊔ zpowers z : Subgroup G) : Set G) :=
    mem_normalizer_V_of_conj h.t_sq h.z_sq h.t_mul_z_comm hczc
      (Or.inl (mul_inv_eq_iff_eq_mul.mpr hct'))
  exact ((mem_normalizer_V_iff_mem_normalizer_Rgrp h hzt htz).mp hmem).1

theorem exists_conj_t_mul_z (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) : ∃ r ∈ Rgrp h, r * t * r⁻¹ = t * z := by
  by_contra hcon
  push Not at hcon
  have htr : t ∈ Rgrp h := Setting25.t_mem_Rgrp h
  have hcentral : ∀ r ∈ Rgrp h, r * t = t * r := by
    intro r hr
    rcases Rgrp_conj_t h hr with hconj | hconj
    · exact mul_inv_eq_iff_eq_mul.mp hconj
    · exact absurd hconj (hcon r hr)
  have htzp : t ∈ zpowers z :=
    Rgrp_center_le h htr (fun y hy => (hcentral y hy).symm)
  have hw0 : wvec h = 0 := by
    show toW h t (Setting25.t_mem_Rgrp h) = 0
    exact (toW_eq_zero_iff h (Setting25.t_mem_Rgrp h)).2 htzp
  exact wvec_ne_zero h hzt htz hw0

theorem Rgrp_inf_centralizer_t (h : Setting25 G t z z₁ ι zv R0 F) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) : Rgrp h ⊓ centralizer ({t} : Set G) = R0 := by
  have hRz : Rgrp h ≤ centralizer ({z} : Set G) :=
    fun x hx => (Subgroup.mem_inf.mp (Rgrp_le_K h hx)).2
  have hsplit : Rgrp h ⊓ centralizer ({t} : Set G) =
      Rgrp h ⊓ (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, hx.2, hRz hx.1⟩
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
  rw [hsplit, ← Dgrp_eq_Rgrp h hzt htz, Dgrp_inf_C h hzt htz]

@[expose] noncomputable def Pgrp (h : Setting25 G t z z₁ ι zv R0 F) : Subgroup ↥(Xgrp h) :=
  ((centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)).subgroupOf (Ngrp h)).map
    (rho0 h).rangeRestrict

theorem Pgrp_fix (h : Setting25 G t z z₁ ι zv R0 F) :
    ∀ g ∈ Pgrp h, ((rhoX h g : Wsp h ≃ₗ[ZMod 2] Wsp h)) (wvec h) = wvec h := by
  intro g hg
  simp only [Pgrp, Subgroup.mem_map] at hg
  obtain ⟨c, hc, rfl⟩ := hg
  rw [Subgroup.mem_subgroupOf] at hc
  have hct : (c : G) * t = t * (c : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1
  have hconj : (c : G) * t * (c : G)⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hct
  have hkey : ((rhoX h ((rho0 h).rangeRestrict c) : Wsp h ≃ₗ[ZMod 2] Wsp h)) =
      ((rho0 h c : TauCeti.QuadraticMap.orthogonalGroup (qW h)) :
        Wsp h ≃ₗ[ZMod 2] Wsp h) := rfl
  rw [hkey, show wvec h = toW h t (Setting25.t_mem_Rgrp h) from rfl,
    rho0_toW h c (Setting25.t_mem_Rgrp h)]
  exact (toW_eq_toW_iff h (conj_mem_Rgrp h c.2 (Setting25.t_mem_Rgrp h))
    (Setting25.t_mem_Rgrp h)).2 (by rw [hconj]; simp)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27

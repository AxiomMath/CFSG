module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GFpf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GLaC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.A5Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private theorem rhoX_injective (h : Setting25 G t z z₁ ι zv R0 F) :
    Function.Injective (rhoX h) := by
  have h1 : Function.Injective (Subgroup.subtype (Xgrp h)) := Subgroup.subtype_injective _
  have h2 : Function.Injective
      (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup (qW h))) :=
    Subgroup.subtype_injective _
  simpa [rhoX] using h2.comp h1

theorem ker_vbar_eq_A0W (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) :
    LinearMap.ker (((rhoX h (vbar h hn) : Wsp h ≃ₗ[ZMod 2] Wsp h) : Wsp h →ₗ[ZMod 2] Wsp h) -
      LinearMap.id) = A0W h := by
  haveI hfin : FiniteDimensional (ZMod 2) (Wsp h) := Module.Finite.of_finite
  obtain ⟨e⟩ := Fbar_iso h hn hnz
  obtain ⟨x, hx⟩ := exists_orderOf_eq_five_a5
  let fbar : ↥(Fbar h n) := e.symm x
  have hfbar5 : orderOf fbar = 5 := by
    have h1 : orderOf (e fbar) = orderOf fbar := e.orderOf_eq fbar
    have h2 : e fbar = x := e.apply_symm_apply x
    rw [h2, hx] at h1
    exact h1.symm
  have hord : orderOf (fbar : ↥(Xgrp h)) = 5 := (Subgroup.orderOf_coe fbar).trans hfbar5
  let σ : Wsp h ≃ₗ[ZMod 2] Wsp h := rhoX h (vbar h hn)
  let f : Wsp h ≃ₗ[ZMod 2] Wsp h := rhoX h (fbar : ↥(Xgrp h))
  have hσ : σ * σ = 1 := by
    show rhoX h (vbar h hn) * rhoX h (vbar h hn) = 1
    rw [← map_mul, vbar_mul_self h hn, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    dsimp only [σ] at h1
    apply vbar_ne_one h hn hnz
    exact rhoX_injective h (by rw [h1, map_one])
  have hcoe : (fbar : ↥(Xgrp h)) ^ 5 = 1 := by
    simpa [hord] using pow_orderOf_eq_one (fbar : ↥(Xgrp h))
  have hf5 : f ^ 5 = 1 := by
    show (rhoX h (fbar : ↥(Xgrp h))) ^ 5 = 1
    rw [← map_pow, hcoe, map_one]
  have hfσ : f * σ = σ * f := by
    show rhoX h (fbar : ↥(Xgrp h)) * rhoX h (vbar h hn) =
      rhoX h (vbar h hn) * rhoX h (fbar : ↥(Xgrp h))
    rw [← map_mul, ← map_mul, Fbar_comm h hn hnz (fbar : ↥(Xgrp h)) fbar.2]
  have hfpf : ∀ y : Wsp h, f y = y → y = 0 := fun y hy =>
    Fbar_fpf h hn hnz (fbar : ↥(Xgrp h)) fbar.2 hord y hy
  have hker : Module.finrank (ZMod 2)
      (LinearMap.ker ((σ : Wsp h →ₗ[ZMod 2] Wsp h) - LinearMap.id)) = 4 :=
    finrank_ker_involution_eq_four (hdim := finrank_Wsp h) σ hσ hσ1 f hf5 hfσ hfpf
  have hle : A0W h ≤ LinearMap.ker ((σ : Wsp h →ₗ[ZMod 2] Wsp h) - LinearMap.id) := by
    intro u hu
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact A0W_fixed_by_vbar h hn hu
  have heq : A0W h = LinearMap.ker ((σ : Wsp h →ₗ[ZMod 2] Wsp h) - LinearMap.id) :=
    Submodule.eq_of_le_of_finrank_eq hle ((finrank_A0W h).trans hker.symm)
  change LinearMap.ker ((σ : Wsp h →ₗ[ZMod 2] Wsp h) - LinearMap.id) = A0W h
  exact heq.symm

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27

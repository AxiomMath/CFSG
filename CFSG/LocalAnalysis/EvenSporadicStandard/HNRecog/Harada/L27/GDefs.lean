module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NRCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.EvenSporadicStandard.HNRecog
  CFSG.RankThree.Literature.FSmith

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G}

abbrev Ngrp (h : Setting25 G t z z₁ ι zv R0 F) : Subgroup G := normalizer (Rgrp h : Set G)

abbrev Qsub (h : Setting25 G t z z₁ ι zv R0 F) : Subgroup ↥(Ngrp h) :=
  (Rgrp h).subgroupOf (Ngrp h)

theorem Rgrp_le_Ngrp (h : Setting25 G t z z₁ ι zv R0 F) : Rgrp h ≤ Ngrp h :=
  Subgroup.le_normalizer

theorem conj_mem_Rgrp (h : Setting25 G t z z₁ ι zv R0 F) {g : G} (hg : g ∈ Ngrp h) {x : G}
    (hx : x ∈ Rgrp h) : g * x * g⁻¹ ∈ Rgrp h :=
  (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx

theorem isPlusExtraspecial_subgroupOf {Γ : Type*} [Group Γ] {m : ℕ} {D N : Subgroup Γ}
    (hDN : D ≤ N) (hD : IsPlusExtraspecial m D) : IsPlusExtraspecial m (D.subgroupOf N) := by
  obtain ⟨hExt, hcard, E, hED, hEel, hEcard⟩ := hD
  have hEN : E ≤ N := hED.trans hDN
  refine ⟨TwoHSData.isExtraspecial_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hDN).symm hExt, ?_,
    E.subgroupOf N, fun x hx => hED hx, ⟨?_, ?_⟩, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv]
    exact hcard
  · refine ⟨⟨fun x y => ?_⟩⟩
    have hc := hEel.1.is_comm.comm (⟨((x : N) : Γ), Subgroup.mem_subgroupOf.mp x.2⟩ : E)
      ⟨((y : N) : Γ), Subgroup.mem_subgroupOf.mp y.2⟩
    have hc' : ((x : N) : Γ) * ((y : N) : Γ) = ((y : N) : Γ) * ((x : N) : Γ) :=
      congrArg Subtype.val hc
    exact Subtype.ext (Subtype.ext hc')
  · intro x hx
    have h1 := hEel.2 (x : Γ) (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa using h1)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]
    exact hEcard

theorem isPlusExtraspecial_Qsub (h : Setting25 G t z z₁ ι zv R0 F) :
    IsPlusExtraspecial 4 (Qsub h) :=
  isPlusExtraspecial_subgroupOf (Rgrp_le_Ngrp h) (isPlusExtraspecial_Rgrp h)

theorem centralizer_Qsub_le (h : Setting25 G t z z₁ ι zv R0 F) :
    centralizer ((Qsub h : Subgroup ↥(Ngrp h)) : Set ↥(Ngrp h)) ≤ Qsub h := by
  intro g hg
  have hgC : (g : G) ∈ centralizer (Rgrp h : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (⟨y, Rgrp_le_Ngrp h hy⟩ : ↥(Ngrp h)) ∈
        ((Qsub h : Subgroup ↥(Ngrp h)) : Set ↥(Ngrp h)) := Subgroup.mem_subgroupOf.2 hy
    have := Subgroup.mem_centralizer_iff.mp hg ⟨y, Rgrp_le_Ngrp h hy⟩ hy'
    exact congrArg Subtype.val this
  rw [centralizer_Rgrp_eq h] at hgC
  exact Subgroup.mem_subgroupOf.2 (Subgroup.zpowers_le.2 (z_mem_Rgrp h) hgC)

instance instFiniteQsub (h : Setting25 G t z z₁ ι zv R0 F) : Finite (Qsub h) :=
  (isPlusExtraspecial_Qsub h).finite

noncomputable instance instModuleWsp (h : Setting25 G t z z₁ ι zv R0 F) :
    Module (ZMod 2) (Additive (Abelianization (Qsub h))) :=
  CFSG.GroupTheory.extraspecialQuotientModule (isPlusExtraspecial_Qsub h).isExtraspecialPGroup

abbrev Wsp (h : Setting25 G t z z₁ ι zv R0 F) : Type := Additive (Abelianization (Qsub h))

instance instFiniteWsp (h : Setting25 G t z z₁ ι zv R0 F) : Finite (Wsp h) := by
  change Finite (Qsub h ⧸ _root_.commutator (Qsub h))
  infer_instance

noncomputable abbrev qW (h : Setting25 G t z z₁ ι zv R0 F) : QuadraticForm (ZMod 2) (Wsp h) :=
  extraspecialQuadForm (isPlusExtraspecial_Qsub h).isExtraspecialPGroup

@[expose] noncomputable def rho0 (h : Setting25 G t z z₁ ι zv R0 F) :
    ↥(Ngrp h) →* TauCeti.QuadraticMap.orthogonalGroup (qW h) :=
  extraspecialConjOrth (isPlusExtraspecial_Qsub h).isExtraspecialPGroup
    (inferInstance : (Qsub h).Normal)

noncomputable abbrev Xgrp (h : Setting25 G t z z₁ ι zv R0 F) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup (qW h)) :=
  (rho0 h).range

@[expose] noncomputable def rhoX (h : Setting25 G t z z₁ ι zv R0 F) :
    ↥(Xgrp h) →* (Wsp h ≃ₗ[ZMod 2] Wsp h) :=
  (TauCeti.QuadraticMap.orthogonalGroup (qW h)).subtype.comp (Xgrp h).subtype

@[expose] noncomputable def toW (h : Setting25 G t z z₁ ι zv R0 F) (x : G) (hx : x ∈ Rgrp h) :
    Wsp h :=
  Additive.ofMul (Abelianization.of
    (⟨⟨x, Rgrp_le_Ngrp h hx⟩, (Subgroup.mem_subgroupOf).2 hx⟩ : Qsub h))

@[expose] noncomputable def wvec (h : Setting25 G t z z₁ ι zv R0 F) : Wsp h :=
  toW h t (Setting25.t_mem_Rgrp h)

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27

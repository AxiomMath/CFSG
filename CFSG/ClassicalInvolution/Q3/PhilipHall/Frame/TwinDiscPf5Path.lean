module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf4Conn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Path

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {H : Subgroup Y}

theorem secPath_of_dstarComp {A B : Subgroup Y} (h : B ∈ dstarComp Ω A) : SecPath Ω H A B := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    rename_i b d
    refine ih.tail ⟨hbc.1, Or.inl ⟨1, H.one_mem, ?_⟩⟩
    rcases hbc.2 with h1 | h1
    · exact Or.inr (Or.inl (by rwa [conjSub_one]))
    · exact Or.inr (Or.inr (by rwa [conjSub_one]))

theorem secPath_tail_conj {A J M : Subgroup Y} (hp : SecPath Ω H A J) (hM : M ∈ Ω) {n : Y}
    (hn : n ∈ H) (h : M = conjSub n J) : SecPath Ω H A M :=
  hp.tail ⟨hM, Or.inr ⟨n, hn, Or.inl h.symm⟩⟩

end Path

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem coreAt_le_rLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    TwinADescent.coreAt c J ≤ rLayer Ω c := by
  unfold TwinADescent.coreAt tightCore
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxK : x ∈ TwinADescent.coreAt c J := Subgroup.subset_closure hx
  obtain ⟨P, hP, hxP⟩ := IsSylow2In.exists_ge (T := Subgroup.zpowers x)
    (P := TwinADescent.coreAt c J) hx.2 (Subgroup.zpowers_le.mpr hxK)
  have hPJ : IsSylow2In P J := ((TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mp hP).1
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) :=
    hP.1.trans (TwinADescent.coreAt_le_centralizer c J)
  have hxP' : x ∈ P := hxP (Subgroup.mem_zpowers x)
  have hle : P ≤ rLayer Ω c := by
    unfold rLayer
    exact le_iSup₂_of_le P (mem_RSet_of_isSylow2In hJ.1 hPJ)
      (le_iSup (fun _ : P ≤ Subgroup.centralizer ({c} : Set G) => P) hPc)
  exact hle hxP'

theorem coreHull_map_le_rLayer (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype ≤ rLayer Ω c := by
  unfold coreHull
  rw [Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  obtain ⟨_, ⟨J, hJ, rfl⟩, hLC, rfl⟩ := hL
  rw [Subgroup.map_subgroupOf_eq_of_le hLC]
  exact coreAt_le_rLayer hΩ hc2 hJ

end Layer

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem eq_conjSub_of_hull_eq (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J M : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hM : M ∈ tqMembers3 Ω c)
    (g : ↥(coreHull Ω c))
    (h : ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
        (coreHull Ω c) =
      conjSub g (((TwinADescent.coreAt c J).subgroupOf
        (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c))) :
    M = conjSub (((g : ↥(Subgroup.centralizer ({c} : Set G))) : G)) J := by
  have hnC : ((g : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ Subgroup.centralizer ({c} : Set G) := (g : ↥(Subgroup.centralizer ({c} : Set G))).2
  rw [conjSub_subgroupOf (coreHull Ω c) g ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)))] at h
  have hle2 : conjSub (g : ↥(Subgroup.centralizer ({c} : Set G))) ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))) ≤ coreHull Ω c := by
    have := conjSub_mono (n := (g : ↥(Subgroup.centralizer ({c} : Set G)))) (le_coreHull hJ)
    rwa [conjSub_eq_self_of_mem g.2] at this
  have h4 : (TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G)) =
      conjSub (g : ↥(Subgroup.centralizer ({c} : Set G))) ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    have := congrArg (Subgroup.map (coreHull Ω c).subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_coreHull hM),
      Subgroup.map_subgroupOf_eq_of_le hle2] at this
  have h5 : conjSub (g : ↥(Subgroup.centralizer ({c} : Set G))) ((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))) =
      (TwinADescent.coreAt c (conjSub ((g : ↥(Subgroup.centralizer ({c} : Set G))) : G) J)).subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    rw [conjSub_subgroupOf (Subgroup.centralizer ({c} : Set G)) (g : ↥(Subgroup.centralizer ({c} : Set G))) (TwinADescent.coreAt c J),
      TwinADescent.conjSub_coreAt hnC J]
  have h6 : TwinADescent.coreAt c M = TwinADescent.coreAt c (conjSub ((g : ↥(Subgroup.centralizer ({c} : Set G))) : G) J) := by
    have := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set G)).subtype) (h4.trans h5)
    rwa [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c M),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c _)] at this
  exact eq_of_coreAt_eq hΩ hc2 hM (conjSub_mem_tqMembers3 hΩ.conjInvariant hnC hJ) h6

theorem secPath_of_connected (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c) {H : Subgroup G}
    (hH : oddCoreOf (Subgroup.centralizer ({c} : Set G)) ≤ H)
    (hconn : ∀ M ∈ secFam Ω c, M ∈ dstarComp (secFam Ω c) (secImg Ω c B)) :
    ∀ M ∈ tqMembers3 Ω c, SecPath Ω H B M := by
  intro M hM
  obtain ⟨n, hn, J', hJ', hJ'B, hMn⟩ := exists_conj_tq_of_connected hΩ hc2 hB hconn M hM
  exact secPath_tail_conj (secPath_of_dstarComp hJ'B) hM.1 (hH hn) hMn

theorem secPath_of_transitive (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c) {H : Subgroup G}
    (hH : (coreHull Ω c).map (Subgroup.centralizer ({c} : Set G)).subtype ≤ H)
    (horb : ∀ M ∈ secFam Ω c, ∃ y, conjSub y (secImg Ω c B) = M) :
    ∀ M ∈ tqMembers3 Ω c, SecPath Ω H B M := by
  intro M hM
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set X := coreHull Ω c with hX
  set N₀ : Subgroup ↥X := classicalInvolutionOddCore ↥X with hN₀def
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hΛ : HypOmegaGen (hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  obtain ⟨y, hy⟩ := horb _ (secImg_mem_secFam hM)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ y
  have hBΛ := subgroupOf_mem_hullFam hB
  have hMΛ := subgroupOf_mem_hullFam hM
  have himg : (conjSub x (((TwinADescent.coreAt c B).subgroupOf C).subgroupOf X)).map
      (QuotientGroup.mk' N₀) =
      (((TwinADescent.coreAt c M).subgroupOf C).subgroupOf X).map (QuotientGroup.mk' N₀) := by
    rw [AscQuot.map_conjSub]
    exact hy
  obtain ⟨n, hn, hn'⟩ := Q3T6.exists_conj_of_map_eq_gen hΛ hN₀odd
    (hΛ.conjInvariant x _ hBΛ) hMΛ himg
  rw [← conjSub_mul] at hn'
  have hMB := eq_conjSub_of_hull_eq hΩ hc2 hB hM (n * x) hn'
  exact secPath_tail_conj Relation.ReflTransGen.refl hM.1
    (hH ⟨_, (n * x).2, rfl⟩) hMB

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

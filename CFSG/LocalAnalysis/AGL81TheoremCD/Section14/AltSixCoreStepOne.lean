module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Chief
public import Mathlib.GroupTheory.IsPerfect
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CentExt
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.GroupTheory.PerfectCoverProduct
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup
open scoped commutatorElement
open CFSG.GH74.GLS.Stage2.Signalizer.L53

variable {K : Type*} [Group K]

theorem eq_top_of_sup_eq_top_of_isSolvable [Group.IsPerfect K] {C N : Subgroup K} [C.Normal]
    (hN : IsSolvable N) (h : N ⊔ C = ⊤) : C = ⊤ := by
  classical
  letI : Group.IsSolvable ↥N := hN
  let π : K →* K ⧸ C := QuotientGroup.mk' C
  have hmap : N.map π = ⊤ := by
    have hsup : (N ⊔ C).map π = ⊤ := by
      rw [h, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective C)]
    rw [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff C).mpr (le_of_eq (QuotientGroup.ker_mk' C).symm),
      sup_bot_eq] at hsup
    exact hsup
  have hsurj : Function.Surjective (π.comp N.subtype) := by
    intro q
    have hq : q ∈ N.map π := by rw [hmap]; exact Subgroup.mem_top q
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨n, hn⟩, rfl⟩
  haveI : Group.IsSolvable (K ⧸ C) := Group.isSolvable_of_surjective hsurj
  have hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ :=
    Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect ↥(⊤ : Subgroup K))
  exact top_le_iff.mp
    (Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := C) hperf)

theorem stabSec_normal {X Y : Subgroup K} (hX : X.Normal) (hY : Y.Normal) :
    (stabSec X Y hY).Normal where
  conj_mem := by
    intro m hm g
    rw [mem_stabSec] at hm ⊢
    intro x hx
    have e : ⁅x, g * m * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, m⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hY.conj_mem _ (hm _ (by simpa using hX.conj_mem x hx g⁻¹)) g

private theorem le_stabSec_of_le_centralizer {S M M₀ Y : Subgroup K} (hM₀ : M₀.Normal)
    (hY : Y ≤ Subgroup.centralizer (S : Set K)) (hSM₀ : S ⊔ M₀ = M) :
    Y ≤ stabSec M M₀ hM₀ := by
  intro y hy
  rw [mem_stabSec]
  intro x hx
  have hx' : x ∈ S ⊔ M₀ := hSM₀.symm ▸ hx
  obtain ⟨s, hs, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hsy : s * y = y * s := Subgroup.mem_centralizer_iff.mp (hY hy) s hs
  have hcomm1 : ⁅s, y⁆ = 1 := by
    rw [commutatorElement_def, hsy]
    group
  have hcomm_m : ⁅m, y⁆ ∈ M₀ := by
    have hconj : y * m⁻¹ * y⁻¹ ∈ M₀ := hM₀.conj_mem m⁻¹ (M₀.inv_mem hm) y
    have e : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact M₀.mul_mem hm hconj
  have e : ⁅s * m, y⁆ = s * ⁅m, y⁆ * s⁻¹ * ⁅s, y⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, hcomm1, mul_one]
  exact hM₀.conj_mem _ hcomm_m s

variable [Finite K]

private theorem isMinimalNormal_map_mk {X Y : Subgroup K} [Y.Normal]
    (hXY : IsChiefPair X Y) [Hn : (X.map (QuotientGroup.mk' Y)).Normal] :
    CFSG.IsMinimalNormal (X.map (QuotientGroup.mk' Y)) := by
  classical
  let π : K →* K ⧸ Y := QuotientGroup.mk' Y
  have hYX : Y ≤ X := hXY.2.2.1.le
  refine ⟨fun Z hZn hZH => ?_⟩
  let L : Subgroup K := Z.comap π
  have hLn : L.Normal := hZn.comap π
  have hYL : Y ≤ L := by
    intro y hy
    rw [Subgroup.mem_comap]
    have hy' : π y = 1 := by
      simpa [π] using (QuotientGroup.eq_one_iff y).mpr hy
    rw [hy']
    exact Z.one_mem
  have hLX : L ≤ X := by
    have h1 : L ≤ Subgroup.comap π (X.map π) := Subgroup.comap_mono hZH
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hYX] at h1
  have hLmap : Subgroup.map π L = Z :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) Z
  rcases hXY.2.2.2 L hLn hYL hLX with hL | hL
  · left
    rw [← hLmap, hL]
    exact (Subgroup.map_eq_bot_iff Y).mpr (le_of_eq (QuotientGroup.ker_mk' Y).symm)
  · right
    rw [← hLmap, hL]

private theorem sup_eq_of_map_eq_map_of_ker_eq {G N : Type*} [Group G] [Group N] {f : G →* N}
    {P X Y : Subgroup G} (hker : f.ker = Y) (hYX : Y ≤ X) (h : P.map f = X.map f) :
    P ⊔ Y = X := by
  have h' : P ⊔ f.ker = X ⊔ f.ker := Subgroup.map_eq_map_iff.mp h
  rw [hker, sup_eq_left.mpr hYX] at h'
  exact h'

theorem exists_isPGroup_sup_eq_of_isChiefPair {X Y : Subgroup K}
    (hXY : CFSG.GH74.GLS.Stage2.Signalizer.L53.IsChiefPair X Y) (hX : IsSolvable X) :
    ∃ r : ℕ, r.Prime ∧ ∃ S : Subgroup K, S ≤ X ∧ IsPGroup r S ∧ S ⊔ Y = X := by
  classical
  letI : Y.Normal := hXY.2.1
  let π : K →* K ⧸ Y := QuotientGroup.mk' Y
  let H : Subgroup (K ⧸ Y) := X.map π
  letI : H.Normal := hXY.1.map π (QuotientGroup.mk'_surjective Y)
  have hHmin : CFSG.IsMinimalNormal H := isMinimalNormal_map_mk hXY
  letI : CFSG.IsMinimalNormal H := hHmin
  have hYX : Y ≤ X := hXY.2.2.1.le
  let f : ↥X →* ↥H :=
    { toFun := fun x => ⟨π x, Subgroup.mem_map_of_mem π x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨x, hxX, hx⟩ := Subgroup.mem_map.mp h.2
    exact ⟨⟨x, hxX⟩, Subtype.ext hx⟩
  letI : Group.IsSolvable ↥X := hX
  haveI : Group.IsSolvable ↥H := Group.isSolvable_of_surjective hf
  obtain ⟨r, hr, hElem⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian H
  letI : Fact r.Prime := ⟨hr⟩
  letI : CFSG.IsElementaryAbelian r ↥H := hElem
  have hHp : IsPGroup r ↥H := CFSG.IsElementaryAbelian.isPGroup r ↥H
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := ↥X)
  have hPtop : (P : Subgroup ↥X).map f = ⊤ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.map_sylow_eq_top_of_isPGroup f hf hHp P
  let S : Subgroup K := (P : Subgroup ↥X).map X.subtype
  have hSπ : Subgroup.map π S = X.map π := by
    have h1 : Subgroup.map π S = ((P : Subgroup ↥X).map f).map H.subtype := by
      simp only [S, Subgroup.map_map, f]; rfl
    rw [h1, hPtop, ← MonoidHom.range_eq_map]
    simpa [H] using H.range_subtype
  refine ⟨r, hr, S, Subgroup.map_subtype_le _, P.isPGroup'.map X.subtype, ?_⟩
  exact sup_eq_of_map_eq_map_of_ker_eq (QuotientGroup.ker_mk' Y) hYX hSπ

variable [Group.IsPerfect K] {N : Subgroup K} [N.Normal]

private theorem le_center_of_commutator_le_of_le_center {M M₀ : Subgroup K}
    (hcomm : ⁅M, (⊤ : Subgroup K)⁆ ≤ M₀) (hM₀ : M₀ ≤ center K) : M ≤ center K := by
  have hcommZ : ⁅(⊤ : Subgroup K), M⁆ ≤ center K :=
    (Subgroup.commutator_comm (⊤ : Subgroup K) M).le.trans (hcomm.trans hM₀)
  have hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top (G := K)
  intro z hz
  exact Subgroup.mem_center_iff.mpr (fun g =>
    CFSG.GroupTheory.PerfectCover.commute_of_commutator_le_center hcommZ
      (by rw [hperf]; exact Subgroup.mem_top g) hz)

theorem le_center_of_forall_exists_le_centralizer (hN : IsSolvable N)
    (h : ∀ r : ℕ, r.Prime → ∀ R : Subgroup K, R ≤ N → IsPGroup r R →
      ∃ Y : Subgroup K, Y ≤ centralizer (R : Set K) ∧ N ⊔ Y = ⊤) :
    N ≤ center K := by
  classical
  letI : Group.IsSolvable ↥N := hN
  have key : ∀ M : Subgroup K, M.Normal → M ≤ N → M ≤ center K := by
    intro M
    refine WellFoundedLT.induction (motive := fun M => M.Normal → M ≤ N → M ≤ center K) M ?_
    intro M ih hMn hMN
    by_cases hMbot : M = ⊥
    · rw [hMbot]; exact bot_le
    obtain ⟨M₀, hchief⟩ := exists_chief_below hMn hMbot
    letI hM₀n : M₀.Normal := hchief.2.1
    have hM₀lt : M₀ < M := hchief.2.2.1
    have hM₀center : M₀ ≤ center K := ih M₀ hM₀lt hM₀n (hM₀lt.le.trans hMN)
    have hMsolv : IsSolvable M :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMN)
        (Subgroup.inclusion_injective hMN)
    obtain ⟨r, hr, S, hSM, hSp, hSM₀⟩ :=
      exists_isPGroup_sup_eq_of_isChiefPair hchief hMsolv
    obtain ⟨Y, hYcent, hNY⟩ := h r hr S (hSM.trans hMN) hSp
    have hYstab : Y ≤ stabSec M M₀ hM₀n :=
      le_stabSec_of_le_centralizer hM₀n hYcent hSM₀
    have htop : stabSec M M₀ hM₀n = ⊤ := by
      haveI : (stabSec M M₀ hM₀n).Normal := stabSec_normal hMn hM₀n
      refine eq_top_of_sup_eq_top_of_isSolvable (C := stabSec M M₀ hM₀n) (N := N) hN ?_
      exact top_le_iff.mp (hNY ▸ sup_le_sup le_rfl hYstab)
    have hcomm : ⁅M, (⊤ : Subgroup K)⁆ ≤ M₀ := by
      rw [Subgroup.commutator_le]
      intro x hx y _
      exact (mem_stabSec.mp (by rw [htop]; exact Subgroup.mem_top y)) x hx
    exact le_center_of_commutator_le_of_le_center hcomm hM₀center
  exact key N inferInstance le_rfl

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
import CFSG.GH74.GLS.NT44.RigidFamily
import CFSG.GH74.GLS.NT44.FixedLayerQuotient
import CFSG.GH74.GLS.NT44.FixedLayerCardinality
import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
import CFSG.GH74.GLS.Bg.Pu5.LPTPAbs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
import CFSG.GH74.GLS.Bg.Iii2.CMPU

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.GH74.GLS.Bg.Iii2.CMEngine CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

theorem mem_zStar_kz_of_pumpUpLT
    {G : Type} [Group G] [Finite G]
    {fullQ : Type} [Group fullQ]
    {x t y : G} {K K' : Subgroup G}
    (hK : CFSG.GH74.GLS.Stage1.Thm4.IsRigidOfType fullQ x K)
    (hlt : CFSG.GH74.GLS.PumpUpLT 2 x K t K')
    (hyK : y ∈ CFSG.GH74.GLS.zStar K)
    (hy2 : ∃ n : ℕ, y ^ (2 ^ n) = 1)
    (hyt : y ∈ Subgroup.centralizer ({t} : Set G)) :
    y ∈ CFSG.GH74.GLS.zStar
      (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ t) := by
  classical
  set Y : Subgroup G := Subgroup.centralizer ({t} : Set G) with hY
  have hxY : x ∈ Y := TwoThin.mem_centralizer_symm hlt.2.2.1
  have hs2 : orderOf (sbar x hxY) = 2 := orderOf_sbar hlt.1.1 hxY
  have hsinv : (sbar x hxY)⁻¹ = sbar x hxY := inv_eq_self_of_orderOf_eq_two hs2
  obtain ⟨eKK'⟩ := hK.1.2 t K' (LongPumpUp.single' hlt)
  have hle : TwoThin.hatCard K' ≤ TwoThin.hatCard K :=
    (Nat.card_congr eKK'.toEquiv).le
  obtain ⟨Λ, hΛ, hK'c, -, -, -, hcases⟩ := rigid_step hlt hxY hle
  have hK'rig : IsRigidOfType fullQ t K' :=
    CFSG.GH74.GLS.Stage1.Thm4.P92.isRigidOfType_of_pumpUpLT hK hlt
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxY
  have htxt : x * t * x⁻¹ = t := by
    calc x * t * x⁻¹ = t * x * x⁻¹ := by rw [hxt]
      _ = t := by group
  have hK'xrig : IsRigidOfType fullQ t (cmap x K') := by
    have h := isRigidOfType_conj (Q := fullQ) hK'rig x
    rwa [htxt] at h
  have hK'x_c : IsPCompIn 2 Y (cmap x K') := hK'xrig.1.1.2.2
  have hK'comp : CFSG.IsComponent (bar t K') := isComponent_bar hK'c
  have hK'xcomp : CFSG.IsComponent (bar t (cmap x K')) := isComponent_bar hK'x_c
  let R : Subgroup G := Kz fullQ t
  have hK'R : K' ∈ RigidSet fullQ t := hK'rig
  have hK'xR : cmap x K' ∈ RigidSet fullQ t := hK'xrig
  have hB_eq : conjSub (sbar x hxY)⁻¹ (bar t K') = bar t (cmap x K') := by
    rw [hsinv]
    exact (CFSG.GH74.GLS.Bg.Iii2.CMEngine.bar_cmap (u := t) (q := x) hxY K').symm
  have hyK1 : y ∈ K := hyK.1
  have hyKinf : y ∈ K ⊓ Y := Subgroup.mem_inf.mpr ⟨hyK1, hyt⟩
  have hyΛ : y ∈ Λ := hΛ.twoElt y hyKinf hy2
  have hcard : Nat.card (bar t Λ) ≤ Nat.card (kBar K) :=
    (card_bar_eq_of_isPRigid hK.1 hlt hΛ).le
  have hquot := exists_fixedLayerQuotientEquiv (x := x) (t := t) (K := K) (Λ := Λ) hΛ hcard
  dsimp only at hquot
  obtain ⟨hrho, -, -, e, hformula, -, -⟩ := hquot
  let hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  let hΛY : Λ ≤ Y := hΛ.le.trans inf_le_right
  let rho : Λ →* bar t Λ :=
    ((barMk Y).comp (Subgroup.inclusion hΛY)).codRestrict (bar t Λ) fun l =>
      ⟨⟨l, hΛY l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  let f : Λ →* kBar K := hatMap hΛK
  have hrho_surj : Function.Surjective rho := by
    simpa only [rho, hΛY] using hrho
  have hformula' : ∀ l : Λ, e (rho l) = f l := by
    intro l
    simpa only [rho, f, hΛK, hΛY] using hformula l
  let yqΛ : bar t Λ := rho ⟨y, hyΛ⟩
  let yq : barQ Y := barMk Y ⟨y, hyt⟩
  have hyq : (yqΛ : barQ Y) = yq := by
    dsimp only [yqΛ, yq, rho]
    change barMk Y ⟨y, hΛY hyΛ⟩ = barMk Y ⟨y, hyt⟩
    rw [show (⟨y, hΛY hyΛ⟩ : Y) = ⟨y, hyt⟩ from Subtype.ext rfl]
  have hcentΛ : ∀ w ∈ bar t Λ, w * (yqΛ : barQ Y) = (yqΛ : barQ Y) * w := by
    intro w hw
    obtain ⟨l, hl⟩ := hrho_surj ⟨w, hw⟩
    have hlw : (rho l : barQ Y) = w := congrArg Subtype.val hl
    rw [← hlw]
    have hlyΛ : ⁅(l : G), y⁆ ∈ Λ := by
      have hl : (l : G) ∈ Λ := l.2
      simp only [commutatorElement_def]
      exact Λ.mul_mem (Λ.mul_mem (Λ.mul_mem hl hyΛ) (Λ.inv_mem hl)) (Λ.inv_mem hyΛ)
    have hlyO : ⁅(l : G), y⁆ ∈ pPrimeCoreOf 2 K := hyK.2.2.2 _ (hΛK l.2)
    have hf_one : f ⟨⁅(l : G), y⁆, hlyΛ⟩ = 1 :=
      (hatMap_eq_one_iff hΛK _).mpr hlyO
    have he_one : e (rho ⟨⁅(l : G), y⁆, hlyΛ⟩) = 1 := by
      rw [hformula']
      exact hf_one
    have hrho_comm : rho ⟨⁅(l : G), y⁆, hlyΛ⟩ = 1 := by
      apply e.injective
      simpa using he_one
    have hsub : (⟨⁅(l : G), y⁆, hlyΛ⟩ : Λ) = ⁅l, (⟨y, hyΛ⟩ : Λ)⁆ :=
      Subtype.ext rfl
    have hmap_comm_sub : ⁅rho l, rho ⟨y, hyΛ⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      rw [← hsub]
      exact hrho_comm
    have hmap_comm : ⁅(rho l : barQ Y), ((rho ⟨y, hyΛ⟩ : bar t Λ) : barQ Y)⁆ = 1 := by
      simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_one] using congrArg (fun z : bar t Λ => (z : barQ Y)) hmap_comm_sub
    have hcomm : (rho l : barQ Y) * (yqΛ : barQ Y) = (yqΛ : barQ Y) * (rho l : barQ Y) := by
      have h := commutatorElement_eq_one_iff_mul_comm.mp hmap_comm
      simpa only [yqΛ] using h
    exact hcomm
  have hyqΛ : yq ∈ bar t Λ := by
    rw [← hyq]
    exact yqΛ.2
  have hcentΛ_yq : ∀ w ∈ bar t Λ, w * yq = yq * w := by
    intro w hw
    rw [← hyq]
    exact hcentΛ w hw
  have hcent_rigid : ∀ I ∈ RigidSet fullQ t, ∀ w ∈ bar t I, w * yq = yq * w := by
    intro I hI w hw
    have hIc : CFSG.IsComponent (bar t I) := isComponent_bar hI.1.1.2.2
    rcases hcases with ⟨-, hvert⟩ | ⟨-, hAB, -, hdiag⟩
    ·
      have hcentK' : ∀ w ∈ bar t K', w * yq = yq * w := by
        rw [← hvert]
        exact hcentΛ_yq
      have hyqK' : yq ∈ bar t K' := by
        rw [← hvert]
        exact hyqΛ
      rcases CFSG.LocalCores.distinct_components_commute hIc hK'comp with heq | hcomm
      · rw [heq] at hw
        exact hcentK' w hw
      · have hmem : ⁅w, yq⁆ ∈ ⁅bar t I, bar t K'⁆ :=
          Subgroup.commutator_mem_commutator hw hyqK'
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
    ·
      have hBcomp : CFSG.IsComponent (conjSub (sbar x hxY)⁻¹ (bar t K')) := by
        rw [hB_eq]
        exact hK'xcomp
      have hyqD : yq ∈ (swapDiag hAB).range := by
        rw [← hdiag]
        exact hyqΛ
      have hcentD : ∀ w ∈ (swapDiag hAB).range, w * yq = yq * w := by
        rw [← hdiag]
        exact hcentΛ_yq
      obtain ⟨hAc, hBc⟩ :=
        CFSG.GH74.GLS.Bg.Pu5.commute_of_mem_range_swapDiag hAB hK'comp.1 hyqD hcentD
      rcases CFSG.LocalCores.distinct_components_commute hIc hK'comp with heqA | hcommA
      · rw [heqA] at hw
        exact hAc w hw
      rcases CFSG.LocalCores.distinct_components_commute hIc hBcomp with heqB | hcommB
      · rw [heqB] at hw
        exact hBc w hw
      · obtain ⟨c, hc⟩ := hyqD
        rw [← hc]
        have hwc : w * (c : barQ Y) = (c : barQ Y) * w := by
          have h : ⁅w, (c : barQ Y)⁆ = 1 := by
            have hmem := Subgroup.commutator_mem_commutator hw c.2
            rwa [hcommA, Subgroup.mem_bot] at hmem
          exact commutatorElement_eq_one_iff_mul_comm.mp h
        have hcB : (sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY) ∈
            conjSub (sbar x hxY)⁻¹ (bar t K') := conj_mem_conjSub c.2
        have hwcB : w * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)) =
            ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)) * w := by
          have h : ⁅w, (sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)⁆ = 1 := by
            have hmem := Subgroup.commutator_mem_commutator hw hcB
            rwa [hcommB, Subgroup.mem_bot] at hmem
          exact commutatorElement_eq_one_iff_mul_comm.mp h
        rw [swapDiag_apply]
        calc
          w * (c * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)))
              = (w * (c : barQ Y)) * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)) := by
                group
          _ = ((c : barQ Y) * w) * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)) := by
                rw [hwc]
          _ = (c : barQ Y) * (w * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY))) := by
                group
          _ = (c : barQ Y) * (((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY)) * w) := by
                rw [hwcB]
          _ = ((c : barQ Y) * ((sbar x hxY)⁻¹ * (c : barQ Y) * (sbar x hxY))) * w := by
                group
  have hbar_mono {A B : Subgroup G} (hAB : A ≤ B) : bar t A ≤ bar t B := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp ha)), rfl⟩
  have hRbarK' : bar t K' ≤ bar t R := hbar_mono (le_sSup hK'R)
  have hRbarK'x : bar t (cmap x K') ≤ bar t R := hbar_mono (le_sSup hK'xR)
  have hDbar : bar t Λ ≤ bar t R := by
    rcases hcases with ⟨-, hvert⟩ | ⟨-, hAB, -, hdiag⟩
    · rw [hvert]
      exact hRbarK'
    · rw [hdiag]
      have hB_le : conjSub (sbar x hxY)⁻¹ (bar t K') ≤ bar t R := by
        rw [hB_eq]
        exact hRbarK'x
      rintro _ ⟨c, rfl⟩
      exact (sup_le hRbarK' hB_le) (swapDiag_mem_sup hAB c)
  have hcentR : ∀ w ∈ bar t R, w * yq = yq * w := by
    set Cq : Subgroup (barQ Y) := Subgroup.centralizer ({yq} : Set (barQ Y)) with hCq
    set T : Subgroup G := (Cq.comap (barMk Y)).map Y.subtype with hT
    have hRT : R ≤ T := by
      rw [hT]
      change sSup (RigidSet fullQ t) ≤ (Cq.comap (barMk Y)).map Y.subtype
      refine sSup_le ?_
      intro I hI i hi
      have hIY : I ≤ Y := hI.1.1.2.2.1
      refine ⟨⟨i, hIY hi⟩, ?_, rfl⟩
      change barMk Y ⟨i, hIY hi⟩ ∈ Cq
      rw [hCq]
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcent_rigid I hI _ ⟨⟨i, hIY hi⟩, Subgroup.mem_subgroupOf.mpr hi, rfl⟩
    have hsub_le : R.subgroupOf Y ≤ Cq.comap (barMk Y) := by
      intro p hp
      have hpT : (p : G) ∈ T := hRT (Subgroup.mem_subgroupOf.mp hp)
      rw [hT] at hpT
      rcases Subgroup.mem_map.mp hpT with ⟨q, hqC, hqp⟩
      have hqp' : q = p := Subtype.ext hqp
      simpa only [hqp'] using hqC
    have hmap_le : (R.subgroupOf Y).map (barMk Y) ≤ Cq :=
      (Subgroup.map_le_iff_le_comap (f := barMk Y)).mpr hsub_le
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hmap_le hw)
  have hRY : R ≤ Y := by
    simpa only [R, Y] using kz_le_centralizer (Q := fullQ) (z := t)
  have hRnorm : (R.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mpr ?_
    simpa only [R, Y] using centralizer_le_normalizer_kz (Q := fullQ) (z := t)
  have hRsubM : (R.subgroupOf Y).IsSubnormal := hRnorm.isSubnormal
  have hS : CFSG.Open.IsSubnormal (R.subgroupOf Y) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hRsubM
  have hX : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hyt⟩ : Y)) := by
    obtain ⟨n, hn⟩ := hy2
    exact TwoThin.isPGroup_zpowers_of_pow_eq_one (n := n) (Subtype.ext (by simpa using hn))
  have himages : (Subgroup.zpowers (⟨y, hyt⟩ : Y)).map (barMk Y) ≤
      (R.subgroupOf Y).map (barMk Y) := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    exact hDbar hyqΛ
  have hyR : y ∈ R := by
    have hle := TwoThin.le_of_isPGroup_of_map_le (barMk Y) TwoThin.barMk_surjective
      TwoThin.odd_card_ker_barMk (Subgroup.zpowers (⟨y, hyt⟩ : Y)) (R.subgroupOf Y)
      hX hS himages
    exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_zpowers (⟨y, hyt⟩ : Y)))
  have hkcO : ∀ k ∈ R, ⁅k, y⁆ ∈ pPrimeCoreOf 2 R := by
    intro k hk
    have hkcR : ⁅k, y⁆ ∈ R := by
      simp only [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hk hyR) (R.inv_mem hk)) (R.inv_mem hyR)
    have hkcY : ⁅k, y⁆ ∈ Y := hRY hkcR
    have hbar_one : barMk Y ⟨⁅k, y⁆, hkcY⟩ = 1 := by
      have hkY : k ∈ Y := hRY hk
      have e1 : (⟨⁅k, y⁆, hkcY⟩ : Y) = ⁅(⟨k, hkY⟩ : Y), (⟨y, hyt⟩ : Y)⁆ := rfl
      rw [e1, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (hcentR (barMk Y ⟨k, hkY⟩) ⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩)
    exact TwoThin.mem_pPrimeCoreOf_of_barMk_eq_one hRY hRsubM hkcR hkcY hbar_one
  change y ∈ zStar R
  show y ∈ R ⊓ centralizerSection R (pPrimeCoreOf 2 R)
  exact Subgroup.mem_inf.mpr ⟨hyR,
    ⟨Subgroup.le_normalizer hyR, mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hyR),
      hkcO⟩⟩

end CFSG.GH74.GLS.NT44

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Sub
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section StdTransport

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_inf' (H A B : Subgroup G) :
    (A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem subgroupOf_centralizer {H K : Subgroup G} (hKH : K ≤ H) :
    (Subgroup.centralizer (K : Set G)).subgroupOf H =
      Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    apply Subtype.ext
    simpa using h (k : G) hk
  · intro h k hk
    have := h ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.2 hk)
    simpa using congrArg Subtype.val this

theorem subgroupOf_inf_centralizer' {H L D : Subgroup G} (hDH : D ≤ H) :
    (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf H =
      L.subgroupOf H ⊓ Subgroup.centralizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [subgroupOf_inf', subgroupOf_centralizer hDH]

theorem isComponentOf_subgroupOf {H Y K : Subgroup G} (hYH : Y ≤ H) (h : IsComponentOf K Y) :
    IsComponentOf (K.subgroupOf H) (Y.subgroupOf H) := by
  obtain ⟨hKY, hsn, hq⟩ := h
  exact ⟨Subgroup.subgroupOf_mono H hKY, (I2015.isSubnormal_subgroupOf_iff hKY hYH).1 hsn,
    hq.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hKY.trans hYH))⟩

theorem isComponentOf_map_subtype {H : Subgroup G} {Y J : Subgroup ↥H} (h : IsComponentOf J Y) :
    IsComponentOf (J.map H.subtype) (Y.map H.subtype) :=
  I142N.isComponentOf_map H.subtype (fun g hg => by
    have : g = 1 := Subtype.ext hg
    rw [this]
    exact Subgroup.one_mem _) h

theorem glaStdSubPre_subgroupOf {p : ℕ} {H B L D K : Subgroup G} {x : G} (hxH : x ∈ H) (hBH : B ≤ H)
    (hLH : L ≤ H) (h : GLAStdSubPre p B x L D K) :
    GLAStdSubPre p (B.subgroupOf H) (⟨x, hxH⟩ : ↥H) (L.subgroupOf H) (D.subgroupOf H) (K.subgroupOf H) := by
  obtain ⟨hDB, hDel, hDcard, hxD, hKlay, hKcomp, hDK⟩ := h
  have hDH : D ≤ H := hDB.trans hBH
  have hKY : K ≤ L ⊓ Subgroup.centralizer (D : Set G) := hKcomp.1
  have hYH : L ⊓ Subgroup.centralizer (D : Set G) ≤ H := inf_le_left.trans hLH
  have hKH : K ≤ H := hKY.trans hYH
  have hYeq := subgroupOf_inf_centralizer' (L := L) hDH
  have hYmap : (L.subgroupOf H ⊓ Subgroup.centralizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H)).map
      H.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [← hYeq, Subgroup.map_subgroupOf_eq_of_le hYH]
  have hcomp : IsComponentOf (K.subgroupOf H)
      (L.subgroupOf H ⊓ Subgroup.centralizer ((D.subgroupOf H : Subgroup ↥H) : Set ↥H)) := by
    rw [← hYeq]
    exact isComponentOf_subgroupOf hYH hKcomp
  refine ⟨Subgroup.subgroupOf_mono H hDB, isElemAbelian_subgroupOf' H hDel,
    by rw [card_subgroupOf' hDH, hDcard], Subgroup.mem_subgroupOf.2 hxD, ?_, hcomp, ?_⟩
  · apply le_antisymm
    · exact I142N.le_GLALayer hcomp
    · refine I142N.GLALayer_le_of fun J hJ => ?_
      have hJ' := isComponentOf_map_subtype hJ
      rw [hYmap] at hJ'
      have hle : J.map H.subtype ≤ K := hKlay ▸ I142N.le_GLALayer hJ'
      intro j hj
      exact Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_map_of_mem _ hj))
  · rw [hDK, subgroupOf_inf', subgroupOf_centralizer hKH]

end StdTransport

section Std

variable {G : Type} [Group G] [Finite G]

theorem i265StdAt_of_fact (hF : FactS) (p : ℕ) : I265StdAt G p := by
  classical
  intro B x L D K hp hp2 hS h4 hq hchev hKx hinn hpre
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hBel, hBcard, -, -, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p G ∧
      ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G) := IsSStarMax.bmax hS
  have hess := IsSStarMax.essential hS
  have hxB : x ∈ B := hess.1
  have hx1 : x ≠ 1 := hess.2.1
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component hS
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes hS
  have hcyc : CycModSylow p L := IsSStarMax.cycMod hS
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hLc.1
  obtain ⟨T, hTC, hT2, hBT, hTT, hT0⟩ :=
    exists_two_group_comm_eq hp hp2 (isPGroup_of_isElemAbelian hBel) hess
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := hTC.trans (S171.cx_le_normalizer hp hp2 hS)
  set H : Subgroup G := L ⊔ B ⊔ T with hH
  have hLH : L ≤ H := le_sup_left.trans le_sup_left
  have hBH : B ≤ H := le_sup_right.trans le_sup_left
  have hTH : T ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hBN) hTN
  have hBx : B ≤ Subgroup.centralizer ({x} : Set G) := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel hc hxB)
  have hHx : H ≤ Subgroup.centralizer ({x} : Set G) := sup_le (sup_le hLx hBx) hTC
  have hxH : x ∈ H := hBH hxB
  have hxL : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLx hl)
  have hcm : ∀ c ∈ B, CentMod p L c ↔ c ∈ Subgroup.zpowers x :=
    centMod_iff_mem_zpowers hp hBel hxB hx1 hxL hcyc
  have hcomp : GLAPComponent p (⊤ : Subgroup ↥H) (L.subgroupOf H) := by
    have h1 := glaPComponent_of_le hp hLc hLH hHx
    have h2 := I2015.glaPComponent_subgroupOf (le_refl H) h1
    rwa [Subgroup.subgroupOf_self] at h2
  have hcfg : SCfg p (L.subgroupOf H) (B.subgroupOf H) (T.subgroupOf H) ⟨x, hxH⟩ (D.subgroupOf H)
      (K.subgroupOf H) :=
    { prime := hp
      odd := hp2
      kgroup := CFSG.Open.IsKGroup.of_le hKx hHx
      comp := hcomp
      normal := normal_subgroupOf hLH hHN
      quasi := hq.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH)
      chev := T156.isChevSimple_congr (T156.psimpleIso (eL hp hLH).symm) hchev
      gen := sup3_subgroupOf rfl
      elem := isElemAbelian_subgroupOf' H hBel
      two := isPGroup_subgroupOf' hT2 hTH
      bnorm := le_normalizer_subgroupOf hBH hTH hBT
      ne := comm_subgroupOf_ne_bot hBH hTH (by rw [hTT]; exact hT0)
      rank := by
        refine (Nat.pow_le_pow_right hp.pos (twoLocalRank_subgroup hp H)).trans ?_
        rw [card_subgroupOf' hBH, hBcard]
      big := by rw [card_subgroupOf' hBH]; exact h4
      cyc := cycModSylow_subgroupOf hp hLH hHN hcyc
      xB := Subgroup.mem_subgroupOf.2 hxB
      x1 := fun h => hx1 (congrArg Subtype.val h)
      xcen := fun g => Subtype.ext (by
        have := Subgroup.mem_centralizer_singleton_iff.1 (hHx g.2)
        simpa using this)
      centB := fun c hc => by
        rw [centMod_subgroupOf_iff hp hLH hHN c, mem_zpowers_subgroupOf_iff]
        exact hcm (c : G) (Subgroup.mem_subgroupOf.1 hc)
      inn := innDiagOn_subgroupOf hp hLH hHN hBH ((innDiagOn_iff hLc hq).1 hinn)
      std := glaStdSubPre_subgroupOf hxH hBH hLH hpre }
  have hDB : D ≤ B := hpre.1
  have hKL : K ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  rcases hF p ↥H (L.subgroupOf H) (B.subgroupOf H) (T.subgroupOf H) ⟨x, hxH⟩ (D.subgroupOf H)
      (K.subgroupOf H) hcfg with ⟨E, ⟨hEB, hEel, hEcard⟩, hDE, hElay⟩ | ⟨hp3, hsm⟩
  · left
    refine ⟨E.map H.subtype, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact (Subgroup.map_mono hEB).trans (Subgroup.map_subgroupOf_eq_of_le hBH).le
    · exact CFSG.Open.IsElemAbelian.map hEel H.subtype
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hEcard]
    · intro d hd
      have hdH : d ∈ H := hBH (hDB hd)
      exact ⟨⟨d, hdH⟩, hDE (Subgroup.mem_subgroupOf.2 hd), rfl⟩
    · exact (layer_cs_map_ne_bot_iff hp hLH E).2 hElay
  · right
    subst hp3
    refine ⟨rfl, ?_⟩
    rcases hsm with hU | hA
    · exact Or.inl ((T156.psimple3_congr rfl (eL hp (hKL.trans hLH)) _).1 hU)
    · exact Or.inr ((T156.psimple3_congr rfl (eL hp (hKL.trans hLH)) _).1 hA)

end Std

end CFSG.LocalAnalysis.GLTheoremA.S265

end

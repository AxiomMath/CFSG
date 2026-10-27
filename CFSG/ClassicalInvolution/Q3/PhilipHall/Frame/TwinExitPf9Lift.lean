module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem isLiftOf_of_liftedAtSec (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c))
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) {t : G} (hJt : IsUniqueInvolution J t)
    (htc : t ∈ Subgroup.centralizer ({c} : Set G)) (hLS : LiftedAtSec J c t htc) :
    ∃ htH : (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c,
      ∃ L : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      IsLiftOf (secImg Ω c J) L
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
          (⟨⟨t, htc⟩, htH⟩ : ↥(coreHull Ω c))) := by
  classical
  obtain ⟨ht, L, hLle, hL⟩ := hLS
  have hidem := tightCore_idem (secR J c)
  rw [hidem] at hLle
  have hKc : tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))) =
      (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) :=
    TwinExitPf2.tightCore_subgroupOf_cent J c
  have hKB : tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))) ≤ coreHull Ω c := by
    rw [hKc]; exact le_coreHull hJ
  have hBsub : IsSubnormal (coreHull Ω c) ⊤ := by
    have := TwinExitPf6.normal_coreHull hΩ hc2
    exact isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hAB : secH J c ≤ coreHull Ω c := subnormalClosure_le hKB hBsub
  have hAs : IsSubnormal (secH J c) (coreHull Ω c) := by
    have h1 := isSubnormal_inf (isSubnormal_subnormalClosure
      (tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))))) (coreHull Ω c)
    rwa [inf_eq_left.mpr hAB, top_inf_eq] at h1
  have hclass := transfer_classicalMember hAB hAs hL
  have htcore : t ∈ TwinADescent.coreAt c J := by
    have hle : Subgroup.zpowers t ≤ J ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hJt.mem, htc⟩
    exact le_tightCore_of_isPGroup hle
      (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hJt.sq)
      (Subgroup.mem_zpowers t)
  have htH : (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c :=
    le_coreHull hJ (Subgroup.mem_subgroupOf.mpr htcore)
  set tb : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c) :=
    QuotientGroup.mk' _ (⟨⟨t, htc⟩, htH⟩ : ↥(coreHull Ω c)) with htb
  have hmem : tb ∈ secImg Ω c J :=
    ⟨⟨⟨t, htc⟩, htH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr htcore), rfl⟩
  have hsq' : (⟨t, htc⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨t, htc⟩ = 1 :=
    Subtype.ext hJt.sq
  have htb1 : tb ≠ 1 := by
    intro h1
    have h1' : (⟨⟨t, htc⟩, htH⟩ : ↥(coreHull Ω c)) ∈ classicalInvolutionOddCore ↥(coreHull Ω c) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have hord : orderOf (⟨⟨t, htc⟩, htH⟩ : ↥(coreHull Ω c)) = 2 := by
      refine orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq') ?_
      intro e
      exact hJt.ne_one (congrArg (fun w : ↥(coreHull Ω c) =>
        (((w : ↥(Subgroup.centralizer ({c} : Set G)))) : G)) e)
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
    rw [hord] at hdvd
    exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd) (by decide)
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : (⟨⟨t, htc⟩, htH⟩ : ↥(coreHull Ω c)) * ⟨⟨t, htc⟩, htH⟩ = 1 := Subtype.ext hsq'
    rw [this, map_one]
  obtain ⟨z, hz⟩ := (hS.hyp.omega1 _ (secImg_mem_secFam hJ)).1
  have htz : tb = z := (hz.unique tb hmem htb2).resolve_left htb1
  have hinv : IsUniqueInvolution (secImg Ω c J) tb := htz ▸ hz
  refine ⟨htH, L.map (secEmb hAB hAs), hinv, ?_, ?_⟩
  ·
    have hKcH : tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))) ≤ secH J c :=
      le_subnormalClosure _
    have hAL : ((tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G)))).subgroupOf
        (secH J c)).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH J c))) ≤ L := by
      refine le_trans ?_ hLle
      have h1 : tightCore ((J.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
          (secH J c)) = (tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G)))).subgroupOf
            (secH J c) := CFSG.ClassicalInvolution.Q3.tightCore_subgroupOf hKcH
      rw [← h1]
      exact map_tightCore_le _ _
    rintro j ⟨b, hb, rfl⟩
    have hb' : (((b : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈
        TwinADescent.coreAt c J := hb
    have hbK : (b : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        tightCore (J.subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
      rw [hKc]; exact Subgroup.mem_subgroupOf.mpr hb'
    have hbA : (b : ↥(Subgroup.centralizer ({c} : Set G))) ∈ secH J c := hKcH hbK
    have hl : QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH J c)) ⟨_, hbA⟩ ∈ L :=
      hAL ⟨⟨_, hbA⟩, Subgroup.mem_subgroupOf.mpr hbK, rfl⟩
    exact ⟨_, hl, rfl⟩
  · exact hclass

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

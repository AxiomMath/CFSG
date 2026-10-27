module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ
public import CFSG.Milestones.ASVolI.I3
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.ASVolI.ChIJK
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_J_isTwoComponent (c : K7Abs ρ t J Q P M6 M7) :
    IsTwoComponentIn J (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Γ) : Set Γ)) := by
  let C : Subgroup Γ := Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Γ) : Set Γ)
  change IsTwoComponentIn J C
  have hJC : J ≤ C := by
    change J ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Γ) : Set Γ)
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    exact c.J_cent
  haveI hJsimple : IsSimpleGroup ↥J := y7c_J_simple c
  have hLnormal : (J.subgroupOf C).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hJC).mpr ?_
    intro h k hh hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup Γ) : Set Γ) := hk
    have hkt : k * t = t * k :=
      ((Subgroup.mem_centralizer_iff.mp hk') t (Subgroup.mem_zpowers t)).symm
    obtain ⟨j, hjJ, q, hqQ, hk_eq⟩ := c.cent k hkt
    rw [hk_eq]
    have hq : q * h = h * q := c.Q_J q hqQ h hh
    have hconj : (j * q) * h * (j * q)⁻¹ = j * h * j⁻¹ := by
      rw [mul_inv_rev, mul_assoc j q h, hq]
      group
    rw [hconj]
    exact J.mul_mem (J.mul_mem hjJ hh) (J.inv_mem hjJ)
  have eL : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  have hcardL : Nat.card ↥(J.subgroupOf C) = 168 := by
    rw [Nat.card_congr eL.toEquiv, y7c_J_card c]
  have hLne : J.subgroupOf C ≠ ⊥ := by
    intro h
    rw [h] at hcardL
    simp at hcardL
  have hmapL : (J.subgroupOf C).map C.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJC]
  have hLperf : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
    rw [← Subgroup.map_subtype_inj]
    rw [Subgroup.map_commutator, hmapL, y7c_J_perfect c]
  have hLsimple : IsSimpleGroup ↥(J.subgroupOf C) :=
    (MulEquiv.isSimpleGroup_congr eL).mpr hJsimple
  have hLmin : ∀ K : Subgroup ↥C, K < J.subgroupOf C → K ≠ ⊥ →
      ⁅K, K⁆ = K → ¬ K.IsSubnormal := by
    intro K hKlt hKne _hKperf hKsn
    have hmapK : (K.subgroupOf (J.subgroupOf C)).map (J.subgroupOf C).subtype = K := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKlt.le]
    have hsubsn : (K.subgroupOf (J.subgroupOf C)).IsSubnormal :=
      Subgroup.IsSubnormal.subgroupOf hKsn
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hLsimple hsubsn with h | h
    · exact hKne (by rw [← hmapK, h, Subgroup.map_bot])
    · exact (ne_of_lt hKlt) (by rw [← hmapK, h, Subgroup.map_top, Subgroup.range_subtype])
  have hLsn : (J.subgroupOf C).IsSubnormal := hLnormal.isSubnormal
  have hcomp : CFSG.IsCComponent (J.subgroupOf C) := ⟨hLne, hLperf, hLsn, hLmin⟩
  refine ⟨⟨hJC, hcomp⟩, ?_⟩
  have hCenterBot : Subgroup.center ↥J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    exact y7c_J_center c x.2 (fun y hy => by
      have hcomm : (⟨y, hy⟩ : ↥J) * x = x * ⟨y, hy⟩ :=
        (Subgroup.mem_center_iff.mp hx) ⟨y, hy⟩
      have := congrArg Subtype.val hcomm
      simpa using this.symm)
  have hJQ : CFSG.IsQuasisimple ↥J := by
    refine ⟨(Subgroup.isPerfect_iff (H := J)).mpr (y7c_J_perfect c), ?_, ?_⟩
    · exact (MulEquiv.isSimpleGroup_congr
          ((QuotientGroup.quotientMulEquivOfEq hCenterBot).trans
            QuotientGroup.quotientBot)).mpr hJsimple
    · let e : (↥J ⧸ Subgroup.center ↥J) ≃* ↥J :=
        (QuotientGroup.quotientMulEquivOfEq hCenterBot).trans QuotientGroup.quotientBot
      obtain ⟨a, ha, b, hb, hab⟩ := y7c_J_nonabelian c
      refine ⟨e.symm ⟨a, ha⟩, e.symm ⟨b, hb⟩, fun h => hab ?_⟩
      have hcomm : (⟨a, ha⟩ : ↥J) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
        have := congrArg (fun z => e z) h
        simpa using this
      simpa using congrArg Subtype.val hcomm
  have hOddCore_eq : CFSG.oddCore ↥J = CFSG.pPrimeCore 2 ↥J :=
    (CFSG.oddCore_eq_piCore (G := ↥J)).trans
      (CFSG.pPrimeCore_eq_piCore (G := ↥J) (p := 2)).symm
  have hOdd : Odd (Nat.card (CFSG.oddCore ↥J)) := by
    rw [hOddCore_eq]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥J))
  have hnotOdd : ¬ Odd (Nat.card ↥J) := by
    rw [y7c_J_card c]
    norm_num
  have hOddCoreBot : CFSG.oddCore ↥J = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (CFSG.oddCore ↥J) with h | h
    · exact h
    · exfalso
      have hcardTop : Nat.card (CFSG.oddCore ↥J) = Nat.card ↥J := by
        rw [h, Subgroup.card_top]
      exact hnotOdd (hcardTop ▸ hOdd)
  have eOdd : (↥J ⧸ CFSG.oddCore ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hOddCoreBot).trans QuotientGroup.quotientBot
  exact CFSG.IsQuasisimple.of_mulEquiv eOdd hJQ

end CFSG.OddStandard.HigherRank.YamadaG23

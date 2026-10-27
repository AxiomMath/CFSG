module

public import CFSG.Quasithin.H13.A6S1372L76N3c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N3a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76N3b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

section Block

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

theorem V3_inf_centralizer_QH_le_F4 (h13314 : Stmt13_3_14_F4) :
    S.V3 ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ fsuV1 T V := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hV1C : fsuV1 T V ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((Subgroup.mem_centralizer_iff.1 (hF.H_le_centralizer (pCoreOf_le 2 H hq))) x hx).symm
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  rcases hF.irred (S.V3 ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))
      (le_inf (S.V1_le_V2.trans S.V2_le_V3) hV1C) inf_le_left
      (fun l hl => mem_normalizer_inf_of (S.L1T_le_NV3 hl)
        (normalizes_of_conj_mem (X := H) (fun k hk y hy => conj_centralizer_mem (hHQ hk) hy)
          (hF.L₁T_le_H hl))) with h | h
  · exact h.le
  · exfalso
    apply h13314 G T L V S.V2 S.h13 S.irr S.zv S.isV2 S.not_iso_a5
    intro x hx
    have hg1 : g1 T V = S.G1 := S.normalizer_V1
    rw [hg1] at hx
    have hxQ : x ∈ pCoreOf 2 H := S.pCoreOf_G1_le_QH hF.T_le_H hH.2.1 hx
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvC : v ∈ S.V3 ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
      rw [h]
      exact S.V2_le_V3 hv
    exact ((Subgroup.mem_centralizer_iff.1 hvC.2) x hxQ).symm

theorem four_pow_three_le_nu_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (hhat : ¬ IsHatA6 L)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (hL1K : S.L1 ≤ K)
    (hSL : BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1) :
    4 ^ 3 ≤ nu (S.cL1 hhat : G) (pCoreOf 2 S.L1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hQL1 := S.QH_le_normalizer_L1_F4 hNS h13315 h1356two hH
  have hQO : pCoreOf 2 H ≤ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hcO' : c ∈ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) := le_normalizer_pCoreOf 2 S.L1 hcL
  have hOH : pCoreOf 2 S.L1 ≤ H := (pCoreOf_le 2 S.L1).trans hL1H

  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))

  have hA : 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) ≤ nu c (pCoreOf 2 S.L1) := by
    obtain ⟨o, ho, hno⟩ := S.exists_O2L1_comm_not_mem_QH_F4 h139 h37 h38 h13315 h1356two hNS hhat
      hH hK hL1K hSL
    refine four_mul_nu_le hc3 (pCoreOf_isPGroup 2 S.L1) inf_le_left hcO'
      (mem_normalizer_inf_of hcO' (hHQ hcH)) ?_ ⟨o, ho, fun h => hno h.2⟩
    exact fun x hx => mem_normalizer_inf_of (Subgroup.le_normalizer (mem_cfix.1 hx).1)
      (hHQ (hOH (mem_cfix.1 hx).1))

  have hB : nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) = nu c (pCoreOf 2 H) := by
    have hY3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by
      obtain ⟨e, he⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le
        (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H))
      rw [he]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hcY : ∀ y ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H, c * y * c⁻¹ ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf_of hcO' (hHQ hcH)) y).mp hy
    have hcX : ∀ q ∈ pCoreOf 2 H, q⁻¹ * (c * q * c⁻¹) ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H := by
      intro q hq
      have h1 : q⁻¹ * c * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 ((pCoreOf 2 H).inv_mem hq)) _).mp hcL
      have hmem : q⁻¹ * (c * q * c⁻¹) ∈ S.L1 ⊓ pCoreOf 2 H := by
        refine ⟨?_, (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq)
          ((Subgroup.mem_normalizer_iff.mp (hHQ hcH) q).mp hq)⟩
        have e : q⁻¹ * (c * q * c⁻¹) = (q⁻¹ * c * q⁻¹⁻¹) * c⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hcL)
      exact ⟨hL1Q hmem, hmem.2⟩
    have hN : cfix c (pCoreOf 2 H) ≤
        Subgroup.normalizer ((pCoreOf 2 S.L1 ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf_of (hQO (mem_cfix.1 hx).1)
        (Subgroup.le_normalizer (mem_cfix.1 hx).1)
    rw [nu_mul c (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H) hN,
      relIndex_cfix_sup_eq_one hc3 inf_le_right hY3 hcY hcX, one_mul]

  have hHCQ : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hNHC : cfix c (pCoreOf 2 H) ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure S.V3 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (mem_cfix.1 hx).1
    exact mem_normalizer_inf_of (hHQ hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHU hl) hy) hxH)
  have hU0U : conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      conjClosure S.V3 H := inf_le_left
  have hNU0 : cfix c (conjClosure S.V3 H) ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (hF.conjClosure_Vp_le_pCoreOf (mem_cfix.1 hx).1)
    exact mem_normalizer_inf_of (hHU hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hxH)
  have hdual := nu_dual_F97 hF hab hcH hc3
  have hC : nu c (pCoreOf 2 H) =
      (cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) *
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    rw [nu_mul c hHCQ hNHC, hdual]

  have hv2U : S.v2 ∈ conjClosure S.V3 H := S.v2_mem_UH H
  have hcU : c ∈ Subgroup.normalizer (conjClosure S.V3 H : Set G) := hHU hcH
  have hcU0 : c ∈ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_of hcU (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hcH)
  have hcv : c * S.v2 * c⁻¹ * S.v2⁻¹ ∉ conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro h
    have hV3 : c * S.v2 * c⁻¹ * S.v2⁻¹ ∈ S.V3 :=
      S.V3.mul_mem (S.conj_v2_mem_V3 (S.cL1_rho hhat)) (S.V3.inv_mem S.v2_mem_V3)
    exact S.comm_v2_not_mem_V1 (S.cL1_rho hhat)
      (S.V3_inf_centralizer_QH_le_F4 hNS h13315 h1356two hH h13314 ⟨hV3, h.2⟩)
  have hU2 : IsPGroup 2 ↥(conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF.conjClosure_Vp_le_pCoreOf
  have hD4 := four_mul_nu_le hc3 hU2 hU0U hcU hcU0 hNU0 ⟨S.v2, hv2U, hcv⟩
  have hpos : 0 < nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
    unfold nu
    exact Nat.pos_of_ne_zero (by
      show ((cfix c _).subgroupOf _).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite)
  have hD : 4 ≤ (cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) := by
    rw [nu_mul c hU0U hNU0] at hD4
    exact Nat.le_of_mul_le_mul_right (by linarith) hpos

  have hUQC : conjClosure S.V3 H ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    refine le_inf hF.conjClosure_Vp_le_pCoreOf fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := mul_comm (⟨w, hw⟩ : ↥(conjClosure S.V3 H)) ⟨u, hu⟩
    exact congrArg Subtype.val this
  have hE1 : 4 ≤ nu c (conjClosure S.V3 H) := by
    have h1 := nu_mul c hU0U hNU0
    rw [h1]
    nlinarith
  have hE2 : nu c (conjClosure S.V3 H) ≤
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) :=
    nu_le_nu hUQC fun x hx => hHU (hQH (mem_cfix.1 hx).1.1)
  calc 4 ^ 3 = 4 * (4 * 4) := by norm_num
    _ ≤ 4 * ((cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) *
          nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by
      gcongr
      exact hE1.trans hE2
    _ = 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by rw [hB, hC]
    _ ≤ nu c (pCoreOf 2 S.L1) := hA

end Block

end Setting4

theorem lem1376NThreeBlock_of_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13314 : Stmt13_3_14_F4) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) : Lem1376NThreeBlock_F4 := by
  intro G _ _ T L V S hNS _ hhat hQ H hH hab _ K hK hL1K hSL
  have h1 := S.nu_O2L1_le_sixteen hhat hQ
  have h2 := S.four_pow_three_le_nu_F4 hNS h13315 h1356two hH h139 h37 h38 h13314 hhat hab hK hL1K
    hSL
  omega

end CFSG.Quasithin.H13.A6
